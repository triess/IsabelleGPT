import os
from enum import Enum
import re


class StatusCode(Enum):
    OK = 1
    SLEDGEHAMMER_NEEDED = 2
    FATAL = 3
    GPT_CORRECTION = 4
    LOGS_NEEDED = 5
    END_SYNTAX = 6
    MALFORMED = 7
    STEP_BY_STEP = 8


def parse_output(output_lines, old_status):
    ret = {}
    lines = ""
    for line in output_lines:
        line = line.strip()
        lines += line + '\n'
    ret['lines'] = lines
    print(lines)
    if len(output_lines) < 2:
        print("no lines found")
        ret['status'] = StatusCode.FATAL
        return ret
    if any(s.startswith('Finished Test') for s in output_lines):
        ret["status"] = StatusCode.OK
        return ret
    if ('Running Test ...' in output_lines) and (
            'Test FAILED (see also "isabelle build_log -H Error Test")' in output_lines):
        if old_status.get("status") == StatusCode.LOGS_NEEDED:
            ret["status"] = StatusCode.GPT_CORRECTION
            ret["error_lines"] = get_error_lines(lines)
        else:
            ret["status"] = StatusCode.LOGS_NEEDED
            ret["error_lines"] = get_error_lines(lines)
        return ret
    if any("missing theory context for command\"end\"" in s for s in output_lines):
        ret["status"] = StatusCode.END_SYNTAX
        ret["error_lines"] = get_error_lines(lines)
        return ret
    if any("Failed to refine any pending" in string for string in output_lines):
        ret["status"] = StatusCode.GPT_CORRECTION
        ret["error_lines"] = (get_error_lines(lines))
        ret["lines"] += "\nPlease try to use the \"consider (case1)...|(case2)...\" syntax to restructure the proof"
        return ret
    if any("At command \"by\"" in string for string in output_lines):
        ret["status"] = StatusCode.SLEDGEHAMMER_NEEDED
        ret["error_lines"] = get_error_lines(lines)
        return ret
    if any("<malformed>" in s for s in output_lines):
        ret["status"] = StatusCode.MALFORMED
        ret["error_lines"] = get_error_lines(lines)
        return ret
    if any("java.lang." in string for string in output_lines) or "Build errors:" in output_lines:
        ret["status"] = StatusCode.GPT_CORRECTION
        err_lines = get_error_lines(lines)
        if err_lines:
            ret["error_lines"] = err_lines
        return ret
    print("defaulting to fatal")
    ret["status"] = StatusCode.FATAL
    return ret


def get_error_lines(lines):
    pattern = r"At command \"by\" \(line (\d+) of"
    matches = re.findall(pattern, lines)
    line_numbers = [int(match) for match in matches]
    return list(set(line_numbers))


#deletes the last line until "end" was deleted
def delete_last_line(file):
    with open(file, 'r+') as f:
        lines = f.readlines()
    while True:
        last_line = lines.pop().strip()
        if last_line == "end":
            break
    with open(file, 'w') as f:
        f.writelines(lines)

#returns False if the file ends with isabelle code and True if it ends with a comment
def check_temp_status(temp_file):
    with open(temp_file, 'r') as f:
        lines = f.readlines()
    comment_end = 0
    for i in range(len(lines)):
        if lines[i].strip().endswith('*)'):
            comment_end = i
    if len(lines) > comment_end + 3:
        return False
    return True

#invoke sledgehammer or replace relevant part with "sorry"
#returns True if sledgehammer is successful and False if it fails
#always returns True in case of cheating
#returns None in case of error
def cheating(thy_file, status, sledge=False):
    if status.get("error_lines") is None or len(status.get("error_lines")) == 0:
        return None
    if sledge:
        print(f"sledge in line {status.get('error_lines')[0]}")
    else:
        print(f"cheating in line {status.get('error_lines')[0]}")
    if sledge:
        #TODO actually call sledgehammer
        manual = input("check if sledgehammer gets it done(0/1):")
        if manual == "0":
            return False
        elif manual == "1":
            return True
    else:
        with open(thy_file, 'r+') as f:
            lines = f.readlines()
            print(f"lines before cheating:{len(lines)}")
            to_fix = status.get("error_lines")[0] - 1
            cheat_line = lines[to_fix]
            cheat_line = cheat_line[:cheat_line.find(" by ")] + " sorry"
            lines[to_fix] = cheat_line
            last_line_counter = 0
            for i in range(len(lines)):
                lines[i] = lines[i].rstrip(" \n\r")
                lines[i] += "\n"
                if lines[i].strip().startswith("end"):
                    lines[i] = "end"
                    last_line_counter = i
            f.truncate(0)
            f.seek(0)
            print(f"lines after cheating:{len(lines[:last_line_counter + 1])}")
            lines[0] = "theory temp\n"
            f.writelines(lines[:last_line_counter + 1])
            f.close()
        return True


def parse_thy_file(thy_file, window=None):
    mess = []
    with open(thy_file, 'r') as f:
        lines = f.readlines()
    axioms = [idx for idx, s in enumerate(lines) if s.strip().startswith("Axiom")]
    m = ""
    for i in range(max(axioms), len(lines)):
        lines[i] = lines[i].rstrip(" \n\r")
        if lines[i].strip().startswith("(*") and lines[i].strip().endswith("*)"):
            if m.strip():
                mess.append({"role": "assistant", "content": m})
            mess.append({"role": "user", "content": lines[i]+'\n'})
            m = ''
        elif lines[i].strip().endswith("*)"):
            if m.strip():
                m += lines[i] + '\n'
                mess.append({"role": "user", "content": m})
                m = ''
        elif lines[i].strip().startswith("(*"):
            if m.strip():
                mess.append({"role": "assistant", "content": m})
                m = lines[i] + '\n'
        else:
            m += lines[i] + "\n"
    mess.append({"role": "assistant", "content": m[:-1]})
    if not window:
        return mess
    else:
        window_mess = mess[len(mess)-window * 2:len(mess)]
        cutoff_line = 1
        for me in window_mess:
            cutoff_line += me["content"].count("\n")
        return window_mess, lines[0:len(lines) - cutoff_line]


def change_namespace(namespace_before, namespace_after, file):
    with open(file, 'r') as f:
        file_content = f.read()
    new_content = file_content.replace(namespace_before, namespace_after)
    with open(file, 'w') as f:
        f.write(new_content)


#cuts the last comment down to only the theorem statement
def cut_comment(file):
    with open(file, 'r') as f:
        lines = f.readlines()
    start_comment=0
    end_comment=0
    for i in range(len(lines)):
        if lines[i].strip().startswith("(*"):
            start_comment = i
        if lines[i].strip().endswith("*)"):
            end_comment = i
    proof_start = 0
    for i in range(start_comment, end_comment):
        if lines[i].strip().startswith("Proof:"):
            proof_start = i
            break
    lines[proof_start-1] += "*)"
    lines = lines[start_comment:proof_start] + lines[end_comment:]
    with open(file, 'w') as f:
        f.writelines(lines)

#replaces everything after last comment with given correction and adds "end"
#if keep_theorem is True it tries to keep the last theorem from the file
def write_correction(correction, file, keep_theorem=False):
    with open(file, 'r') as f:
        lines = f.readlines()
    last_proof = 0
    for i in range(len(lines)):
        if (not keep_theorem) and lines[i].strip().endswith("*)"):
            last_proof = i
        elif keep_theorem and lines[i].strip().startswith("theorem Theorem"):
            last_proof = i
    lines[last_proof + 1:] = [correction + '\nend\n']
    with open(file, 'w') as f:
        f.writelines(lines)

def get_only_isabelle_code(message):
    try:
        start = message.index("```isabelle\n") + len("```isabelle\n")
        stop = message.index("```", start)
        return message[start:stop]
    except ValueError:
        return message

#eliminates extra "end"s from the file
def fix_malformation(file):
    with open(file, 'r') as f:
        lines = f.readlines()
    second_theory = -1
    for i in range(len(lines)):
        if lines[i].strip().startswith("theory"):
            if second_theory==-1:
                second_theory = i
            else:
                lines = lines[:i]
                break
    lines = [l for l in lines if not l.strip().startswith("end")]
    lines.append("\nend\n")
    with open(file, 'w') as f:
        f.writelines(lines)