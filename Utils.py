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


def delete_last_line(file):
    with open(file, 'r+') as f:
        f.seek(0, 2)
        pos = f.tell()
        while pos > 0:
            pos -= 1
            f.seek(pos)
            if f.read(1) == '\n':
                break
        f.truncate(pos)


def cheating(thy_file, status):
    if status.get("error_lines") is None or len(status.get("error_lines")) == 0:
        return
    print(f"cheating in line {status.get('error_lines')[0]}")
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


def write_correction(correction, file):
    with open(file, 'r') as f:
        lines = f.readlines()
    last_proof = 0
    for i in range(len(lines)):
        if lines[i].strip().endswith("*)"):
            last_proof = i
    lines[last_proof + 1:] = [correction + '\nend\n']
    with open(file, 'w') as f:
        f.writelines(lines)


def fix_malformation(file):
    with open(file, 'r') as f:
        lines = f.readlines()
    last_comment = 0
    code_start = -1
    code_end = -1
    for i in range(len(lines)):
        if lines[i].strip().endswith("*)"):
            last_comment = i
        if lines[i].strip().startswith("```") and code_start == -1:
            code_start = i
        if lines[i].strip().startswith("```") and code_start != -1:
            code_end = i
    lines = lines[:last_comment + 1] + lines[code_start+1:code_end]
    lines.append("\nend\n")
    with open(file, 'w') as f:
        f.writelines(lines)