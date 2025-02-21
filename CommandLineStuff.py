import re
import subprocess
import threading
import queue
import os
from threading import Thread

import GPTStuff
import Utils
import shutil
from deprecated import deprecated

proofs = []
proof_counter = 0
client = None
TEMP_THY_FILE = ""
theory_file = ''
NAMESPACE = ""

def enqueue_output(out, queue):
    while True:
        try:
            line = out.readline()
            #print("line:")
            #print(line)
            if not line:
                break
            queue.put(line.rstrip('\r\n'))
        except UnicodeDecodeError:
            print("decoding issue")
            continue
    out.close()


@deprecated
def run_command(command):
    try:
        result = subprocess.run(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode == 0:
            return result.stdout.strip()
        else:
            print(f'Error running command: {command}')
            print(f'Error: {result.stderr}')
            return None
    except Exception as e:
        print(f'Error running command: {command}')
        print(f'Error: {e}')
        return None


@deprecated
def run_continuous(shell_process, command):
    print("running command")
    try:
        shell_process.stdin.write(command.encode('utf-8')+b'\n')
        shell_process.stdin.flush()
        output = []
        for line in shell_process.stdout:
            output.append(line.decode('utf-8').strip())
            print(line)
        return '\n'.join(output)
    except Exception as e:
        print(f'Error running command: {command}:{e}')
        return None


def shell_startup():
    shell_process = subprocess.Popen("bash",
                                     stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE,
                                     stdin=subprocess.PIPE,
                                     text=True)
    output_queue = queue.Queue()
    output_thread = threading.Thread(target=enqueue_output, args=(shell_process.stdout, output_queue), daemon=True)
    output_thread.start()
    error_thread = threading.Thread(target=enqueue_output, args=(shell_process.stderr, output_queue), daemon=True)
    error_thread.start()
    print("Shell Process Started")
    shell_process.stdin.write("export ISABELLE_HOME=\"/home/tim/Downloads/Isabelle2024\"\n")
    shell_process.stdin.flush()
    shell_process.stdin.write("export PATH=\"$ISABELLE_HOME/bin:$PATH\"\n")
    shell_process.stdin.flush()
    return shell_process, output_queue


def user_interaction(translation,next_proof):
    print("Is the following translation correct?")
    print(next_proof.split("Proof")[0])
    print(translation.split('proof')[0])
    trans = translation
    retries = 0
    while True:
        feedback = input("[Y/N]:")
        if feedback in ["Y", "y", "Yes", "yes", "YES"]:
            print("User check success. Continuing...")
            break
        elif feedback in ["N", "n", "No", "no", "NO"]:
            print("User check failure.")
            print("Re-translate? (Y)\nmanual input otherwise (N)")
            option = input("[Y/N]:")
            if option in ["Y", "y", "Yes", "yes", "YES"]:
                err_mess = input("Whats wrong with the translation?")
                trans = GPTStuff.chat_call(client, next_proof.split("Proof")[0], error="theorem", err_mess=err_mess)
                one_line = trans.split("proof")
                if len(one_line) > 1:
                    trans = one_line[0]
                print("Is the following translation correct?")
                print(next_proof.split("Proof")[0])
                print(trans)
            else:
                trans = input("manual translation:")
                trans = trans + "\n"+ "\n".join(translation.split('\n')[1:])
                retries = -1
                break
        retries += 1
    return trans, retries

def get_output_lines(output_queue):
    output_lines = []
    while True:
        try:
            output_line = output_queue.get(timeout=20)
            output_lines.append(output_line)
            # print(output_line)
        except queue.Empty:
            print("Queue empty, moving on")
            break
    return output_lines

def main(skip_first=None):
    if skip_first is None:
        startup_done = False
    else:
        startup_done = skip_first
    try:
        shell_process, output_queue = shell_startup()
        # main loop
        main_loop(startup_done, shell_process , output_queue)
    except KeyboardInterrupt:
        print("\nUser Interrupt. Session terminated.")
    except ChildProcessError:
        print("Fatal Error. Shutting down.")
    finally:
        GPTStuff.log_messages()
        shell_process.stdin.close()
        shell_process.wait()
        print("Session Terminated.")

#@param start boolean True when starting with the next translation False when starting with isabelle check
def main_loop(start, shell_process, output_queue):
    startup_done = start
    while True:
        if startup_done:
            next_proof = get_next_proof()
            if next_proof is None:
                print("translation finished")
                break
            print(f"Translating next proof {next_proof[0:15]}")
            # deleting "end"
            Utils.delete_last_line(TEMP_THY_FILE)
            # writing prompt as comment
            with open(TEMP_THY_FILE, 'a') as file:
                file.write("\n(* " + next_proof + " *)\n")
            translation = GPTStuff.chat_call(client, next_proof)
            # user checks translation of theorem
            trans, retries = user_interaction(translation, next_proof)
            print(f"retires: {retries}")
            proof_without_theorem = "".join(next_proof.split("Proof:")[1:])
            if retries != 0:
                trans_without_theorem = GPTStuff.chat_call(client, proof_without_theorem, err_mess=trans)
                #print(trans_without_theorem)
                if not trans_without_theorem.startswith("theorem "):
                    trans += "\n" + trans_without_theorem
                else:
                    if trans != trans_without_theorem.split("proof")[0].strip():
                        trans = trans + "\n" + trans_without_theorem[trans_without_theorem.find("proof"):]
                    else:
                        trans = trans_without_theorem
            # writing translation and "end" if needed
            with open(TEMP_THY_FILE, 'a') as file:
                file.write(trans)
                if not trans.strip().endswith('end'):
                    file.write('\nend')
                file.close()
            status = {}
            Utils.change_namespace(NAMESPACE, "temp", TEMP_THY_FILE)
        else:
            print("skipping first translation")
            status = {}
            Utils.change_namespace(NAMESPACE, "temp", TEMP_THY_FILE)
            startup_done = True
            next_proof = get_next_proof(-1)
        # repeat command line calls and fix isabelle code until it runs fine
        while True:
            command = get_next_command(status)
            shell_process.stdin.write(command + '\n')
            shell_process.stdin.flush()
            # wait for output from shell process
            output_lines = get_output_lines(output_queue)
            old_status = status
            #analyze status
            status = Utils.parse_output(output_lines, old_status)
            print(status.get("status"))
            #act appropriately on status
            status = parse_status(status)
            if status.get("status") == Utils.StatusCode.OK:
                break
            if status.get("status")==Utils.StatusCode.SLEDGEHAMMER_NEEDED and not status.get("cheating_success"):
                #print("trying step by step translation")
                #Utils.cut_comment(TEMP_THY_FILE)
                #sbs_trans = step_by_step_translation(next_proof)
                #Utils.write_correction(sbs_trans, TEMP_THY_FILE, keep_theorem=True)
                print("sledge fail, prompting for alternate translation")
                help_message = input("Additional info?")
                relevant_line = Utils.get_line(TEMP_THY_FILE, status.get("error_lines")[0])
                corr = GPTStuff.chat_call(client, relevant_line + "\n" + help_message, error="sledge")
                Utils.write_correction(corr, TEMP_THY_FILE)


def parse_status(status):
    if status.get("status") == Utils.StatusCode.OK:
        shutil.copyfile(TEMP_THY_FILE, theory_file)
        Utils.change_namespace("temp", NAMESPACE, theory_file)
        GPTStuff.startup(theory_file)
    elif status.get("status") == Utils.StatusCode.SLEDGEHAMMER_NEEDED:
        if status.get("error_lines") is not None:
            success = Utils.cheating(TEMP_THY_FILE, status, sledge=True)
            status["cheating_success"] = success
    elif status.get("status") == Utils.StatusCode.GPT_CORRECTION:
        corr = GPTStuff.chat_call(client, status.get("lines"), error="isabelle")
        Utils.write_correction(corr, TEMP_THY_FILE)
    elif status.get("status") == Utils.StatusCode.LOGS_NEEDED:
        pass
    elif status.get("status") == Utils.StatusCode.END_SYNTAX:
        Utils.delete_last_line(TEMP_THY_FILE)
    elif status.get("status") == Utils.StatusCode.MALFORMED:
        Utils.fix_malformation(TEMP_THY_FILE)
    else:
        print(status.get("lines"))
        raise ChildProcessError
    return status

def step_by_step_translation(proof):
    GPTStuff.start_step_by_step()
    trans = ""
    theo_split = ("Proof:" + proof.split("Proof:")[1]).split(".")
    for line in theo_split:
        trans += "\n" + "(* " + line + " *)\n" + GPTStuff.chat_call(client, line)
    GPTStuff.stop_step_by_step()
    return trans

def get_next_proof(offset=None):
    global proof_counter
    if proof_counter >= len(proofs):
        return None
    if offset is None:
        ret = proofs[proof_counter]
        proof_counter += 1
    else:
        ret = proofs[proof_counter + offset]
    return ret


def get_next_command(status, set_up=''):
    if set_up == 'user':
        return input("Command:")
    elif not set_up:
        if status.get("status") == Utils.StatusCode.LOGS_NEEDED:
            print("calling isabelle error log")
            return "isabelle build_log -H Error Test"
        else:
            print("calling isabelle build")
            return "isabelle build -o quick_and_dirty=true -d. Test"


def read_proofs(proof_file,paper=False):
    global proofs
    if paper:
        with open(proof_file,'r') as file:
            lines = file.readlines()
            full_text = ''.join(lines)
            proofs = full_text.split('§')
            return
    curr_proof = ""
    with open(proof_file, 'r') as f:
        for line in f:
            line = line.strip()
            if line.startswith("Theorem") or line.startswith("Definition"):
                if curr_proof:
                    proofs.append(curr_proof)
                    curr_proof = line + "\n"
                else:
                    curr_proof += line + "\n"
            else:
                curr_proof += line + "\n"
        if curr_proof:
            proofs.append(curr_proof)



def find_current_proof(paper=False):
    global proof_counter
    last_input = ""
    mess = GPTStuff.get_messages()
    for m in reversed(mess):
        if m["role"] == "user":
            last_input = m["content"]
            break
    for i in range(len(proofs)):
        line_one = proofs[i].strip().split("\n")[0]
        if not line_one:
            continue
        if line_one in last_input:
            proof_counter = i+1
            break

#TODO refactor to Utils (GPT stuff needs to stay here)
def read_params():
    global theory_file, client, proof_counter, TEMP_THY_FILE, NAMESPACE
    parameters = {}
    isa_start = False
    #read parameters
    with open("files/config", "r") as f:
        for line in f:
            line = line.strip()
            if line.startswith('#') or not line:
                continue
            param = line.split("=")
            parameters[param[0].strip()] = param[1].strip()
    print("Parameters loaded")
    print(parameters)
    theory_file = parameters['theory']
    if "paper" in theory_file:
        NAMESPACE = "paper"
    else:
        NAMESPACE = "Landau_GPT4"
    temp_file = parameters.get("temp")
    #read temp file or make new one
    if temp_file:
        print("loading temp file")
        TEMP_THY_FILE = temp_file.strip()
        isa_start = Utils.check_temp_status(TEMP_THY_FILE)
    else:
        TEMP_THY_FILE = "temp.thy"
        shutil.copyfile(theory_file, TEMP_THY_FILE)
    #check for fresh start
    print("reading natural language proofs")
    read_proofs(parameters["proof"], paper=NAMESPACE=="paper")
    print(f"found:{len(proofs)} proofs")
    if parameters.get("fresh_start") == "True":
        print("initializing GPT module")
        client = GPTStuff.fresh_start()
        thy_setup = GPTStuff.chat_call(client, None, cold_call=True)
        with open(TEMP_THY_FILE, 'w') as f:
            f.write(thy_setup)
        GPTStuff.system_message("")
    else:
        print("initializing GPT module")
        client = GPTStuff.initialise(seed=int(parameters.get('seed')), model=parameters.get('model'),
                                     few_shot=int(parameters.get('few_shot')))

    Utils.change_namespace(NAMESPACE, "temp", TEMP_THY_FILE)
    GPTStuff.startup(TEMP_THY_FILE)
    #initialize proof counter
    proof_counter = int(parameters.get("starting_proof"))
    if not proof_counter:
        proof_counter = 0
    elif proof_counter == -1:
        find_current_proof(paper=NAMESPACE=="paper")
        if proof_counter == -1:
            proof_counter = 0
        print(f"current proof: {proof_counter}")
    return isa_start


if __name__ == '__main__':
    starts_with_comment = read_params()
    print(f"starting command line module. (skip?{starts_with_comment})")
    main(skip_first=starts_with_comment)
