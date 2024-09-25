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
TEMP_THY_FILE = "temp.thy"
theory_file = ''


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
    print(translation.split('\n')[0])
    trans = ""
    while True:
        feedback = input("[Y/N]:")
        if feedback in ["Y", "y", "Yes", "yes", "YES"]:
            print("User check success. Continuing...")
            trans = translation
            break
        elif feedback in ["N", "n", "No", "no", "NO"]:
            print("User check failure.")
            print("Re-translate? (Y)\nmanual input otherwise (N)")
            option = input("[Y/N]:")
            if option in ["Y", "y", "Yes", "yes", "YES"]:
                trans = GPTStuff.chat_call(client, next_proof.split("Proof")[0], error="theorem")
                print("Is the following translation correct?")
                print(next_proof.split("Proof")[0])
                print(trans.split('\n')[0])
            else:
                trans = input("manual translation:")
                trans = trans + "\n" + translation.split('\n')[1:]
                break
    return trans

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

def main(startup=None):
    if startup is None:
        startup_done = True
    else:
        startup_done = False
    try:
        shell_process, output_queue = shell_startup()
        # main loop
        main_loop(startup_done, shell_process , output_queue)
    except KeyboardInterrupt:
        print("\nUser Interrupt. Session terminated.")
    except ChildProcessError:
        print("Fatal Error. Shutting down.")
    finally:
        shell_process.stdin.close()
        shell_process.wait()
        print("Session Terminated.")

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
            trans = user_interaction(translation, next_proof)
            # writing translation and "end" if needed
            with open(TEMP_THY_FILE, 'a') as file:
                file.write(trans)
                if not trans.strip().endswith('end'):
                    file.write('\nend')
                file.close()
            status = {}
            Utils.change_namespace("Landau_GPT4", "temp", TEMP_THY_FILE)
        else:
            print("skipping first translation")
            status = {}
            Utils.change_namespace("Landau_GPT4", "temp", TEMP_THY_FILE)
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
            if not status.get("cheating_success"):
                step_by_step_translation(next_proof)
            if status.get("status") == Utils.StatusCode.OK:
                break

def parse_status(status):
    if status.get("status") == Utils.StatusCode.OK:
        shutil.copyfile(TEMP_THY_FILE, theory_file)
        Utils.change_namespace("temp", "Landau_GPT4", theory_file)
        GPTStuff.startup(theory_file)
    elif status.get("status") == Utils.StatusCode.SLEDGEHAMMER_NEEDED:
        if status.get("error_lines") is not None:
            success = Utils.cheating(TEMP_THY_FILE, status)
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
    for line in proof.split("."):
        trans += "\n" + GPTStuff.chat_call(client, line)

    GPTStuff.stop_step_by_step()

def get_next_proof(offset=0):
    global proof_counter
    if proof_counter >= len(proofs):
        return None
    ret = proofs[proof_counter+offset]
    if offset == 0:
        proof_counter += 1
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


def read_proofs(proof_file):
    global proofs
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


def find_current_proof():
    global proof_counter
    last_theo = ""
    last_def = ""
    with open(TEMP_THY_FILE, 'r') as f:
        for line in f:
            if line.startswith("theorem"):
                last_theo = line
            elif line.startswith("(* Definition"):
                last_def = line
    gr = re.search(r'\d+', last_def)
    if gr is not None:
        gr = int(gr.group())
    else:
        gr = 0
    theo = re.search(r'\d+', last_theo)
    if theo is not None:
        theo = int(theo.group())
    else:
        theo = 0
    proof_counter = theo + gr


#TODO refactor to Utils (GPT stuff need to stay here)
def read_params():
    global theory_file, client, proof_counter
    parameters = {}
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
    #TODO startup should load temp theory from config
    if not parameters.get("startup"):
        print("copying theory file")
        shutil.copyfile(theory_file, TEMP_THY_FILE)
    else:
        print("debug start")
    if parameters.get("fresh_start"):
        #TODO figure out what to do with empty file
        pass
    Utils.change_namespace("Landau_GPT4", "temp", TEMP_THY_FILE)
    print("initializing GPT module")
    client = GPTStuff.initialise(seed=int(parameters.get('seed')), model=parameters.get('model'), few_shot=int(parameters.get('few_shot')))
    GPTStuff.startup(theory_file)
    print("reading natural language proofs")
    read_proofs(parameters["proof"])
    print(f"found:{len(proofs)} proofs")
    proof_counter = int(parameters.get("starting_proof"))
    if not proof_counter:
        proof_counter = 0
    elif proof_counter == -1:
        find_current_proof()
    return parameters.get("startup")


if __name__ == '__main__':
    start = read_params()
    print("starting command line module")
    main(startup=start)
