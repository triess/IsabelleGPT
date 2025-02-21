import datetime
import pickle

from openai import OpenAI

import Utils

SEED = 12345
MODEL = "gpt-4"
global_messages = []
FEW_SHOT_NO = 5
WORKING_FILE = None
LOG_FILE = "files/gpt_messages.log"


def chat_loop(client, initial_messages):
    messages = initial_messages
    while True:
        text = input("next promt:")
        if text == "exit":
            break
        elif text:
            messages.append({"role": "user", "content": text})
            chat = client.chat.completions.create(model=MODEL, seed=SEED, temperature=0, messages=messages)
            reply = chat.choices[0].message.content
            print(f"reply:{reply}")
            messages.append({"role": "assistant", "content": reply})
    with open("files/save/messages.pkl", 'wb') as file:
        pickle.dump(messages, file)


def chat_call(client, mess, error=None, err_mess=None, cold_call=False):
    global global_messages
    messages = global_messages
    if not cold_call:
        if error == "isabelle":
            err_mess = "The following errors occurred in your translation of the proof please fix them but do not change the theorem statement in any way:\n" + mess
            messages.append({"role": "user", "content": err_mess})
        elif error == "theorem":
            if err_mess:
                messages.append({"role": "user", "content": err_mess + "\n" + mess})
            else:
                messages.append({"role": "user", "content": "The translation of the theorem statement is incorrect:\n" + mess})
        elif error == "proof":
            messages.append({"role": "user", "content": "the theorem statement has been manually corrected to: \n" + err_mess + "\nPlease retranslate the proof to match the new theorem:\n" + mess})
        elif error == "sledge":
            messages.append({"role": "user", "content": "The following line could not be proven by isabelle and sledgehammer. Please add mor steps or restructure the proof to elaborate.\n\n" + mess})
        else:
            messages.append({"role": "user", "content": mess})
    chat = client.chat.completions.create(model=MODEL, seed=SEED, temperature=0, messages=messages)
    reply = chat.choices[0].message.content
    reply = Utils.get_only_isabelle_code(reply)
    messages.append({"role": "assistant", "content": reply})
    global_messages = messages
    return reply


def start_step_by_step():
    global global_messages
    messages = global_messages
    messages.append({"role":"system", "content":"The following statements are not complete proofs but only "
                                                "single sentences of a proof. Please only translate the exact statements given. "
                                                "They do not have to be syntactically correct by themselves."})
    global_messages = messages

def stop_step_by_step():
    global global_messages
    messages = global_messages
    messages.append({"role":"system", "content":"The partial proofs are finished. You will be given complete proofs again."})
    global_messages = messages

def initialise(seed=None, model=None, few_shot=None):
    global SEED, MODEL, FEW_SHOT_NO
    if seed:
        SEED = seed
    if model:
        MODEL = model
    if few_shot:
        FEW_SHOT_NO = few_shot
    if "gpt" in model:
        API_KEY = open("files/openai_key.txt", "r").read()
    else:
        API_KEY = open("files/openai_key.txt", "r").read()
    OpenAI.api_key = API_KEY
    client = OpenAI(api_key=API_KEY)
    return client

def system_message(message):
    global global_messages
    global_messages.append({"role":"system", "content":message})

def fresh_start(examples=None, seed=None, model=None, few_shot=None):
    global global_messages
    initialise(seed=seed, model=model, few_shot=few_shot)
    messages = []
    with open("files/fresh_start.txt", 'r') as file:
        for line in file:
            line = line.strip().split("§")
            messages.append({"role": line[0], "content": line[1]})
        file.close()
    global_messages += messages
    return initialise(seed=seed, model=model, few_shot=few_shot)

def log_messages():
    global global_messages
    with open(LOG_FILE,"a") as file:
        file.write(str(datetime.datetime.now()) + "\n")
        for mess in global_messages:
            file.write(str(mess) + "\n")

def startup(theory_file):
    global global_messages, WORKING_FILE
    WORKING_FILE = theory_file

    try:
        mess, theory = Utils.parse_thy_file(theory_file, window=FEW_SHOT_NO)
    except ValueError:
        mess = []
        theory = []
        print("error reading theory, no message history reconstructed")
    theory = '\n'.join(theory)
    messages = []
    with open("files/GPT_startup_messages.txt", 'r') as file:
        for line in file:
            line = line.strip()
            messages.append({"role": "system", "content": line})
        file.close()
    messages.append({"role": "system", "content": theory})
    messages.append({"role": "system", "content": "We will now start translating further."})
    messages += mess
    global_messages = messages

def get_messages():
    global global_messages
    return global_messages

def read_file_to_gpt():
    messages = []
    with open("files/GPT-4_chat_on_formalizing_Landau.txt", "r", encoding="utf-8") as preset:
        preset.readline()
        line = preset.readline()
        content = ""
        mess = {}
        while line:
            # print(line)
            if line == "Input:\n" or line == "Input: \n":
                if len(content) > 0:
                    mess["role"] = "assistant"
                    mess["content"] = content.strip("\n").strip()
                    messages.append(mess)
                    mess = {}
                    content = ""
                line = preset.readline()
                continue
            if line == "Output:\n" or line == "Output: \n":
                if len(content) > 0:
                    mess["role"] = "user"
                    mess["content"] = content.strip("\n").strip()
                    messages.append(mess)
                    mess = {}
                    content = ""
                line = preset.readline()
                continue
            if line.startswith("Now please help"):
                mess["role"] = "assistant"
                mess["content"] = content.strip("\n").strip()
                messages.append(mess)
                mess = {}
                content = ""
                break
            content += line
            line = preset.readline()
        while line:
            if line == "User\n" or line == "User \n":
                if len(content) > 0:
                    mess["role"] = "assistant"
                    mess["content"] = content.strip("\n").strip()
                    messages.append(mess)
                    mess = {}
                    content = ""
                line = preset.readline()
                continue
            if line == "ChatGPT\n" or line == "ChatGPT \n":
                if len(content) > 0:
                    mess["role"] = "user"
                    mess["content"] = content.strip("\n").strip()
                    messages.append(mess)
                    mess = {}
                    content = ""
                line = preset.readline()
                continue
            if line == "You\n":
                line = preset.readline()
                continue
            content += line
            line = preset.readline()
        mess["role"] = "assistant"
        mess["content"] = content.strip("\n").strip()
        messages.append(mess)
    messages[0]["role"] = "user"
    return messages

'''
if __name__ == '__main__':
    with open("files/thy_file.pkl", "rb") as f:
        messages = pickle.load(f) #read_file_to_gpt()
    client = initialise()
    chat_loop(client, messages)
'''