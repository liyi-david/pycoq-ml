from pycoq.core import CoqWorker
from pycoq.core import set_raw_send_receive_debug, set_serapi_addr
from pycoq.exception import PyCoqException
from pycoq.serapi.coqobj import *

import logging
import os
import re


set_serapi_addr("/home/liyi/projects/coq-serapi/sertop.native")
# set_raw_send_receive_debug(send=True, receive=True)


def scan_files(lst_paths):
    files = []
    for path in lst_paths:
        if not os.path.exists(path):
            logging.warning("%s does not exist." % path)
        elif os.path.isfile(path):
            if path.endswith(".v"):
                files.append(path)
            else:
                logging.warning("%s is not a coq source file" % path)
        elif os.path.isdir(path):
            for directory in os.walk(path):
                base_path = directory[0]
                for file in directory[2]:
                    if file.endswith(".v"):
                        files.append(os.path.join(base_path, file))

    return files


def reformat(coq_file):
    content = coq_file.read().replace("\n", " ")
    # 1. remove comments
    comments = re.compile(r'\(\*(.*?)\*\)')
    content = comments.sub("", content)
    # important: add one more space after the file, so that ". " will have a match here
    content += " "
    # 2. break into lines

    # pre-processing
    content = content.replace("..", "__dot_dot__")

    inString = False
    bracketLevel = 0
    i = 0
    while i < len(content):
        if content[i] == "\"":
            inString = not inString
        if content[i] == "(":
            bracketLevel += 1
        if content[i] == ")":
            bracketLevel -= 1
        if (inString or bracketLevel > 0) and content[i] == ".":
            content = content[:i] + "__dot__" + content[i+1:]
        i += 1

    lines = list(
        map(
            lambda line: line.strip() + ".",
            filter(lambda line: len(line.strip()) > 0, content.split(". "))
        )
    )

    for i in range(len(lines)):
        lines[i] = lines[i].replace("Require", "From Coq Require")
        lines[i] = lines[i].replace("__dot_dot__", "..")
        lines[i] = lines[i].replace("__dot__", ".")
        # print(lines[i])

    return lines


def scan(lst_paths):
    files = scan_files(lst_paths)
    files_failed = 0

    goals = []

    for file in files:
        print(file)
        with open(file, 'r') as f:
            coqcodes = reformat(f)

            worker = CoqWorker()
            try:
                for code in coqcodes:
                    state_ids = worker.add_and_execute_raw(code)
                    if isinstance(state_ids, list):
                        for state_id in state_ids:
                            objlist = worker.query_goals(state_id)
                            # TODO
                            for obj in objlist:
                                if isinstance(obj, CoqGoal):
                                    if len(obj.fg_goals) > 0:
                                        # only the current working goal is chosen
                                        goals.append(obj.fg_goals[0])
                                else:
                                    pass
            except Exception:
                files_failed += 1

            del worker

        # break

    print("%d failed in %d total." % (files_failed, len(files)))
    print("%d goals generated." % len(goals))