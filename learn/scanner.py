from pycoq.core import CoqWorker
from pycoq.exception import PyCoqException
from pycoq.serapi.coqobj import *

import logging
import os
import re
import gc
import psutil


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
        if lines[i].startswith("Require"):
            tokens = lines[i].split(' ')
            if len(tokens) >= 3:
                if not tokens[2].startswith("Coq."):
                    lines[i] = lines[i].replace("Require", "From Coq Require")
            elif len(tokens) >= 2:
                if not tokens[1].startswith("Coq."):
                    lines[i] = lines[i].replace("Require", "From Coq Require")

        lines[i] = lines[i].replace("__dot_dot__", "..")
        lines[i] = lines[i].replace("__dot__", ".")
        # print(lines[i])

    return lines


def scan(lst_paths, nonstop=True):
    """
    scans all files in *lst_paths* and its sub-paths, runs them in Coq, and
    extract all the training data (including goal & tactic)
    :param lst_paths:
    :param nonstop:
    :return: training dataset
    """
    files = scan_files(lst_paths)
    files_failed = 0

    goals = []
    commands = []

    for file in files:
        print(file)
        info = psutil.virtual_memory()
        if info.percent > 90:
            print("Memory is going to overflow, stop scanning.")
            break

        # if memory is filled then exitw
        with open(file, 'r') as f:
            coqcodes = reformat(f)

            worker = CoqWorker()
            try:
                for code in coqcodes:
                    state_ids, cmds = worker.add_and_execute_raw(code)
                    if isinstance(state_ids, list):
                        for state_id in state_ids:
                            objlist = worker.query_goals(state_id)

                            # store the command used
                            assert(len(objlist) <= 1)
                            if len(objlist) == 1 and isinstance(objlist[0], CoqGoal) and len(objlist[0].fg_goals) > 0:
                                goals.append(objlist[0].fg_goals[0])
                            else:
                                # for each sid, we put a goal in this array
                                goals.append(None)

                            commands.append(cmds[state_ids.index(state_id)])
            except Exception as ex:
                files_failed += 1
                if not nonstop:
                    raise ex

            del worker

        gc.collect()

        # break

    # filter the valid tactics and goals
    selected_goals, tactics = [], []
    for i in range(len(goals)):
        if goals[i] is not None and commands[i + 1][0].islower():
            selected_goals.append(goals[i])
            tactics.append(commands[i + 1])

    print("%d failed in %d total." % (files_failed, len(files)))
    print("%d goals generated." % len(goals))

    return selected_goals, tactics