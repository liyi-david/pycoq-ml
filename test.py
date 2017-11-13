from pycoq.core import CoqWorker
from pycoq.config import *
from pycoq.logger import logger
from logging import INFO


set_serapi_addr("/home/liyi/projects/coq-serapi/sertop.native")
set_raw_send_receive_debug(True, True)
# set_coq_addr("/home/liyi/projects/coq-v8.7")
# logger.setLevel(INFO)

w = CoqWorker()

with open("/home/liyi/projects/coq-v8.7/theories/Arith/Compare_dec.v") as fin:
    cache = ""
    for line in fin:
        # it is very import to remove all the endl chars, it may lead to weird behavior in serapi
        cache += line.replace("\n", " ")
        if cache.strip().endswith("."):
            sid = w.add_and_execute_raw(cache)
            goals = w.query_goals(sid)
            for goal in goals:
                print(goal)
            cache = ""
