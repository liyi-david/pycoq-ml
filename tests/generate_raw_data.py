import sys, os
sys.path.append(os.path.split(os.path.split(os.path.realpath(__file__))[0])[0])
print(sys.path)

from learn.scanner import *
from pycoq.config import set_serapi_addr, set_raw_send_receive_debug
from learn.render import render, render_natural


set_serapi_addr("/home/liyi/projects/coq-serapi/sertop.native")
# set_raw_send_receive_debug(send=True, receive=True)

# goals = scan(["/home/liyi/projects/coq-v8.7/theories/Logic/FinFun.v"])
goals, tactics = scan(["/home/liyi/projects/coq-v8.7/theories/ZArith"], nonstop=False)
# goals, tactics = scan(["/home/liyi/projects/coq-v8.7/theories/ZArith/ZArith_dec.v"], nonstop=False)
render_natural(goals, tactics, filename='raw_ds.txt')

goals, tactics = scan("../db/reo.v")
render_natural(goals, tactics, filename='reo_ds.txt')