import sys, os
sys.path.append(os.path.split(os.path.split(os.path.realpath(__file__))[0])[0])

from learn.scanner import *
from pycoq.config import set_serapi_addr, set_raw_send_receive_debug
from learn.render import render, render_natural


set_serapi_addr("/home/liyi/projects/coq-serapi/sertop.native")
# set_raw_send_receive_debug(send=True, receive=True)

goals, tactics = scan(["/home/liyi/projects/pycoq-ml/db/reo.v"])
render_natural(goals, tactics, filename='reo_ds.txt')