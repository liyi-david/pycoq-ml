from learn.scanner import *
from pycoq.config import set_serapi_addr, set_raw_send_receive_debug
from learn.render import render

set_serapi_addr("/home/liyi/projects/coq-serapi/sertop.native")
set_raw_send_receive_debug(send=True, receive=True)

# goals = scan(["/home/liyi/projects/coq-v8.7/theories/Logic/FinFun.v"])
goals = scan(["/home/liyi/projects/coq-v8.7/theories"], nonstop=False)
render(goals, filename='temp.txt')