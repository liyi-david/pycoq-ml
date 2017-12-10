from pycoq.core import CoqWorker
from pycoq.config import set_serapi_addr, set_coq_addr, set_raw_send_receive_debug

set_raw_send_receive_debug(True, True)

set_serapi_addr("/home/liyi/projects/coq-serapi/sertop.native")
set_coq_addr("/home/liyi/projects/coq-v8.7")
w = CoqWorker()
w.add_and_execute_raw("Parameters A B:Prop.")
sid, cmd = w.add_and_execute_raw("Goal A -> A.")
w.add_and_execute_raw("intros.")
w.add_and_execute_raw("tauto.")
w.add_and_execute_raw("Qed.")
w.query_goals(sid[0])