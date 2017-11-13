from subprocess import Popen, PIPE
from pycoq.config import *
from pycoq.logger import logger
from pycoq.serapi.response import *
from pycoq.serapi.parser import *


class CoqWorker:
    def __init__(self):
        serapi_addr = get_serapi_addr()
        coq_addr = get_coq_addr()

        if coq_addr is not None:
            invoked_cmd = "%s --prelude %s" % (serapi_addr, coq_addr)
        else:
            invoked_cmd = serapi_addr

        self.subprocess = Popen(
            [invoked_cmd],
            stdin=PIPE,
            stdout=PIPE,
            stderr=PIPE,
            shell=True
        )

        self.cmd_counter = 0
        self.max_exec_stateid = 0

        logger.info("CoqWorker successfully started by: %s" % invoked_cmd)

    def __del__(self):
        if self.quit() is None:
            self.subprocess.wait(100)
            logger.info("CoqWorker exited normally with returned value %d." % self.subprocess.returncode)
            return
        else:
            self.subprocess.terminate()
            logger.warn("CoqWorker terminated.")

    def execute_cmd(self, cmd):
        # TODO automatically detect encoding
        cmd = "(%d %s)" % (self.cmd_counter, cmd)
        self.cmd_counter += 1

        # debug flag
        raw_send_flag, raw_receive_flag = get_raw_send_receive_debug()

        # write command
        if raw_send_flag:
            logger.debug("<<< " + cmd)
        self.subprocess.stdin.write((cmd + "\n").encode(encoding="utf-8"))
        self.subprocess.stdin.flush()

        answer = None

        # read response
        while self.subprocess.poll() is None:
            line = self.subprocess.stdout.readline().strip().decode(encoding="utf-8")
            if raw_receive_flag:
                logger.debug(">>> " + line)

            resp = parse_response(get_tuple(line))

            if isinstance(resp, SerFeedBack):
                pass
            elif isinstance(resp, SerAnswer):
                if isinstance(resp, SerAnswerAck):
                    pass
                elif isinstance(resp, SerAnswerCompleted):
                    # loop terminated when execution is finished
                    break
                elif isinstance(resp, SerAnswerException):
                    # terminated abnormally
                    answer = resp
                    break
                else:
                    if answer is not None:
                        logger.error("answer is assigned dumplicatedly")

                    answer = resp
            elif resp is None:
                pass
            else:
                raise PyCoqException("CoqWorker", "unknown response type")

        return answer

    def add_raw(self, add_str, add_opts={}):
        assert isinstance(add_opts, dict)
        assert isinstance(add_str, str)

        # PATCHES
        add_str = add_str.strip().replace("Require Import", "From Coq Require Import")

        # FIXME
        result = self.execute_cmd("(Add () \"%s\")" % add_str)
        if result is None:
            return None

        if isinstance(result, SerAnswerAdded):
            return result.state_id
        else:
            raise PyCoqException("ADD", "unknown result %s" % type(result))

    def add_and_execute_raw(self, add_str, add_opts={}):
        state_id = self.add_raw(add_str, add_opts)

        if state_id is not None:
            exec_result = self.exec(state_id)
            if isinstance(exec_result, SerAnswerException):
                logger.error("@@@ " + add_str)
                raise PyCoqException("Coq", "Runtime exception occurred in Coq.")

        return state_id

    def exec(self, stateid):
        result = self.execute_cmd("(Exec %d)" % stateid)
        if result is None:
            # that is normal
            self.max_exec_stateid = stateid
            return
        # otherwise something must be wrong
        if isinstance(result, SerAnswerException):
            return result

    def query_goals(self, stateid=None):
        if stateid is None:
            stateid = self.max_exec_stateid
        elif stateid > self.max_exec_stateid:
            self.exec(stateid)

        result = self.execute_cmd("(Query ((sid %d)) Goals)" % (stateid))

        if isinstance(result, SerAnswerObjList):
            return result.objects
        else:
            raise PyCoqException("Coq", "Query does not return object list.")

    def quit(self):
        return self.execute_cmd("Quit")