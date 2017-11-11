from subprocess import Popen, PIPE
from pycoq.config import *
from pycoq.logger import logger
from pycoq.serapi.response import *
from pycoq.serapi.parser import *


class CoqWorker:
    def __init__(self):
        serapi_addr = get_serapi_addr()
        self.subprocess = Popen(
            [serapi_addr],
            stdin=PIPE,
            stdout=PIPE,
            stderr=PIPE,
            shell=True
        )

        self.cmd_counter = 0
        self.max_exec_stateid = 0

        logger.info("CoqWorker successfully started.")

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

        # write command
        logger.debug("<<< " + cmd)
        self.subprocess.stdin.write((cmd + "\n").encode(encoding="utf-8"))
        self.subprocess.stdin.flush()

        answer = None

        # read response
        while self.subprocess.poll() is None:
            line = self.subprocess.stdout.readline().strip().decode(encoding="utf-8")
            logger.debug(">>> " + line)
            resp = parse_response(get_tuple(line))

            if isinstance(resp, SerFeedBack):
                pass
            elif isinstance(resp, SerAnswer):
                if isinstance(resp.answered_kind, SerAnswerAck):
                    pass
                elif isinstance(resp.answered_kind, SerAnswerCompleted):
                    # loop terminated when execution is finished
                    break
                elif isinstance(resp.answered_kind, SerAnswerException):
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

        # update state id if needed
        if isinstance(answer, SerAnswerAdded):
            pass
        else:
            # do not need to update
            pass

        return answer

    def add_raw(self, add_str, add_opts={}):
        assert isinstance(add_opts, dict)
        assert isinstance(add_str, str)

        # FIXME
        result = self.execute_cmd("(Add () \"%s\")" % add_str)
        if isinstance(result.answered_kind, SerAnswerAdded):
            return result.answered_kind.stateid
        else:
            raise PyCoqException("ADD", "unknown result %s" % type(result))

    def add_and_execute_raw(self, add_str, add_opts={}):
        stateid = self.add_raw(add_str, add_opts)
        self.exec(stateid)
        return stateid

    def exec(self, stateid):
        result = self.execute_cmd("(Exec %d)" % stateid)
        if result is None:
            # that is normal
            return
        # otherwise something must be wrong
        if isinstance(result.answered_kind, SerAnswerException):
            # TODO
            raise PyCoqException("Coq", "TODO Coq Runtime Exception")

    def query_goals(self, stateid=None):
        if stateid is None:
            stateid = self.max_exec_stateid
        elif stateid > self.max_exec_stateid:
            self.exec(stateid)
        return self.execute_cmd("(Query ((sid %d)) Goals)" % (stateid))

    def quit(self):
        return self.execute_cmd("Quit")