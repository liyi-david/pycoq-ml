from pycoq.serapi.coqobj import coq_obj_parse


def parse_response(resp_tuple):
    if len(resp_tuple) == 0:
        return None

    if resp_tuple[0] == "Feedback":
        return SerFeedBack(resp_tuple)
    elif resp_tuple[0] == "Answer":
        return SerAnswer.parse(resp_tuple)
    else:
        raise Exception("unknown response type %s" % str(resp_tuple[0]))


class SerFeedBack:
    def __init__(self, _):
        pass


class SerAnswer:
    type = "SerAnswer"

    def __init__(self, answered_tag, _):
        pass
        self.answered_tag = answered_tag

    @classmethod
    def parse(cls, answer_tuple):
        for sub_cls in SerAnswer.__subclasses__():
            answer_kind_name = answer_tuple[2]
            if isinstance(answer_kind_name, list):
                answer_kind_name = answer_kind_name[0]

            if sub_cls.type == answer_kind_name:
                return sub_cls(answer_tuple[1], answer_tuple[2])

        raise Exception("unhandled answer_kind %s" % (answer_tuple[2]))


class SerAnswerAck(SerAnswer):
    type = "Ack"

    def __init__(self, answered_tag, answer_kind):
        SerAnswer.__init__(self, answered_tag, answer_kind)


class SerAnswerCompleted(SerAnswer):
    type = "Completed"

    def __init__(self, answered_tag, answer_kind):
        SerAnswer.__init__(self, answered_tag, answer_kind)


class SerAnswerAdded(SerAnswer):
    type = "Added"

    def __init__(self, answered_tag, answer_kind):
        self.state_id = int(answer_kind[1])
        self.info = dict(answer_kind[2])
        # TODO Loc.t && ...
        SerAnswer.__init__(self, answered_tag, answer_kind)

    def get_cmd(self, string):
        bp = int(self.info['bp'])
        ep = int(self.info['ep'])

        return string[bp:ep - 1]

    def get_tactic_name(self, string):
        return self.get_cmd(string).split(' ')[0]



class SerAnswerException(SerAnswer):
    type = "CoqExn"

    def __init__(self, answered_tag, answer_kind):
        # TODO
        SerAnswer.__init__(self, answered_tag, answer_kind)


class SerAnswerObjList(SerAnswer):
    type = "ObjList"

    def __init__(self, answered_tag, answer_kind):
        self.objects = []
        for obj in answer_kind[1]:
            self.objects.append(coq_obj_parse(obj))

        SerAnswer.__init__(self, answered_tag, answer_kind)
