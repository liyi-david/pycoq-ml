def parse_response(resp_tuple):
    if len(resp_tuple) == 0:
        return None

    if resp_tuple[0] == "Feedback":
        return SerFeedBack(resp_tuple)
    elif resp_tuple[0] == "Answer":
        return SerAnswer(resp_tuple)
    else:
        raise Exception("unknown response type %s" % str(resp_tuple[0]))


class SerFeedBack:
    def __init__(self, resp_tuple):
        pass


class SerAnswer:
    def __init__(self, resp_tuple):
        assert len(resp_tuple) == 3

        self.answered_tag = resp_tuple[1]
        self.answered_kind = parse_answer_kind(resp_tuple[2])


def parse_answer_kind(kind_tuple):
    if not isinstance(kind_tuple, list):
        if kind_tuple == 'Ack':
            return SerAnswerAck()
        elif kind_tuple == 'Completed':
            return SerAnswerCompleted()
    else:
        if kind_tuple[0] == 'Added':
            return SerAnswerAdded(kind_tuple)
        elif kind_tuple[0] == 'CoqExn':
            return SerAnswerException(kind_tuple)

    raise Exception("unhandled answer_kind %s" % (kind_tuple))


class SerAnswerAck:
    pass


class SerAnswerCompleted:
    pass


class SerAnswerAdded:
    def __init__(self, tuple):
        self.stateid = int(tuple[1])
        # TODO Loc.t && ...


class SerAnswerException:
    def __init__(self, tuple):
        pass