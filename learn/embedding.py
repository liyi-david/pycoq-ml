from pycoq.serapi.coqobj import *


embedding_size = 100
sentence_len = 50


def term2seq(term):
    assert isinstance(term, CoqTerm)
    result = []

    if type(term) in [CoqTermRel, CoqTermVar, CoqTermId, CoqTermSort, CoqTermInd, CoqTermConst]:
        result = [str(term)]
        return result
    elif isinstance(term, CoqTermProd):
        result = [
            'forall',
            '_' if term.var_quantified is None else str(term.var_quantified)
        ] + term2seq(term.type_quantified) + term2seq(term.term)
    elif isinstance(term, CoqTermLambda):
        result = [
                 'exists',
                 '_' if term.name_arg is None else str(term.name_arg)
             ] + term2seq(term.type_arg) + term2seq(term.term)
    elif isinstance(term, CoqTermApp):
        result = term2seq(term.function)
        for arg in term.args:
            result += term2seq(arg)
    else:
        result = ["TODO"]

    return ["("] + result + [")"]


def embedding(word):
    assert len(word) <= embedding_size
    return [ord(word[i]) if i < len(word) else 0 for i in range(embedding_size)]


def serialize(term):
    seq = term2seq(term)
    assert len(seq) <= sentence_len
    return [embedding(seq[i] if i < len(seq) else []) for i in range(sentence_len)]


def vec2text(vec):
    # vec is supposed to be a 2-dimension array
    result = ""
    result += "%d\n" % len(vec)

    for line in vec:
        result += " ".join(map(lambda num: str(num), line)) + "\n"

    return result