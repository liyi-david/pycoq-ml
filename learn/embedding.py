from pycoq.serapi.coqobj import *

word_size = 20
sentence_len = 256


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
        result = ["apply"]
        result += term2seq(term.function)
        for arg in term.args:
            result += term2seq(arg)
    else:
        result = ["TODO"]

    return result[::-1]


def embedding(word):
    assert len(word) <= word_size
    return [ord(word[i]) if i < len(word) else 0 for i in range(word_size)]


def serialize(seq):
    assert len(seq) <= sentence_len
    result = []
    for i in range(sentence_len):
        result += embedding(seq[i] if i < len(seq) else [])

    return result


def vec2text(vec):
    # vec is supposed to be a 2-dimension array
    result = ""
    result += "%d\n" % len(vec)

    for line in vec:
        result += " ".join(map(lambda num: str(num), line)) + "\n"

    return result
