from learn.embedding import *

import numpy as np

supported_tactics = ['absurd', 'apply', 'assert', 'assumption', 'auto', 'boolify_even_odd', 'case', 'case_eq', 'change', 'clear', 'compute', 'congruence', 'constructor', 'contradict', 'cut', 'decide', 'destruct', 'discriminate', 'do', 'easy', 'elim', 'enough', 'exact', 'exfalso', 'exists', 'f_equal', 'firstorder', 'generalize', 'induction', 'intro', 'intros', 'intuition', 'inversion', 'inversion_clear', 'left', 'now', 'omega', 'pattern', 'red', 'refine', 'reflexivity', 'remember', 'repeat', 'replace', 'revert', 'rewrite', 'right', 'ring', 'ring_simplify', 'romega', 'set', 'simpl', 'simple', 'specialize', 'split', 'subst', 'symmetry', 'tauto', 'transitivity', 'trivial', 'unfold', 'zero_or_not']
time_step = 15

def load_dataset(file, limit=None):
    X = []
    Y = []

    raw_X = []
    raw_Y = []

    maxlen_word = 0
    maxlen_sentence = 0
    maxlen_list = 0

    if limit is None:
        limit = 5000000

    print("load dataset %s" % file)

    with open(file, 'r') as fin:
        n = int(fin.readline())

        for i in range(min(n, limit)):
            # read data
            nhypo = int(fin.readline())
            x = [
                eval(fin.readline()) for j in range(nhypo)
            ]
            x.append(eval(fin.readline()))
            tactic = fin.readline().strip()

            for sent in x:
                maxlen_sentence = max(maxlen_sentence, len(sent))
                for word in sent:
                    maxlen_word = max(maxlen_word, len(word))

            maxlen_list = max(maxlen_list, len(x))

            if tactic == 'admit':
                # admit is not a valid tactic
                continue

            raw_X.append(x)
            raw_Y.append(tactic)

    print("MAX DATA SIZE: ", maxlen_list, maxlen_sentence, maxlen_word)

    for i in range(len(raw_X)):
        try:
            nx = list(map(lambda item: serialize(item), raw_X[i]))
            if len(nx) < time_step:
                nx = [[0 for _ in range(len(nx[0]))] for i in range(time_step - len(nx))] + nx

            if len(nx) > time_step:
                nx = nx[len(nx) - time_step:]

            ny = [1 if supported_tactics.index(raw_Y[i]) == j else 0 for j in range(len(supported_tactics))]
            X.append(nx)
            Y.append(ny)
        except Exception as _:
            pass

    return np.array(X), np.array(Y)


def get_maximum_indexes(lst, num):
    # in case num is an array
    lst = list(lst)
    sn = sorted(list(lst), reverse=True)
    sn = sn[:num]
    sn = [lst.index(i) for i in sn]
    return sn
