import re

from sys import stdout
from learn.embedding import *


def tactic_simplify(tactic):
    """
    simplify the tactic, e.g. apply H0. -> apply
    :param tactic:
    :return: name of the tactic
    """
    names = re.split("[\;\.\ \(\)]", tactic)
    return names[0]


def render_natural(goals, tactics, filename=None):
    if filename is not None:
        f = open(filename, 'w')
    else:
        f = stdout

    f.write("%d\n" % len(goals))
    for goal in goals:
        assert isinstance(goal, CoqGoalSingle)
        f.write("%d\n" % len(goal.hypothesis))
        for hypo in goal.hypothesis:
            assert isinstance(hypo, CoqHypothesis)
            lsthypo = hypo.ids + term2seq(hypo.type)
            f.write(str(lsthypo))
            f.write("\n")

        f.write(str(term2seq(goal.type)))
        f.write("\n")
        f.write(tactic_simplify(tactics[goals.index(goal)]))
        f.write("\n")


def render(dataset, filename=None):
    if filename is not None:
        f = open(filename, 'w')
    else:
        f = stdout

    f.write("%d\n" % len(dataset))
    for goal in dataset:
        assert isinstance(goal, CoqGoalSingle)
        f.write("%d\n" % len(goal.hypothesis))
        for hypo in goal.hypothesis:
            assert isinstance(hypo, CoqHypothesis)
            vec_hypo = serialize(hypo.type)
            f.write(vec2text(vec_hypo))

        f.write(vec2text(serialize(goal.type)))
        f.write("\n")