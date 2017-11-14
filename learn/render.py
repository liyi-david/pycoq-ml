from sys import stdout
from pycoq.serapi.coqobj import CoqGoalSingle, CoqHypothesis
from learn.embedding import *


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