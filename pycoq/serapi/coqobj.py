def coq_obj_parse(tuple):
    if tuple[0] == 'CoqGoal':
        return CoqGoal(tuple)
    pass


class CoqGoal():
    def __init__(self, tuple):
        self.fg_goals = []
        self.bg_goals = []
        self.shelved_goals = []
        self.given_up_goals = []

        for item in tuple[1]:
            if item[0] == 'fg_goals':
                self.fg_goals = list(map(lambda item: CoqGoalSingle(item), item[1]))
            elif item[0] == 'bg_goals':
                self.bg_goals = list(map(
                    lambda goals: [CoqGoalSingle(i) for i in goals],
                    item[1]
                ))
            elif item[0] == 'shelved_goals':
                self.shelved_goals = list(map(lambda item: CoqGoalSingle(item), item[1]))
            elif item[0] == 'given_up_goals':
                self.given_up_goals = list(map(lambda item: CoqGoalSingle(item), item[1]))
            else:
                raise Exception("unhandled goals type %s" % (item[0]))


class CoqGoalSingle():
    def __init__(self, tuple):
        dicttuple = dict(tuple)
        self.name = dicttuple['name']
        self.type = CoqTerm(dicttuple['ty'])
        self.hypothesis = [CoqHypothesis(hyp) for hyp in dicttuple['hyp']]


class CoqHypothesis():
    def __init__(self, tuple):
        # TODO
        self.id = dict(tuple[0])['Id']
        pass

class CoqTerm():
    def __init__(self, tuple):
        print(tuple)
        pass