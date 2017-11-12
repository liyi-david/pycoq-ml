def coq_obj_parse(obj_tuple):
    if obj_tuple[0] == 'CoqGoal':
        return CoqGoal(obj_tuple)
    pass


class CoqGoal:
    def __init__(self, obj_tuple):
        self.fg_goals = []
        self.bg_goals = []
        self.shelved_goals = []
        self.given_up_goals = []

        for goal_set in obj_tuple[1]:
            if goal_set[0] == 'fg_goals':
                self.fg_goals = list(map(lambda item: CoqGoalSingle(item), goal_set[1]))
            elif goal_set[0] == 'bg_goals':
                self.bg_goals = list(map(
                    lambda goals: [CoqGoalSingle(i) for i in goals],
                    goal_set[1]
                ))
            elif goal_set[0] == 'shelved_goals':
                self.shelved_goals = list(map(lambda item: CoqGoalSingle(item), goal_set[1]))
            elif goal_set[0] == 'given_up_goals':
                self.given_up_goals = list(map(lambda item: CoqGoalSingle(item), goal_set[1]))
            else:
                raise Exception("unhandled goals type %s" % (goal_set[0]))


class CoqGoalSingle:
    def __init__(self, obj_tuple):
        dict_tuple = dict(obj_tuple)
        self.name = dict_tuple['name']
        self.type = CoqTerm.parse(dict_tuple['ty'])
        self.hypothesis = [CoqHypothesis(hyp) for hyp in dict_tuple['hyp']]


class CoqHypothesis:
    def __init__(self, obj_tuple):
        self.ids = list(map(lambda idv: idv[0], obj_tuple[0]))
        assert len(self.ids) == 1
        # FIXME parse the options
        self.options = obj_tuple[1]
        self.term = CoqTerm.parse(obj_tuple[2])
        pass


class CoqTerm:
    identifier = "CoqTerm"

    def __init__(self, obj_tuple):
        pass

    @classmethod
    def parse(cls, obj_tuple):
        for sub_cls in CoqTerm.__subclasses__():
            if getattr(sub_cls, "identifier") == obj_tuple[0]:
                return sub_cls(obj_tuple)

        raise Exception("unhandled coq term type %s" % obj_tuple[0])


class CoqTermId(CoqTerm):
    identifier = "Id"

    def __init__(self, obj_tuple):
        self.id = obj_tuple[1]
        CoqTerm.__init__(self, obj_tuple)


class CoqTermConst(CoqTerm):
    identifier = "Const"

    def __init__(self, obj_tuple):
        # FIXME other fields are simply ignored
        self.term = CoqTerm.parse(obj_tuple[1][0][3])
        CoqTerm.__init__(self, obj_tuple)


class CoqTermProd(CoqTerm):
    identifier = "Prod"

    def __init__(self, obj_tuple):
        print(obj_tuple)
        # FIXME self.name = obj_tuple[1]
        self.left = CoqTerm.parse(obj_tuple[2])
        self.right = CoqTerm.parse(obj_tuple[3])
        CoqTerm.__init__(self, obj_tuple)