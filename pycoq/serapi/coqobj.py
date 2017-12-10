# TODO from coq object to string (especially, should be able sent directly into coq)


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
                # self.bg_goals = list(map(
                #     lambda goals: [CoqGoalSingle(i) for i in goals],
                #     goal_set[1]
                # ))
                pass
            elif goal_set[0] == 'shelved_goals':
                self.shelved_goals = list(map(lambda item: CoqGoalSingle(item), goal_set[1]))
            elif goal_set[0] == 'given_up_goals':
                self.given_up_goals = list(map(lambda item: CoqGoalSingle(item), goal_set[1]))
            else:
                raise Exception("unhandled goals type %s" % (goal_set[0]))

    def __str__(self):
        result = ""
        if len(self.fg_goals) > 0:
            result += "foreground goals:\n"
            for i in range(len(self.fg_goals)):
                result += "[%d] %s\n" % (i, self.fg_goals[i])
        if len(self.bg_goals) > 0:
            result += "background goals:\n"
            for i in range(len(self.bg_goals)):
                result += "[%d] %s\n" % (i, self.bg_goals[i])
        if len(self.shelved_goals) > 0:
            result += "shelved goals:\n"
            for i in range(len(self.shelved_goals)):
                result += "[%d] %s\n" % (i, self.shelved_goals[i])
        if len(self.given_up_goals) > 0:
            result += "given up goals:\n"
            for i in range(len(self.given_up_goals)):
                result += "[%d] %s\n" % (i, self.given_up_goals[i])
        return result


class CoqGoalSingle:
    def __init__(self, obj_tuple):
        dict_tuple = dict(obj_tuple)
        if 'name' not in dict_tuple:
            print(dict_tuple)
        self.name = dict_tuple['name']
        self.type = CoqTerm.parse(dict_tuple['ty'])
        self.hypothesis = [CoqHypothesis(hyp) for hyp in dict_tuple['hyp']]

    def __str__(self):
        return "{%s} |- %s" % (
            ", ".join(map(lambda hypo: str(hypo), self.hypothesis)),
            str(self.type)
        )


class CoqHypothesis:
    def __init__(self, obj_tuple):
        self.ids = list(map(lambda idv: idv[1], obj_tuple[0]))
        # FIXME parse the options
        self.options = obj_tuple[1]
        self.type = CoqTerm.parse(obj_tuple[2])
        pass

    def __str__(self):
        return "%s : %s" % (
            " ".join(map(lambda id: str(id), self.ids)),
            str(self.type)
        )


class CoqTerm:
    identifier = "CoqTerm"
    parent = None

    def __init__(self, obj_tuple, parent):
        self.parent = parent
        pass

    @classmethod
    def parse(cls, obj_tuple, parent=None):
        for sub_cls in CoqTerm.__subclasses__():
            if getattr(sub_cls, "identifier") == obj_tuple[0]:
                return sub_cls(obj_tuple, parent)

        raise Exception("unhandled coq term type %s" % obj_tuple[0])

    def __str__(self):
        return ""


class CoqTermId(CoqTerm):
    identifier = "Id"

    def __init__(self, obj_tuple, parent):
        CoqTerm.__init__(self, obj_tuple, parent)
        self.id = obj_tuple[1]

    def __str__(self):
        return self.id


class CoqTermConst(CoqTerm):
    identifier = "Const"

    def __init__(self, obj_tuple, parent):
        CoqTerm.__init__(self, obj_tuple, parent)

        # FIXME other fields are simply ignored
        self.term = CoqTerm.parse(obj_tuple[1][0][3], self)

    def __str__(self):
        return str(self.term)


class CoqTermInd(CoqTerm):
    identifier = "Ind"

    def __init__(self, obj_tuple, parent):
        CoqTerm.__init__(self, obj_tuple, parent)
        # print(obj_tuple)
        # FIXME other information
        self.inductive = CoqElemInductive(obj_tuple[1][0])
        self.univs = obj_tuple[1][1]

    def __str__(self):
        return str(self.inductive)


class CoqTermSort(CoqTerm):
    identifier = "Sort"

    def __init__(self, obj_tuple, parent):
        CoqTerm.__init__(self, obj_tuple, parent)
        self.type = obj_tuple[1][0]
        assert self.type in ['Prop', 'Type']

    def __str__(self):
        return self.type


class CoqTermRel(CoqTerm):
    identifier = "Rel"

    def __init__(self, obj_tuple, parent):
        CoqTerm.__init__(self, obj_tuple, parent)
        self.value = int(obj_tuple[1])

    def __str__(self):
        # locate the variable
        left = self.value
        p = self

        while left > 0 and p is not None:
            if isinstance(p.parent, CoqTermProd):
                if p == p.parent.term:
                    left -= 1

            if isinstance(p.parent, CoqTermLambda):
                if p == p.parent.term:
                    left -= 1

            p = p.parent

        if p is None:
            raise Exception("failed to find reference for bounded variable.")

        if isinstance(p, CoqTermLambda):
            return str(p.name_arg)
        elif isinstance(p, CoqTermProd):
            return str(p.var_quantified)


class CoqTermVar(CoqTerm):
    identifier = "Var"

    def __init__(self, obj_tuple, parent):
        CoqTerm.__init__(self, obj_tuple, parent)
        self.id = CoqTerm.parse(obj_tuple[1], self)

    def __str__(self):
        return str(self.id)


class CoqTermApp(CoqTerm):
    identifier = "App"

    def __init__(self, obj_tuple, parent):
        CoqTerm.__init__(self, obj_tuple, parent)
        self.function = CoqTerm.parse(obj_tuple[1], self)
        self.args = [CoqTerm.parse(term_tuple, self) for term_tuple in obj_tuple[2]]

    def __str__(self):
        return "(%s %s)" % (
            str(self.function),
            " ".join(list(map(lambda term: str(term), self.args)))
        )


class CoqTermProd(CoqTerm):
    identifier = "Prod"

    def __init__(self, obj_tuple, parent):
        CoqTerm.__init__(self, obj_tuple, parent)

        if obj_tuple[1] == 'Anonymous':
            self.var_quantified = None
        elif obj_tuple[1][0] == 'Name':
            self.var_quantified = CoqTerm.parse(obj_tuple[1][1], self)
        else:
            raise Exception("unrecognized prod quantified variable %s" % obj_tuple[1])

        self.type_quantified = CoqTerm.parse(obj_tuple[2], self)
        self.term = CoqTerm.parse(obj_tuple[3], self)

    def __str__(self):
        if self.var_quantified is not None:
            return "forall (%s:%s), %s" % (
                self.var_quantified,
                self.type_quantified,
                self.term
            )
        else:
            return "%s -> %s" % (self.type_quantified, self.term)


class CoqTermLambda(CoqTerm):
    identifier = "Lambda"

    def __init__(self, obj_tuple, parent):
        CoqTerm.__init__(self, obj_tuple, parent)

        if obj_tuple[1] == 'Anonymous':
            self.name_arg = None
        elif obj_tuple[1][0] == 'Name':
            self.name_arg = CoqTerm.parse(obj_tuple[1][1], self)
        else:
            raise Exception("unrecognized lambda arg variable %s" % obj_tuple[1])

        self.type_arg = CoqTerm.parse(obj_tuple[2], self)
        self.term = CoqTerm.parse(obj_tuple[3], self)

    def __str__(self):
        if self.name_arg is not None:
            return "exists %s:%s, %s" % (
                self.name_arg,
                self.type_arg,
                self.term
            )
        else:
            raise Exception("unhandled lambda str request")


class CoqTermConstruct(CoqTerm):
    identifier = "Construct"

    def __init__(self, obj_tuple, parent):
        self.constructor = CoqElemConstructor(obj_tuple[1][0])
        # todo parse univs
        self.univs = obj_tuple[1][1]
        CoqTerm.__init__(self, obj_tuple, parent)


class CoqTermCase(CoqTerm):
    identifier = "Case"

    def __init__(self, obj_tuple, parent):
        print(obj_tuple)
        CoqTerm.__init__(self, obj_tuple, parent)


class CoqTermEvar(CoqTerm):
    identifier = "Evar"

    def __init__(self, obj_tuple, parent):
        print(obj_tuple)
        CoqTerm.__init__(self, obj_tuple, parent)


class CoqTermLetIn(CoqTerm):
    identifier = "LetIn"

    def __init__(self, obj_tuple, parent):
        print(obj_tuple)
        CoqTerm.__init__(self, obj_tuple, parent)


class CoqTermCast(CoqTerm):
    identifier = "Cast"

    def __init__(self, obj_tuple, parent):
        print(obj_tuple)
        CoqTerm.__init__(self, obj_tuple, parent)


class CoqTermFix(CoqTerm):
    identifier = "Fix"

    def __init__(self, obj_tuple, parent):
        print(obj_tuple)
        CoqTerm.__init__(self, obj_tuple, parent)


class CoqTermCoFix(CoqTerm):
    identifier = "CoFix"

    def __init__(self, obj_tuple, parent):
        print(obj_tuple)
        CoqTerm.__init__(self, obj_tuple, parent)


class CoqTermProj(CoqTerm):
    identifier = "Proj"

    def __init__(self, obj_tuple, parent):
        print(obj_tuple)
        CoqTerm.__init__(self, obj_tuple, parent)


class CoqTermMeta(CoqTerm):
    identifier = "Meta"

    def __init__(self, obj_tuple, parent):
        print(obj_tuple)
        CoqTerm.__init__(self, obj_tuple, parent)


class CoqElemConstructor:
    def __init__(self, obj_tuple):
        self.inductive_type = CoqElemInductive(obj_tuple[0])
        self.index = int(obj_tuple[1])


class CoqElemInductive:
    def __init__(self, obj_tuple):
        self.mutind = CoqElemMutind(obj_tuple[0])
        self.index = obj_tuple[1]

    def __str__(self):
        return str(self.mutind) + "_" + str(self.index)


class CoqElemMutind:
    def __init__(self, obj_tuple):
        """
        refer to coq github repo at kernel/names.mli, line 392 - 407
        :param obj_tuple:
        """
        assert obj_tuple[0] =='Mutind'
        # obj_tuple[1] is ModPath
        # obj_tuple[2] is DirPath
        self.id = CoqTerm.parse(obj_tuple[3], self)

    def __str__(self):
        return str(self.id)