class CoqElemId:
    def __init__(self, obj_tuple):
        assert obj_tuple[0] == "Id"
        self.value = obj_tuple[1]

    def __str__(self):
        return self.value


class CoqElemConstructor:
    def __init__(self, obj_tuple):
        self.inductive_type = CoqElemInductive(obj_tuple[0])
        self.index = int(obj_tuple[1])


class CoqElemConstant:
    def __init__(self, obj_tuple):
        self.id = CoqElemId(obj_tuple[3])

    def __str__(self):
        return str(self.id)


class CoqElemInductive:
    def __init__(self, obj_tuple):
        self.mutind = CoqElemMutind(obj_tuple[0])
        self.index = obj_tuple[1]

    def __str__(self):
        # todo why index?
        return str(self.mutind)


class CoqElemMutind:
    def __init__(self, obj_tuple):
        assert obj_tuple[0] =='Mutind'
        self.mpfile = obj_tuple[1]
        self.dirpath = obj_tuple[2]
        self.id = CoqElemId(obj_tuple[3])

    def __str__(self):
        return str(self.id)