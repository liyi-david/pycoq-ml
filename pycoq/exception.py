class PyCoqException (Exception):
    def __init__(self, module, msg):
        Exception.__init__(self, msg)

        self.module = module