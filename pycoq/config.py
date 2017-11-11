from pycoq.exception import PyCoqException

__serapi_addr = None


def set_serapi_addr(addr):
    global __serapi_addr
    __serapi_addr = addr
    # TODO check if it exists
    pass


def get_serapi_addr():
    if __serapi_addr is None:
        raise PyCoqException("config", "address of serapi is not correctly specified. " +
                                       "use pycoq.config.set_serapi_addr(addr) to fix this problem."
                             )
    return __serapi_addr