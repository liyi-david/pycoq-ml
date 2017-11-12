from pycoq.exception import PyCoqException
from pycoq.logger import logger

__serapi_addr = None
__coq_addr = None
__debug_send = False
__debug_receive = False


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


def set_coq_addr(addr):
    global __coq_addr
    __coq_addr = addr
    pass


def get_coq_addr():
    if __coq_addr is None:
        logger.info("Coq directory is not specified, use default path.")

    return __coq_addr


def set_raw_send_receive_debug(send=True, receive=True):
    global __debug_send, __debug_receive
    if not isinstance(send, bool) or not isinstance(receive, bool):
        raise PyCoqException("Config", "send_receive flag set to non-boolean value")

    __debug_send = send
    __debug_receive = receive


def get_raw_send_receive_debug():
    return __debug_send, __debug_receive