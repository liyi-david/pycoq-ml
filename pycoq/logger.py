import logging

logger = logging.getLogger("pyCoq")
logger.setLevel(logging.DEBUG)

strhandler = logging.StreamHandler()
strhandler.setFormatter(logging.Formatter('%(asctime)s [%(name)s|%(levelname)7s] %(message)s'))

logger.addHandler(strhandler)