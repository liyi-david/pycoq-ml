class ScanningMode:
    PLAIN = 0
    STRING = 1


def tokens2str(tokens):
    if isinstance(tokens, list):
        return "(" + " ".join(map(lambda t: tokens2str(t), tokens)) + ")"
    else:
        return str(tokens)

def get_tokens(string):
    tokens = []
    spaces = [' ', "\t", "\n"]
    brackets = ["(", ")"]
    quota = "\""
    curr = ""

    def push_token(token = None):
        nonlocal curr, tokens
        if token is None:
            if curr != "":
                tokens.append(curr)
            curr = ""
        else:
            if curr != "":
                raise Exception("push_token invoked while current token is unfinished")

            tokens.append(token)

    mode = ScanningMode.PLAIN
    for i in range(len(string)):
        if mode == ScanningMode.PLAIN:
            if string[i] in spaces:
                push_token()
            elif string[i] in brackets:
                push_token()
                push_token(string[i])
            elif string[i] == quota:
                push_token()
                curr = quota
                mode = ScanningMode.STRING
            else:
                curr += string[i]
        else:
            if string[i] == quota:
                curr += string[i]
                push_token()
                mode = ScanningMode.PLAIN

    return tokens


def get_tuple(tokens_or_string):
    tokens = None
    if isinstance(tokens_or_string, str):
        tokens = get_tokens(tokens_or_string)
    else:
        tokens = tokens_or_string

    if len(tokens) == 0:
        return []

    ptr = 0

    def read_tuple():
        nonlocal ptr
        result = []
        assert tokens[ptr] == '('

        while ptr < len(tokens):
            ptr += 1
            if tokens[ptr] == '(':
                result.append(read_tuple())
            elif tokens[ptr] == ')':
                return result
            else:
                result.append(tokens[ptr])

        if ptr == len(tokens):
            raise Exception("unclosed tuple %s" % str(tokens))

        return result

    if tokens[0] != '(':
        if len(tokens) > 1:
            raise Exception('invalid serapi tuple %s' % str(tokens))
        else:
            return tokens[0]
    else:
        return read_tuple()