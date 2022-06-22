def S1(x):
    return ''.join(x)


def pass_through(x):
    return x[0]


def pass_through_as_tuple(x):
    return tuple(x)


def pass_through_as_list(x):
    return x


def concat(x):
    return x[0] + x[1]


def flatten(x):
    try:
        if isinstance(x[0], str):
            return x[0]
        else:
            return flatten(x[0])
    except:
        return None


def reduce(x):
    comp = flatten(x[3])
    res = [x[8] if flatten(z) == comp else z for z in x[5]]
    return res
