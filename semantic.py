from copy import deepcopy

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


def reduce_rec(x, comp, replacer):
    if isinstance(x, str):
        return x
    if len(x) == 1:
        if flatten(x) == comp:
            x[0] = deepcopy(replacer)
            return x
        else:
            return reduce_rec(x[0], comp, replacer)
    else:
        for i, elem in enumerate(x.copy()):
            x[i] = reduce_rec(elem, comp, replacer)
        return x



def reduce(x):
    # print(x)
    comp = flatten(x[3])
    res = reduce_rec(x[5], comp, x[8])
    # res = [x[8] if flatten(z) == comp else z for z in x[5]]
    # print(x)
    return res
