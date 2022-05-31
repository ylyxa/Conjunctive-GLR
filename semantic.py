def S1(x):
    return ''.join(x)


def pass_through(x):
    return x[0]


def pass_through_as_tuple(x):
    return tuple(x)


def reduce(x):
    expr = x[3]
    var = x[1][4]
    return tuple(x)
