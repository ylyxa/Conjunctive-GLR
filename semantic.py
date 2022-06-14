def S1(x):
    return ''.join(x)


def pass_through(x):
    return x[0]


def pass_through_as_tuple(x):
    return tuple(x)


def pass_through_as_list(x):
    return x


def reduce(x):
    x[1][4] = x[3]
    return x
