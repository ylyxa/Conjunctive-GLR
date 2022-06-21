def S1(x):
    return ''.join(x)


def pass_through(x):
    return x[0]


def pass_through_as_tuple(x):
    return tuple(x)


def pass_through_as_list(x):
    return x


def concat(x):
    return (x[0] + x[1])


def reduce(x):
    return [x[8] if z == x[3] else z for z in x[5]]
