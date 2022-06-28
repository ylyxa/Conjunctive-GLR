def flatten(xs):
    if isinstance(xs, str):
        return xs
    else:
        return ''.join([flatten(x) for x in xs])


def reconfigure(xs):
    res = flatten(xs)
    return res