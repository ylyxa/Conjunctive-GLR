def reconfigure(xs):
    if isinstance(xs, str):
        return xs
    else:
        return ''.join([reconfigure(x) for x in xs])