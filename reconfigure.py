from numpy import base_repr
from itertools import count

counter = None
letters = ['x', 'y', 'z']

def varname_generator():
    global counter, letters
    n = str(base_repr(next(counter), base=3))
    name = [letters[int(i)] for i in n]
    return name


def is_flat_var(x):
    return isinstance(x, list) and len(x) == 1 and isinstance(x[0], str)


def is_lambda(x):
    return isinstance(x, list) and len(x) == 6 and x[0] == '[' and x[1] == '\\' \
            and is_flat_var(x[2]) and x[3] == '->' and x[5] == ']'



def reconfigure_rec(xs, binding):
    if isinstance(xs, str):
        return xs
    if is_flat_var(xs):
        replacer = next(elem for elem in reversed(binding) if elem[1] == xs)[0]
        return replacer
    new_binding = binding.copy()
    if is_lambda(xs):
        replacer = varname_generator()
        new_binding.append((replacer, xs[2].copy()))
        xs[2] = replacer
        xs[4] = reconfigure_rec(xs[4], binding + new_binding)
        return xs
    for i, x in enumerate(xs.copy()):
        if is_flat_var(x):
            replacer = next(elem for elem in reversed(binding) if elem[1] == x)[0]
            xs[i] = replacer
        else:
            xs[i] = reconfigure_rec(xs[i], binding)
    return xs


def flatten(xs):
    if isinstance(xs, str):
        return xs
    else:
        return ''.join([flatten(x) for x in xs])


def reconfigure(xs):
    global counter
    counter = count()
    res = flatten(reconfigure_rec(xs, []))
    return res