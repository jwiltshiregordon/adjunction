from CatMat import *
from sage.all import vector, matrix


# Objects are subsets of a universe set
# Morphisms are inclusions
# Since the category is a poset, all morphisms are named *
def subsets_category(universe):
    def cat_one(x):
        return '*'

    def cat_hom(x, y):
        if x.issubset(y):
            return ['*']
        return []

    def cat_comp(x, f, y, g, z):
        return '*'

    cat = FiniteCategory(list(universe.subsets()), cat_one, cat_hom, cat_comp)
    return cat

# Builds the product of several categories
# Objects are tuples
# and morphisms are strings with format '(f,g,h)'
# (one-fold products don't change the category, and zero-fold products return the terminal category)


def product_category(*cats):
    n_factors = len(cats)
    left = '('
    sep = ','
    right = ')'

    def combine_strings(*strings):
        if len(strings) == 0:
            return '*'
        if len(strings) == 1:
            return strings[0]
        ts = '('
        for s in strings:
            ts += s + ','
        return ts[:-1] + ')'

    def break_string(s):
        # If the string is not a tuple, then we may have a zero- or one-fold product
        if s[0] != left or s[-1] != right:
            return s,
        return s[1:-1].split(sep)

    def cat_one(x):
        return combine_strings(*[cats[i].identity(x[i]) for i in range(n_factors)])

    def cat_hom(x, y):
        return [combine_strings(*t) for t in itertools.product(*[cats[i].hom(x[i], y[i]) for i in range(n_factors)])]

    def cat_comp(x, f, y, g, z):
        ff = break_string(f)
        gg = break_string(g)
        return combine_strings(*[cats[i].compose(x[i], ff[i], y[i], gg[i], z[i]) for i in range(n_factors)])

    cat = FiniteCategory(list(itertools.product(*[cats[i].objects for i in range(n_factors)])),
                         cat_one, cat_hom, cat_comp)
    return cat

def opposite_category(cat):
    def op_one(x):
        return cat.identity(x)

    def op_hom(x, y):
        return cat.hom(y, x)

    def op_comp(x, f, y, g, z):
        return cat.compose(z, g, y, f, x)

    op = FiniteCategory(cat.objects, op_one, op_hom, op_comp)
    return op