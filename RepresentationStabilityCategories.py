from CatMat import *

# FA
# The category of finite sets where morphisms are functions
def FA_one(x):
    return '*' if x == 0 else ''.join([chr(v + 97) for v in range(x)])

def FA_hom(x, y):
    return ['*'] if x == 0 else [''.join([chr(v + 97) for v in w]) for w in
                                 tuple(itertools.product(*([range(0, y)] * x)))]

def FA_comp(x, f, y, g, z):
    return '*' if x == 0 else ''.join([tuple(g)[ord(c) - 97] for c in tuple(f)])

def FA(objects=[]):
    return FiniteCategory(objects, FA_one, FA_hom, FA_comp)


# OI
# The the category of totally-ordered sets with monotone injections
# See Sam-Snowden's paper
def OI_hom(x, y):
    return ['*'] if x == 0 else [''.join([chr(v + 96) for v in sorted(list(w))]) for w in Subsets(y, x)]

def OI(objects=[]):
    return FiniteCategory(objects, FA_one, OI_hom, FA_comp)

# OA
# The category of totally-ordered sets with monotone maps
# The simplicial category \Delta omits the empty total order, but we allow it.
def OA_hom(x, y):
    if x == 0:
        return ['*']
    else:
        return [''.join([chr(v + 97) for v, p in enumerate(ic) for _ in range(p)]) for ic in IntegerVectors(x, y)]

def OA(objects):
    return FiniteCategory(objects, FA_one, OA_hom, FA_comp)

# FI
# The category of finite sets with injections
# See Church-Ellenberg-Farb
def FI_hom(x, y):
    return ['*'] if x == 0 else [''.join([chr(v + 96) for v in w]) for w in Permutations(y, x)]

def FI(objects=[]):
    return FiniteCategory(objects, FA_one, FI_hom, FA_comp)


# ncFin
# The category of noncommutative finite sets
# See Pirashvili-Richter, May-Thomason
def ncFin_one(x):
    return '|' + ''.join([chr(v + 97) + '|' for v in range(x)])

def ncFin_hom(x, y):
    if y == 0:
        if x == 0:
            return ['|']
        else:
            return []
    return ['|' + ''.join(cc) + '|' for cc in Permutations([chr(v + 97) for v in range(x)] + ['|'] * (y - 1))]

def ncFin_comp(x, f, y, g, z):
    if z == 0:
        # The only morphism to zero is the identity
        return '|'
    return '|' + ''.join([''.join([f.split('|')[ord(c) - 96] for c in s]) + '|' for s in g.split('|')[1:-1]])

def ncFin(objects):
    return FiniteCategory(objects, ncFin_one, ncFin_hom, ncFin_comp)


# We define the inclusion functors connecting these categories

def OI_to_FI(objects):
    def law(x, f, y):
        return x, f, y
    return Functor(OI(objects), law, FI(objects))

def OI_to_OA(objects):
    def law(x, f, y):
        return x, f, y
    return Functor(OI(objects), law, OA(objects))

def OI_to_FA(objects):
    def law(x, f, y):
        return x, f, y
    return Functor(OI(objects), law, FA(objects))

def FI_to_FA(objects):
    def law(x, f, y):
        return x, f, y
    return Functor(FI(objects), law, FA(objects))

def OA_to_ncFin(objects):
    def law(x, f, y):
        counts = [f.count(chr(97 + i)) for i in range(y)]
        m = '|'
        if y == 0:
            return 0, '|', 0
        id = FA_one(x)
        for c in counts:
            m += id[0: c] + '|'
            id = id[c:]
        return x, m, y
    return Functor(OA(objects), law, ncFin(objects))

def FI_to_ncFin(objects):
    def law(x, f, y):
        if y == 0:
            return 0, '|', 0
        m = '|'
        for i in range(y):
            if chr(i + 97) in f:
                p = f.index(chr(i + 97))
                m += chr(p + 97)
            m += '|'
        return x, m, y
    return Functor(FI(objects), law, ncFin(objects))

# The indecomposable flat FI-modules of Patzt and Wiltshire-Gordon
def FI_flat(k):
    def law(x, f, y):
        def entry(r, c):
            if any(ord(f[r[i] - 1]) - 96 != c[i] for i in range(k)):
                return 0
            if any(c.index(ord(f[r[i] - 1]) - 96) >= c.index(ord(f[r[i + 1] - 1]) - 96) for i in range(k, len(r) - 1)):
                return 0
            return 1
        rows = [] if x < k else Permutations(x)
        cols = [] if y < k else Permutations(y)
        if k == 0 and x == 0:
            return matrix(ZZ, 1, len(cols), [1] * len(cols))
        return matrix(ZZ, len(rows), len(cols), [entry(r, c) for r in rows for c in cols])
    return MatrixRepresentation(FI(), ZZ, law)

F = FI_to_ncFin([0, 1, 2, 3])
F.test()
