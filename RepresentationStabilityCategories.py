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
# F.test()

def FI_concatenation_law(xx, ff, yy):
    D = FI()
    C = ProductCategory(';', D, D)
    x1, x2 = xx
    f1, f2 = C.break_string(ff)
    y1, y2 = yy
    f1 = '' if f1 == '*' else f1
    f2 = '' if f2 == '*' else f2
    f1f2 = '*' if f1 + f2 == '' else f1 + ''.join([chr(ord(v) + y1) for v in f2])
    return CatMat.from_string(ZZ, D, [x1 + x2], '[[' + f1f2 + ']]', [y1 + y2])

FI_concatenation = MatrixRepresentation(ProductCategory(';', FI(), FI()), ZZ, FI_concatenation_law, target_cat=FI())


def subsum_indexing(x):
    u = range(x)
    return [([i for i in u if i in s], [i for i in u if i not in s]) for s in Subsets(u)]


def subsum(x):
    return [(len(s), len(t)) for s, t in subsum_indexing(x)]


def subsum_unit(x):
    D = FI()
    if x == 0:
        return CatMat.from_string(ZZ, D, [0], '[[*]]', [0])
    idx = D.identity(x)
    ind = subsum_indexing(x)
    entries = ','.join([''.join([idx[st.index(i)] for i in range(x)]) for s, t in ind for st in [s + t]])
    return CatMat.from_string(ZZ, D, [x], '[[' + entries + ']]', [x] * len(ind))


def subsum_law(x, f, y):
    D = FI()
    C = ProductCategory(';', D, D)
    sx = subsum(x)
    sxu = subsum_unit(x)
    sy = subsum(y)
    syu = subsum_unit(y)
    n = len(CatMat.zero_matrix(ZZ, C, sx, sy).data_vector)
    mm = matrix([(sxu * FI_concatenation(CatMat(ZZ, C, sx, v, sy))).data_vector for v in identity_matrix(ZZ, n).rows()])
    ff = CatMat.from_string(ZZ, D, [x], '[[' + f + ']]', [y])
    w = (ff * syu).data_vector
    u = CatMat.matrix_solve_right(mm.transpose(), matrix(ZZ, len(w), 1, w)).transpose()
    return CatMat(ZZ, C, sx, u.row(0), sy)


# This representation is the left adjoint to FI_concatenation
FI_decompositions = MatrixRepresentation(FI(), ZZ, subsum_law, target_cat=ProductCategory(';', FI(), FI()))

# Using work of Djament, tail shifts are always semi-induced
def FI_tail_shift(k):
    D = FI()
    C = ProductCategory(';', D, D)
    decomp = FI_decompositions
    flat = FI_flat(k)
    def apply_flat_law(xp, fg, yq):
        x, p = xp
        f, g = C.break_string(fg)
        y, q = yq
        ff = CatMat.from_string(ZZ, D, [x], '[[' + f + ']]', [y])
        return CatMat.kronecker_product(ff, flat(p, g, q))


    apply_flat = MatrixRepresentation(C, ZZ, apply_flat_law, target_cat=D)


    def tail_shift_law(x, f, y):
        return apply_flat(decomp(x, f, y))


    return MatrixRepresentation(D, ZZ, tail_shift_law, target_cat=D)