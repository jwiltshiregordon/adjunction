from RepresentationStabilityCategories import *
from AdditiveCategories import *

# Preliminary implementation of the category of FJ-modules defined by Patzt and Wiltshire-Gordon

# Set the degree FJ_d
d = 2
D = FI()

# Give a presentation matrix for an FI-module
# We will compute its degree <= d part as a rep of FJ_d
m = CatMat.from_string(ZZ, D, [3], '[[abc-bac,abc-bca]]', [3, 3])
m = CatMat.zero_matrix(ZZ, D, [2], [])
print
print 'If M is the FI-module with presentation matrix'
m.pp()
print
print 'then the low-degree part of M looks like'
for i in range(7):
    print i, ': ', m.coker_at(i)


# Shuffle up from Vl to Vm

def is_monotone(ls):
    sls = sorted(ls)
    return ls == sls


def is_split_monotone(l, m, p):
    return p[:l] == range(1, l + 1) and is_monotone(p[l:m]) and is_monotone(p[m:])


def shc_entry(l, m, sigma, tau):
    return 1 if is_split_monotone(l, m, sigma * tau.inverse()) else 0


def shc(l, m, n):
    cols = Permutations(n) if n >= l else []
    rows = Permutations(n) if n >= m else []
    return matrix(ZZ, len(rows), len(cols), [shc_entry(l, m, r, c) for r in rows for c in cols])


# Bracket back down

def ecoef(k, lie_inj, n, p):
    if list(p[k:]) != range(k + 1, n + 1):
        return 0
    return lie_inj.data_vector[list(Permutations(k)).index(Permutation(p[:k]))]


def ec_entry(k, lie_inj, n, sigma, tau):
    return ecoef(k, lie_inj, n, sigma * tau.inverse())


def ec(lie_inj, n, k):
    l = lie_inj.source[0]
    rows = Permutations(n) if n >= k else []
    cols = Permutations(n) if n >= l else []
    return matrix(ZZ, len(rows), len(cols), [ec_entry(l, lie_inj, n, r, c) for r in rows for c in cols])


def cyclic_permutations(s):
    assert len(s) >= 2
    return [[s[0]] + list(p) for p in Permutations(s[1:])]


def to_Lie_polynomial(l):
    if len(l) == 1:
        return [1], [chr(l[0] + 96)]
    last_char = chr(l[-1] + 96)
    coefs, words = to_Lie_polynomial(l[:-1])
    return coefs + [-c for c in coefs], [w + last_char for w in words] + [last_char + w for w in words]

def to_group_ring(coefs, words):
    ret = ''
    for c, w in zip(coefs, words):
        if c == 1:
            ret += '+' + w
        else:
            ret += '-' + w
    return ret[1:]


def concat(coefs1, words1, coefs2, words2):
    coefs = []
    words = []
    for a, w in zip(coefs1, words1):
        for b, v, in zip(coefs2, words2):
            coefs += [a * b]
            words += [w + v]
    return coefs, words


def to_bracketing(c):
    if len(c) == 1:
        return chr(c[0] + 96)
    b = '{' * (len(c) - 1) + chr(c[0] + 96) + ',' + ''.join([chr(x + 96) + '},' for x in c[1:]])
    return b[:-1]


name_to_poly = {}
names = {}
for x in range(d + 1):
    for y in range(d + 1):
        names[x, y] = []


for k in range(d + 1):
    for p in SetPartitions(k):
        singletons = [x for s in p for x in s if len(s) == 1]
        for brackets in itertools.product(*([Permutations(singletons)] +
                                            [cyclic_permutations(sorted(list(s))) for s in p if len(s) > 1])):
            inj = brackets[0]
            l = len(inj)
            lie = brackets[1:]
            inj_string = ''.join([chr(x + 96) for x in inj])
            name = inj_string + ''.join([to_bracketing(c) for c in lie])
            grpr = ([1], [inj_string])
            for c in lie:
                grpr = concat(*(grpr + to_Lie_polynomial(c)))
            poly = to_group_ring(*grpr)
            name_to_poly[name] = poly if k > 0 else '*'
            names[k, l] += [name]


FJ_homs = {}
hom_to_Sd = {}
hom_to_q_inj_lie = {}
for x in range(d + 1):
    for y in range(d + 1):
        FJ_homs[x, y] = []
        for q in range(0, d - x + 1):
            for r in names[x + q, y]:
                name = 't^' + str(q) + r
                FJ_homs[x, y] += [name]
                sh = CatMat(ZZ, D, [d], shc(x, x + q, d).transpose()[0], [d])
                inj_lie = CatMat.from_string(ZZ, D, [x + q], '[[' + name_to_poly[r] + ']]', [x + q])
                br = CatMat(ZZ, D, [d], ec(inj_lie, d, y).transpose()[0], [d])
                hom_to_Sd[x, name, y] = (br * sh).data_vector
                hom_to_q_inj_lie[x, name, y] = (q, inj_lie.data_vector)


# Direct calculation of Hom to compare
def sm(q, x):
    idq = identity_matrix(q)
    top = [idq[i + 1] - idq[i] for i in range(q - x - 1)]
    bot = idq[q - x:].rows()
    return matrix(top + bot)


def smoi(q, x):
    smqx = sm(q, x)
    return CatMat(ZZ, OI(), [q - 1] * smqx.nrows(), vector([e for v in smqx for e in v]), [q])


def FJqHom(q, x, y):
    moi = smoi(q, x)
    inj = OI_to_FI([])
    flat = FI_flat(y)
    tvs = flat(inj(moi)).transpose().kernel().basis()
    tr = CatMat(ZZ, FI(), [q], vector(ZZ, [e for v in tvs for e in v]), [q] * len(tvs))
    #oiex = CatMat(ZZ, OI(), range(q + 1),
    #              vector(ZZ, [1 if j == 0 else 0 for i in range(q + 1) for j in range(binomial(q, i))]), [q])
    #cvs = (flat(inj(oiex)) * tvs).columns()
    return tr


for x in range(d + 1):
    for y in range(d + 1):
        homs = FJ_homs[x, y]
        dv = vector(ZZ, [e for f in homs for e in hom_to_Sd[x, f, y]])
        cm = CatMat(ZZ, D, [d], dv, [d] * len(homs))
        direct = FJqHom(d, x, y)
        mo = matrix(ZZ, len(homs), factorial(d), dv)
        md = matrix(ZZ, len(homs), factorial(d), direct.data_vector)
        # If these two lines run without causing an error, then the hom-spaces coincide
        CatMat.matrix_solve_right(mo.transpose(), md.transpose())
        CatMat.matrix_solve_right(md.transpose(), mo.transpose())


FJ_hom_mats = {}
for x in range(d + 1):
    for y in range(d + 1):
        homs = FJ_homs[x, y]
        hm = matrix(ZZ, len(homs), factorial(d), [e for f in homs for e in hom_to_Sd[x, f, y]])
        FJ_hom_mats[x, y] = hm.transpose()


def FJ_hom(x, y):
    return FJ_homs[x, y]


def FJ_one(x):
    if x == 0:
        return vector(ZZ, [1 if f == 't^0' else 0 for f in FJ_hom(x, x)])
    return vector(ZZ, [1 if f == 't^0' + D.identity(x) else 0 for f in FJ_hom(x, x)])


def FJ_comp(x, f, y, g, z):
    fm = CatMat(ZZ, D, [d], hom_to_Sd[x, f, y], [d])
    gm = CatMat(ZZ, D, [d], hom_to_Sd[y, g, z], [d])
    fgm = matrix(ZZ, factorial(d), 1, list((gm * fm).data_vector))
    return CatMat.matrix_solve_right(FJ_hom_mats[x, z], fgm).column(0)

def mll(x, f, y):
    ret = f.replace('{', '[').replace('}', ']').replace('t^0', '').replace('t^1', 't')
    return ret if ret != '' else '1'
FJ = PreadditiveCategory(range(d + 1), FJ_one, FJ_hom, FJ_comp, morphism_latex_law=mll)
FJ.show_multiplication_table()
#FJ.test()

def I_one(x):
    return '*'


def I_hom(x, y):
    return ['*'] if x <= y else []


def I_comp(x, f, y, g, z):
    return '*'


FIopxFJ = ProductCategory(';', FI().op(), FJ)


# We build the map FI_flat(a) ---> FI_flat(b) coming from the FJ morphism z : a ---> b.
# This function evaluates along the FI-op map f.
# There should be a commuting square
#
#  FI_flat(a)(x) --z--> FI_flat(b)(x)
#      ^                    ^
#      |                    |
#      f                    f
#      |                    |
#  FI_flat(a)(y) --z--> FI_flat(b)(y)
#
def fundamental_law((y, a), fopz, (x, b)):
    f, z = FIopxFJ.break_string(fopz)
    q, inj_lie_v = hom_to_q_inj_lie[a, z, b]
    inj_lie = CatMat(ZZ, D, [a + q], inj_lie_v, [a + q])
    zx = (ec(inj_lie, x, b) * shc(a, a + q, x)).transpose()
    zy = (ec(inj_lie, y, b) * shc(a, a + q, y)).transpose()
    up_and_over = FI_flat(a)(x, f, y).transpose() * zx
    right_and_up = zy * FI_flat(b)(x, f, y).transpose()
    assert up_and_over == right_and_up
    return up_and_over

fundamental_rep = MatrixRepresentation(FIopxFJ, ZZ, fundamental_law)


# We specialize the factor of FI to the single matrix of interest
I = FiniteCategory([0, 1], I_one, I_hom, I_comp)
IxFJ = ProductCategory(';', I, FJ)

def law((x, a), ff, (y, b)):
    _, f = IxFJ.break_string(ff)
    fi_op_mat = \
        {(0, 0): CatMat.identity_matrix(ZZ, D.op(), m.target),
         (0, 1): m.transpose(),
         (1, 1): CatMat.identity_matrix(ZZ, D.op(), m.source)}[x, y]
    fj_mat = CatMat.from_string(ZZ, FJ, [a], '[[' + f + ']]', [b])
    return fundamental_rep(CatMat.kronecker_product(fi_op_mat, fj_mat))


m_rep = MatrixRepresentation(IxFJ, ZZ, law)
pres = m_rep.presentation()
v = [e for i, (x, a) in enumerate(pres.source)
       for j, (y, b) in enumerate(pres.target) for e in pres.entry_vector(i, j) if x == 1 and y == 1]
rows = [a for x, a in pres.source if x == 1]
cols = [b for y, b in pres.target if y == 1]
coker_pres = CatMat(ZZ, FJ, rows, v, cols)
print
print 'and the degree <= ' + str(d) + ' part of the tail of M is given by the cokernel of the FJ-matrix'
coker_pres.pp()
print
print 'which is much more information than just the tail invariants in degree 0 through ' + str(d)
print

for i in range(d + 1):
    print i, ': ', coker_pres.coker_at(i)
