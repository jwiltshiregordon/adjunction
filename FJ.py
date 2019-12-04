from RepresentationStabilityCategories import *
from AdditiveCategories import *

# Preliminary implementation of the category of FJ-modules defined by Patzt and Wiltshire-Gordon
# https://arxiv.org/abs/1909.09729

# Shuffle up from Vl to Vm

def is_monotone(ls):
    sls = sorted(ls)
    return ls == sls


def is_split_monotone(l, m, p):
    return p[:l] == list(range(1, l + 1)) and is_monotone(p[l:m]) and is_monotone(p[m:])


def shc_entry(l, m, sigma, tau):
    return 1 if is_split_monotone(l, m, sigma * tau.inverse()) else 0


def shc(l, m, n):
    cols = Permutations(n) if n >= l else []
    rows = Permutations(n) if n >= m else []
    return matrix(ZZ, len(rows), len(cols), [shc_entry(l, m, r, c) for r in rows for c in cols])


# Bracket back down

def ecoef(k, lie_inj, n, p):
    if list(p[k:]) != list(range(k + 1, n + 1)):
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

def FJ(d):
    name_to_poly = {}
    names = {}
    for x in range(d + 1):
        for y in range(d + 1):
            names[x, y] = []

    D = FI()

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
                    #print (x, y, q, r)
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


    #for x in range(d + 1):
    #    for y in range(d + 1):
    #        homs = FJ_homs[x, y]
    #        dv = vector(ZZ, [e for f in homs for e in hom_to_Sd[x, f, y]])
    #        cm = CatMat(ZZ, D, [d], dv, [d] * len(homs))
    #        direct = FJqHom(d, x, y)
    #        mo = matrix(ZZ, len(homs), factorial(d), dv)
    #        md = matrix(ZZ, len(homs), factorial(d), direct.data_vector)
    #        # If these two lines run without causing an error, then the hom-spaces coincide
    #        CatMat.matrix_solve_right(mo.transpose(), md.transpose())
    #        CatMat.matrix_solve_right(md.transpose(), mo.transpose())


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
    FJd = PreadditiveCategory(range(d, -1, -1), FJ_one, FJ_hom, FJ_comp, morphism_latex_law=mll)
    FIopxFJ = ProductCategory(';', FI(range(4)).op(), FJd)

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
    def fundamental_law(ya, fopz, xb):
        y, a = ya
        x, b = xb
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

    # Finds an FJ matrix that maps in degree d to the symmetric group vector v using Xi
    def solve_to_Xi(x, v, y):
        vv = CatMat.matrix_solve_right(FJ_hom_mats[x, y], matrix(ZZ, factorial(d), 1, list(v))).column(0)
        return CatMat(ZZ, FJd, [x], vv, [y])

    return FJd, fundamental_rep, solve_to_Xi


# Current implementation is safe
# but it would be much faster to truncate by power of t
def FJ_restrict(d, e):
    C, XiC, _ = FJ(d)
    D, _, solve_to_XiD = FJ(e)
    F = FI()
    iddm = CatMat.identity_matrix(ZZ, F, [e])
    def res_law(x, f, y):
        if x > e or y > e:
            return CatMat.zero_matrix(ZZ, D, [i for i in [x] if i <= e], [j for j in [y] if j <= e])
        m = CatMat.from_string(ZZ, C, [x], '[[' + f + ']]', [y])
        mi = CatMat.kronecker_product(iddm.transpose(), m)
        return solve_to_XiD(x, XiC(mi).row(0), y)

    return MatrixRepresentation(C, ZZ, res_law, target_cat=D)


# Alternative implementation that needs debugging and a proof of correctness
# def truncation(e):
#     def truncation_law(x, f, y):
#         ee = x + int(''.join(ch for ch in f if ch.isdigit()))
#         if x <= e and y <= e and ee <= e:
#             return CatMat.from_string(ZZ, C, [x], '[[' + f + ']]', [y])
#         if x <= e and y <= e and ee > e:
#             return CatMat.zero_matrix(ZZ, C, [x], [y])
#         return CatMat.zero_matrix(ZZ, C, [x] if x <= e else [], [y] if y <= e else [])
#
#     return MatrixRepresentation(C, ZZ, truncation_law, target_cat=C)


def FJ_shift(d):
    C, Xi, solve_to_Xi = FJ(d + 1)
    E, _, _ = FJ(d)
    D = FI()
    res = FJ_restrict(d + 1, d)
    def iota(k, n):
        if k == n:
            return zero_matrix(ZZ, factorial(d), 0)
        if k > n:
            return matrix(ZZ, 0, 0, [])
        return block_matrix([[identity_matrix(ZZ, factorial(n))], [
            -matrix(ZZ, factorial(n), factorial(n), [1 if r[k] == c[0] and c[1:] == r[:k] + r[k + 1:] else 0
                                                     for r in Permutations(range(n)) for c in
                                                     Permutations(range(n))])]])
    def copi(k, n):
        if k == n:
            return identity_matrix(ZZ, factorial(d))
        if k > n:
            return matrix(ZZ, 0, 0, [])
        return block_matrix([[identity_matrix(ZZ, factorial(n)) * 0], [identity_matrix(ZZ, factorial(n))]])

    def iso(k, n):
        return block_matrix([[iota(k, n), copi(k, n)]])

    def FJ_shift_law(x, f, y):
        topid = [] + (d + 1) * [d] + [d + 1]
        m = CatMat.identity_matrix(ZZ, D, topid)
        o = CatMat.from_string(ZZ, C, [x], '[[' + f + ']]', [y])
        mo = CatMat.kronecker_product(';', m.transpose(), o)
        zm = iso(y, d + 1).inverse() * Xi(mo).transpose() * iso(x, d + 1)
        dd = factorial(d + 1)
        a = solve_to_Xi(x + 1, zm.column(0)[:dd], y + 1)
        b = solve_to_Xi(x + 1, zm.column(0)[dd:], y)
        c = solve_to_Xi(x, zm.column(dd)[dd:], y)
        ret = CatMat.block_matrix([[a, b], [0, c]])
        return res(ret)

    return MatrixRepresentation(E, ZZ, FJ_shift_law, target_cat=E)


def FJ_derivative(d):
    C, Xi, solve_to_Xi = FJ(d + 1)
    E, _, _ = FJ(d)
    D = FI()
    res = FJ_restrict(d + 1, d)
    def iota(k, n):
        if k == n:
            return zero_matrix(ZZ, factorial(d), 0)
        if k > n:
            return matrix(ZZ, 0, 0, [])
        return block_matrix([[identity_matrix(ZZ, factorial(n))], [
            -matrix(ZZ, factorial(n), factorial(n), [1 if r[k] == c[0] and c[1:] == r[:k] + r[k + 1:] else 0
                                                     for r in Permutations(range(n)) for c in
                                                     Permutations(range(n))])]])
    def copi(k, n):
        if k == n:
            return identity_matrix(ZZ, factorial(d))
        if k > n:
            return matrix(ZZ, 0, 0, [])
        return block_matrix([[identity_matrix(ZZ, factorial(n)) * 0], [identity_matrix(ZZ, factorial(n))]])

    def iso(k, n):
        return block_matrix([[iota(k, n), copi(k, n)]])

    def FJ_derivative_law(x, f, y):
        topid = [] + (d + 1) * [d] + [d + 1]
        m = CatMat.identity_matrix(ZZ, D, topid)
        o = CatMat.from_string(ZZ, C, [x], '[[' + f + ']]', [y])
        mo = CatMat.kronecker_product(';', m.transpose(), o)
        zm = iso(y, d + 1).inverse() * Xi(mo).transpose() * iso(x, d + 1)
        dd = factorial(d + 1)
        a = solve_to_Xi(x + 1, zm.column(0)[:dd], y + 1)
        return res(a)

    return MatrixRepresentation(E, ZZ, FJ_derivative_law, target_cat=E)


# Should return a matrix representation of a divided power algebra
# but these haven't been implemented yet
def FJ_t(d):
    C, _, _ = FJ(d)
    def tmap(x, y):
        assert x <= y
        return CatMat.from_string(ZZ, C, [x],
                                  '[[t^' + str(y - x) + ''.join([chr(i + 97) for i in range(y)]) + ']]', [y])
    return tmap


def FJ_leading(d):
    C, _, _ = FJ(d)
    tmap = FJ_t(d)

    def leading_law(x, f, y):
        ff = CatMat.from_string(ZZ, C, [x], '[[' + f + ']]', [y])
        return tmap(x, d) >> (ff * tmap(y, d))

    return MatrixRepresentation(C, ZZ, leading_law, target_cat=C)


# The concatenation operation on FI induces
# a monoidal structure on FJ.  On objects,
# p * q = [p + q, p + q + 1, p + q + 2, ..., p + q + d]
def FJ_product(d):
    D, Xi, solve_to_Xi = FJ(d)
    DD = ProductCategory(';', D, D)
    C = FI()
    CC = ProductCategory(';', C, C)

    # Obtain an FI^op module from Xi(k) \boxtimes Xi(l)
    # by restricting along s^op (s = FI_decompositions)
    # Since the output is matrices, we follow the FI_flat convention
    # and keep them as matrix reps FI --> mat/ZZ
    def skl_rep(k, l):
        xik = FI_flat(k)
        xil = FI_flat(l)

        def outer_law(x, fg, y):
            f, g = CC.break_string(fg)
            return CatMat.kronecker_product(xik(x[0], f, y[0]), xil(x[1], g, y[1]))

        outer = MatrixRepresentation(CC, ZZ, outer_law)

        def law(x, f, y):
            return outer(FI_decompositions(x, f, y))

        return MatrixRepresentation(C, ZZ, law)

    def skl_basis(k, l, n):
        return [(p, q) for w in Subsets(n)
                for p in Permutations(w) for wc in [[ww for ww in range(1, n + 1) if ww not in w]]
                for q in Permutations(wc) if len(w) >= k and len(wc) >= l]

    # This iso goes to FI_flat(k + l + m)
    # The full iso would be the infinite sum of these blocks over m >= 0
    def iso_block(k, l, m, n):
        if n < k + l + m:
            return matrix(ZZ, 0, 0, [])
        rows = Permutations(n)
        cols = skl_basis(k, l, n)

        def entry(p, q, r):
            if p[k:] == [e for e in r[k + l: k + l + m] if e in p[k:]] \
                    and q[l:l + (m - len(p[k:]))] == [e for e in r[k + l: k + l + m] if e not in p[k:]] \
                    and p[:k] == r[:k] and q[:l] == r[k:k + l] and (list(p) + list(q))[k + l + m:] == r[k + l + m:]:
                if (m - len(p[k:])) % 2 == 0:
                    return 1
                return -1
            return 0

        return matrix(ZZ, len(rows), len(cols), [entry(p, q, r) for r in rows for p, q in cols]).transpose()

    def iso(k, l, n):
        return block_matrix([[iso_block(k, l, m, n) for m in range(n - k - l + 1)]])

    def upsum(kl, n):
        def law(x, f, y):
            return block_diagonal_matrix([FI_flat(kl + m)(x, f, y) for m in range(n - kl + 1)])

        return MatrixRepresentation(C, ZZ, law)

    # We need the natural transformations between skls
    # n is the degree in FI
    # and fg is a pair of FJ-morphisms
    def fjfj_action(n, x, fg, y):
        f, g = DD.break_string(fg)
        ff = CatMat.from_string(ZZ, D, [x[0]], '[[' + f + ']]', [y[0]])
        gg = CatMat.from_string(ZZ, D, [x[1]], '[[' + g + ']]', [y[1]])
        blocks = []
        for w in Subsets(n):
            idw = CatMat.identity_matrix(ZZ, C.op(), [len(w)])
            idwc = CatMat.identity_matrix(ZZ, C.op(), [n - len(w)])
            idwf = CatMat.kronecker_product(idw, ff)
            idwcg = CatMat.kronecker_product(idwc, gg)
            blocks += [CatMat.kronecker_product(Xi(idwf), Xi(idwcg))]
        return block_diagonal_matrix(blocks).transpose()

    def FJ_product_law(x, fg, y):
        xx = x[0] + x[1]
        yy = y[0] + y[1]
        if xx > d or yy > d:
            return CatMat.zero_matrix(ZZ, D, list(range(xx, d + 1)), list(range(yy, d + 1)))
        nat = iso(*y, d).inverse() * fjfj_action(d, x, fg, y) * iso(*x, d)
        df = factorial(d)
        tab = [[solve_to_Xi(i + xx, nat[df * j:df * j + df, df * i: df * i + 1].column(0), j + yy)
                for j in range(d + 1 - yy)] for i in range(d + 1 - xx)]
        return CatMat.block_matrix(tab)

    return MatrixRepresentation(DD, ZZ, FJ_product_law, target_cat=D)
