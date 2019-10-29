from FJ import *

d = 2
D, Xi, solve_to_Xi = FJ(d)
C = FI(range(d + 1))

m = CatMat.from_string(ZZ, C, [2, 1, 0], '[[ab-ba],[b+8a],[*]]', [2])
for i in range(8):
    print(m.coker_at(i))


def I_one(x):
    return '*'


def I_hom(x, y):
    return ['*'] if x <= y else []


def I_comp(x, f, y, g, z):
    return '*'


I = FiniteCategory([0, 1], I_one, I_hom, I_comp)
IxFJ = ProductCategory(';', I, D)

def law(xa, ff, yb):
    _, f = IxFJ.break_string(ff)
    x, a = xa
    y, b = yb
    fi_mat = \
        {(0, 0): CatMat.identity_matrix(ZZ, C, m.target),
         (0, 1): m,
         (1, 1): CatMat.identity_matrix(ZZ, C, m.source)}[x, y]
    fj_mat = CatMat.from_string(ZZ, D, [a], '[[' + f + ']]', [b])
    return Xi(CatMat.kronecker_product(fi_mat.transpose(), fj_mat))


m_rep = MatrixRepresentation(IxFJ, ZZ, law)
pres = m_rep.presentation()
v = [e for i, (x, a) in enumerate(pres.source)
       for j, (y, b) in enumerate(pres.target) for e in pres.entry_vector(i, j) if x == 1 and y == 1]
rows = [a for x, a in pres.source if x == 1]
cols = [b for y, b in pres.target if y == 1]
mm = CatMat(ZZ, D, rows, v, cols)




print()
for i in range(d + 1):
    print(i, mm.coker_at(i))

print()
mm.pp()


# Suppose a, b are CatMats over products with the same second factor
def hom_coker_coker(a, b):
    c = +b
    f0 = CatMat.identity_matrix(ZZ, a.cat, a.source)
    f1 = CatMat.identity_matrix(ZZ, a.cat, a.target)
    g0 = CatMat.identity_matrix(ZZ, b.cat, b.source)
    g1 = CatMat.identity_matrix(ZZ, b.cat, c.source)
    bf0 = CatMat.kronecker_product(';', b.transpose(), f0)
    g1a = CatMat.kronecker_product(';', g1.transpose(), a)
    cf1 = CatMat.kronecker_product(';', c.transpose(), f1)
    g0a = CatMat.kronecker_product(';', g0.transpose(), a)
    bf1 = CatMat.kronecker_product(';', b.transpose(), f1)
    d0 = CatMat.block_matrix([[bf0, g1a], [0, (-1) * cf1]])
    d1 = CatMat.block_matrix([[g0a], [(-1) * bf1]])
    def bimod_law(xxxx, ffff, yyyy):
        (p, q), (r, s) = xxxx
        (t, u), (v, w) = yyyy
        aa, bb = bf0.cat.break_string(ffff)
        ee, ff = b.cat.break_string(aa)
        gg, hh = a.cat.break_string(bb)
        emat = CatMat.from_string(ZZ, b.cat.cats[0], [t], '[[' + ee + ']]', [p])
        fmat = CatMat.from_string(ZZ, b.cat.cats[1], [u], '[[' + ff + ']]', [q])
        gmat = CatMat.from_string(ZZ, a.cat.cats[0], [r], '[[' + gg + ']]', [v])
        hmat = CatMat.from_string(ZZ, a.cat.cats[1], [s], '[[' + hh + ']]', [w])
        hom_bimod = a.cat.cats[1].hom_bimodule()
        mid = hom_bimod(CatMat.kronecker_product(';', fmat.transpose(), hmat))
        return CatMat.kronecker_product('$', emat.transpose(), mid, gmat)
    pc = ProductCategory('$', b.cat.cats[0].op(), a.cat.cats[0])
    bimod = MatrixRepresentation(bf0.cat, ZZ, bimod_law, target_cat=pc)
    return bimod(d0), bimod(d1)


def free_tail(k):
    S = FI([k])
    SopxD = ProductCategory('#', S.op(), D)
    def free_tail_law(px, ef, qy):
        p, x = px
        q, y = qy
        e, f = SopxD.break_string(ef)
        ee = CatMat.from_string(ZZ, S, [q], '[[' + e + ']]', [p])
        ff = CatMat.from_string(ZZ, D, [x], '[[' + f + ']]', [y])
        kf = CatMat.kronecker_product(';', ee.transpose(), ff)
        return Xi(kf)
    return MatrixRepresentation(SopxD, ZZ, free_tail_law)



mmm = CatMat.kronecker_product('&', CatMat.from_string(ZZ, TerminalCategory, ['*'], '[[*]]', ['*']), mm)


pC = ProductCategory('$', TerminalCategory.op(), C)
def proj_law(xp, fg, yq):
    _, p = xp
    _, q = yq
    _, g = pC.break_string(fg)
    return CatMat.from_string(ZZ, C, [p], '[[' + g + ']]', [q])


proj = MatrixRepresentation(pC, ZZ, proj_law, target_cat=C)

# Compute tail hom (i,-) --> coker m
#
for i in range(d + 1):
    ft = free_tail(i).presentation()
    d0, d1 = hom_coker_coker(ft, mmm)
    print()
    #dd0 = CatMat(ZZ, C, [x[1] for x in d0.source], d0.data_vector, [y[1] for y in d0.target])
    #dd1 = CatMat(ZZ, C, [x[1] for x in d1.source], d1.data_vector, [y[1] for y in d1.target])
    dd0 = proj(d0)
    dd1 = proj(d1)
    cf = C.cofree_module(ZZ, [i])
    ch = ChainComplex({-1: cf(dd0).transpose(), 0: cf(dd1).transpose()})
    print(ch.homology(0))
    dd0.pp()
    dd1.pp()
    (+dd0).pp()




