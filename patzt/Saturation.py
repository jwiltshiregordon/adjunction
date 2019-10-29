from FJ import *

d = 2
D, Xi, solve_to_Xi = FJ(d)
C = FI()

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


def hom_coker_coker(a, b):
    cat = a.cat
    c = +b
    f0 = CatMat.identity_matrix(ZZ, cat, a.source)
    f1 = CatMat.identity_matrix(ZZ, cat, a.target)
    g0 = CatMat.identity_matrix(ZZ, cat, b.source)
    g1 = CatMat.identity_matrix(ZZ, cat, c.source)
    bf0 = CatMat.kronecker_product(';', b.transpose(), f0)
    g1a = CatMat.kronecker_product(';', g1.transpose(), a)
    cf1 = CatMat.kronecker_product(';', c.transpose(), f1)
    g0a = CatMat.kronecker_product(';', g0.transpose(), a)
    bf1 = CatMat.kronecker_product(';', b.transpose(), f1)
    d0 = CatMat.block_matrix([[bf0, g1a], [0, (-1) * cf1]])
    d1 = CatMat.block_matrix([[g0a], [(-1) * bf1]])
    bimod = cat.hom_bimodule()
    return ChainComplex({-1: bimod(d0).transpose(), 0: bimod(d1).transpose()}).homology(0)


def free_tail(k):
    idk = CatMat.identity_matrix(ZZ, C, [k]).transpose()
    def free_tail_law(x, f, y):
        ff = CatMat.from_string(ZZ, D, [x], '[[' + f + ']]', [y])
        kf = CatMat.kronecker_product(';', idk, ff)
        return Xi(kf)
    return MatrixRepresentation(D, ZZ, free_tail_law)



# Compute tail hom (i,-) --> coker m
#
for i in range(d + 1):
    ft = free_tail(i).presentation()
    print(i, hom_coker_coker(ft, mm))

