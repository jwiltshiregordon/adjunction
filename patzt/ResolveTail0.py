from FJ import *

# Gives a functorial rightward tail-resolution by free FI-modules
# The resolution is infinite

d = 2
D, Xi, _ = FJ(d)
C, _, _ = FJ(d - 1)
CopxD = ProductCategory(';', C.op(), D)
E = FI()

print('resolve tail')

# First build Sigma X --> Djk X
# then check that the homology vanishes at 2
# then build double complex model of j^! j_! and check that it has the same homology
# Build the adjunction unit 1 --> j^! j_!
# Then take the mapping cone of the inclusion of jk into Djk to get a model for the original cx

res = FJ_restrict(d, d - 1)
der = FJ_derivative(d)
sigma = FJ_leading(d)
shift = FJ_shift(d)
sha = FJ_t(d)

for x, y in itertools.product(range(d + 1), range(d + 1)):
    for f in D.hom(x, y):
        print(x, f, y)
        ff = CatMat.from_string(ZZ, D, [x], '[[' + f + ']]', [y])
        print()
        shift(shift(shift(ff))).pp()
        print()





def free_tail(k):
    idk = CatMat.identity_matrix(ZZ, E, [k]).transpose()
    def free_tail_law(x, f, y):
        ff = CatMat.from_string(ZZ, D, [x], '[[' + f + ']]', [y])
        kf = CatMat.kronecker_product(';', idk, ff)
        return Xi(kf)
    return MatrixRepresentation(D, ZZ, free_tail_law)


ft = free_tail(0).presentation()
print()
m0 = shift(shift(shift(ft)))
ft = free_tail(1).presentation()
print()
m1 = shift(shift(shift(ft)))
ft = free_tail(2).presentation()
print()
m2 = shift(shift(shift(ft)))

m0_row_string0 = '[[t^0ab,0,0,0,0,0,0],[-t^0ab,t^0ab,0,0,0,0,0],[t^1ba,0,t^0a,0,0,0,0],[-t^0ba,0,0,t^0ba,0,0,0],[t^1ba,0,0,0,t^0a,0,0],[t^1ba,0,0,0,0,t^0a,0],[-t^2ba,0,0,0,0,0,t^0]]'
m0_row_string1 = '[[t^0ab,0,0,t^0ba,0,0,0],[0,t^0ab,0,0,0,0,0],[0,0,t^0a,0,0,0,0],[0,0,0,t^0ab,0,0,0],[0,0,0,t^1ab,t^0a,0,0],[0,0,0,t^1ab,0,t^0a,0],[0,0,0,-t^2ab,0,0,t^0]]'
m0_row_string2 = '[[t^0ab,t^0ba,0,0,0,0,0],[0,t^0ab,0,0,0,0,0],[0,t^1ba,t^0a,0,0,0,0],[0,t^0ab-t^0ba,0,t^0ab,0,0,0],[0,0,0,0,t^0a,0,0],[0,t^1ab,0,0,0,t^0a,0],[0,-t^2ab,0,0,0,0,t^0]]'
m0_row_string3 = '[[t^0ab,0,0,0,0,0,0],[0,t^0ab,0,0,0,0,0],[0,0,t^0a,0,0,0,0],[0,0,0,t^0ab,0,0,0],[0,0,0,0,t^0a,0,0],[0,0,0,0,0,t^0a,0],[0,0,0,0,0,0,t^0]]'
m0_row_string4 = '[[t^0ab,0,0,0,0,0,0],[0,t^0ab,0,0,0,0,0],[0,0,t^0a,0,0,0,0],[0,0,0,t^0ab,0,0,0],[0,0,0,0,t^0a,0,0],[0,0,0,0,0,t^0a,0],[0,0,0,0,0,0,t^0]]'


m0_row0 = CatMat.from_string(ZZ, D, [2, 2, 1, 2, 1, 1, 0], m0_row_string0, [2, 2, 1, 2, 1, 1, 0])
m0_row1 = CatMat.from_string(ZZ, D, [2, 2, 1, 2, 1, 1, 0], m0_row_string1, [2, 2, 1, 2, 1, 1, 0])
m0_row2 = CatMat.from_string(ZZ, D, [2, 2, 1, 2, 1, 1, 0], m0_row_string2, [2, 2, 1, 2, 1, 1, 0])


(m0_row2 * m0_row1 * m0_row0 * m0).pp()


sys.exit(0)
def Djk_law(x, f, y):
    return CatMat.block_matrix([[der(x, f, y), 0], [0, sigma(x, f, y)]])

Djk = MatrixRepresentation(D, ZZ, Djk_law, target_cat=D)



connecting_dict = dict()
def connecting(p):
    if p in connecting_dict:
        return connecting_dict[p]
    jk = shift(sha(p, d))
    if p == d:
        return jk
    idcol = CatMat.identity_matrix(ZZ, D, [p + 1, p]).column(0)
    ret = CatMat.block_matrix([[idcol, jk]])
    connecting_dict[p] = ret
    return ret

# They look like [[1, -tt((p+1)-cycle)],[0, tt]] but I'm not sure why that would be

for i in range(d + 1):
    connecting(i).pp()
    print()



for x, y in itertools.product(range(d + 1), range(d + 1)):
    for f in D.hom(x, y):
        print(x, f, y)
        print()
        assert shift(x, f, y) * connecting(y) == connecting(x) * Djk(x, f, y)
        print()





# Build the model Sigma ---> Djk
# where Sigma is in degree zero
def model_f_law(dd, x, f, y):
    if dd == (0,):
        return shift(x, f, y)
    if dd == (1,):
        return Djk(x, f, y)
    return CatMat.zero_matrix(ZZ, D, [], [])

def model_d_law(p, dd):
    if dd == (-1,):
        return CatMat.zero_matrix(ZZ, D, [], shift.rank(p))
    if dd == (0,):
        return connecting(p)
    if dd == (1,):
        return CatMat.zero_matrix(ZZ, D, shift.rank(p), [])
    return CatMat.zero_matrix(ZZ, D, [], [])

dg_model = dgModule(D, ZZ, model_f_law, [model_d_law], target_cat=D)



Chom = C.hom_bimodule()

def x_resy_law(ab, fg, cd):
    a, b = ab
    c, d = cd
    f, g = CopxD.break_string(fg)
    ff = CatMat.from_string(ZZ, C.op(), [a], '[[' + f + ']]', [c])
    gg = CatMat.from_string(ZZ, D, [b], '[[' + g + ']]', [d])
    return Chom(CatMat.kronecker_product(ff, res(gg)))


x_resy = MatrixRepresentation(CopxD, ZZ, x_resy_law, target_cat=None)
ch = x_resy.resolution()



# Apply shift to the factor of D in CopxD
def apply_shift(ab, fg, pq):
    a, b = ab
    p, q = pq
    f, g = CopxD.break_string(fg)
    ff = CatMat.from_string(ZZ, C.op(), [a], '[[' + f + ']]', [p])
    return CatMat.kronecker_product(';', ff, shift(b, g, q))


ap = MatrixRepresentation(CopxD, ZZ, apply_shift, target_cat=CopxD)


# Apply shift to the factor of D in CopxD
def apply_Djk(ab, fg, pq):
    a, b = ab
    p, q = pq
    f, g = CopxD.break_string(fg)
    ff = CatMat.from_string(ZZ, C.op(), [a], '[[' + f + ']]', [p])
    return CatMat.kronecker_product(';', ff, Djk(b, g, q))


adjk = MatrixRepresentation(CopxD, ZZ, apply_Djk, target_cat=CopxD)


ch.differential('*', (0,)).pp()
chap = ch.apply_matrix_rep(ap)
chadjk = ch.apply_matrix_rep(adjk)
print()
chap.differential('*', (0,)).pp()
print()
chadjk.differential('*', (0,)).pp()

print()


def chcon(p):
    blks = []
    for a, b in ch.differential('*', (p,)).source:
        o = CatMat.identity_matrix(ZZ, C, [a]).transpose()
        m = connecting(b)
        blks += [CatMat.kronecker_product(';', o, m)]
    return CatMat.block_diagonal(blks)


def sgn(k):
    return 1 if k % 2 == 0 else -1


def remainder(k):
    return CatMat.block_matrix([[chap.differential('*', (k,)), sgn(k) * chcon(k)],
                                [0, chadjk.differential('*', (k - 1,))]])



print()
(remainder(0) * remainder(1)).pp()
print()
(remainder(1) * remainder(2)).pp()
print()
remainder(0).pp()
print()
remainder(1).pp()
print()
remainder(2).pp()
print(remainder(0))
print(remainder(1))
print(remainder(2))



M = D.free_module((0, 1))
E = C.cofree_module((1,))


def test_law(ab, fg, pq):
    a, b = ab
    p, q = pq
    f, g = CopxD.break_string(fg)
    ff = CatMat.from_string(ZZ, C.op(), [a], '[[' + f + ']]', [p])
    gg = CatMat.from_string(ZZ, D, [b], '[[' + g + ']]', [q])
    return CatMat.kronecker_product(E(ff.transpose()).transpose(), M(gg))


test_rep = MatrixRepresentation(CopxD, ZZ, test_law, target_cat=None)




cx = ChainComplex({k: test_rep(remainder(k)).transpose() for k in range(3)})
print(cx)
print(cx.homology(0))
print(cx.homology(1))
print(cx.homology(2))
print(cx.homology(3))