from RepresentationStabilityCategories import *
from FJ import *

d = 3
C, Xi, solve_to_Xi = FJ(d)
D = FI()

def plus_one_law(x, f, y):
    sf = ''.join(chr(ord(c) + 1) for c in f)
    return x + 1, 'a' + sf, y + 1

PlusOne = Functor(D, plus_one_law, D)


def I(n):
    if n == 0:
        return [(0, '*', 1)]
    bcde = ''.join([chr(i + 98) for i in range(n)])
    return [(n, bcde[:r] + 'a' + bcde[r:-1], n) for r in range(n)] + [(n, bcde, n + 1)]
    #matrix_string = '[[' + ', '.join([bcde[:r] + 'a' + bcde[r:-1] for r in range(n)] + [bcde]) + ']]'
    #return CatMat.from_string(ZZ, D, [n], matrix_string, ([n] * n) + [n + 1])


def h(x, f, y):
    if 'a' in f:
        return I(x)[f.index('a')]
    return I(x)[x]


def g(x, f, y):
    fl = ''.join([chr(ord(c) - 1) for c in f])
    if 'a' in f:
        r = f.index('a')
        return x - 1, fl[:r] + fl[r + 1:], y - 1
    return x, fl, y - 1


# x, y = 2, 5
# for f in D.hom(x, y):
#     a, b, c = h(x, f, y)
#     p, q, r = plus_one_law(*g(x, f, y))
#     assert x == a and c == p and y == r
#     assert D.compose(a, b, c, q, r) == f
#
#
# print 'Passed checks for g, h'



def J(n):
    id = D.identity(n)
    return [(n, id[r] + id[:r] + id[r+1:], n) for r in range(n)]


def e(x, f, y):
    id = D.identity(y)
    r = id.index(f[0])
    return J(y)[r]

def ff(x, f, y):
    id = D.identity(y)
    r = id.index(f[0])
    return x - 1, ''.join([c if ord(c) < r + 97 else chr(ord(c) - 1) for c in f[1:]]), y - 1


# x, y = 2, 5
# for f in D.hom(x, y):
#     a, b, c = plus_one_law(*ff(x, f, y))
#     p, q, r = e(x, f, y)
#     assert x == a and c == p and y == r
#     assert D.compose(a, b, c, q, r) == f
#
# print 'Passed checks for e, ff'


def F_law(x, f, y):
    rows = I(x)
    cols = I(y)
    matrix_string = '[' + ', '.join(['[' + ', '.join([g(x, fj, b)[1] if h(x, fj, b) == (x, i, a) else '0'
             for _, j, b in cols for fj in [D.compose(x, f, y, j, b)]]) + ']' for _, i, a in rows]) + ']'
    return CatMat.from_string(ZZ, D, [r[2] - 1 for r in rows], matrix_string, [c[2] - 1 for c in cols])


# x, y, z = 2, 3, 4
# for f in D.hom(x, y):
#     for gg in D.hom(y, z):
#         assert (F_law(x, f, y) * F_law(y, gg, z) == F_law(x, D.compose(x, f, y, gg, z), z))
#
# print 'F passes functoriality checks'


def G_law(x, f, y):
    rows = J(x)
    cols = J(y)
    matrix_string = '[' + ', '.join(['[' + ', '.join([ff(a, pf, y)[1] if e(a, pf, y) == (b, q, y) else '0'
            for b, q, _ in cols for pf in [D.compose(a, p, x, f, y)]]) + ']' for a, p, _ in rows]) + ']'
    return CatMat.from_string(ZZ, D, [r[0] - 1 for r in rows], matrix_string, [c[0] - 1 for c in cols])


# x, y, z = 2, 3, 4
# for f in D.hom(x, y):
#     for gg in D.hom(y, z):
#         assert (G_law(x, f, y) * G_law(y, gg, z) == G_law(x, D.compose(x, f, y, gg, z), z))
#
# print 'G passes functoriality checks'
# print

x, f, y = 2, 'dc', 4
F_law(x, f, y).pp()
print
G_law(x, f, y).pp()
print


def pi(n):
    return block_matrix([[identity_matrix(ZZ, factorial(n)), identity_matrix(ZZ, factorial(n)) * 0]])


def copi(k, n):
    if k == n:
        return identity_matrix(ZZ, factorial(d))
    if k > n:
        return matrix(ZZ, 0, 0, [])
    return block_matrix([[identity_matrix(ZZ, factorial(n)) * 0], [identity_matrix(ZZ, factorial(n))]])


def iota(k, n):
    if k == n:
        return zero_matrix(ZZ, factorial(d), 0)
    if k > n:
        return matrix(ZZ, 0, 0, [])
    return block_matrix([[identity_matrix(ZZ, factorial(n))], [
        -matrix(ZZ, factorial(n), factorial(n), [1 if r[k] == c[0] and c[1:] == r[:k] + r[k + 1:] else 0
                                                for r in Permutations(range(n)) for c in Permutations(range(n))])]])

# k = 1
# x, y = 2, 4
# for f in D.hom(x, y):
#     assert pi(x) * FI_flat(k)(F_law(x, f, y)) == FI_flat(k)(G_law(x, f, y)) * pi(y)
#
# print 'pi passes naturality checks'
#
# k = 0
# x, y = 2, 4
# for f in D.hom(x, y):
#     assert iota(k, x) * FI_flat(k)(G_law(x, f, y)) == FI_flat(k)(F_law(x, f, y)) * iota(k, y)
#
# print 'iota passes naturality checks'

print(FI_flat(2)(2, 'bc', 3))
print(FI_flat(2)(2, 'ac', 3))
print(FI_flat(2)(2, 'ab', 3))




# Gives the FI^op isomorphism F^* Xi(k) <----- G^* Xi(k) + Xi(k)
def iso(k, n):
    return block_matrix([[iota(k, n), copi(k, n)]])




print

print
x, y = 2, 4
l = 0
for f in D.hom(x, y):
    assert FI_flat(l)(F_law(x, f, y)) * iso(l, y) == iso(l, x) * block_diagonal_matrix([FI_flat(l)(G_law(x, f, y)), FI_flat(l)(x, f, y)])
    assert FI_flat(l)(F_law(x, f, y)) * iso(l, y) == iso(l, x) * block_diagonal_matrix(
        [FI_flat(l + 1)(x, f, y), FI_flat(l)(x, f, y)])
    print(f + ' passed')



def FJ_shift_law(x, f, y):
    topid = [] + d * [d - 1] + [d]
    m = CatMat.identity_matrix(ZZ, D, topid)
    o = CatMat.from_string(ZZ, C, [x], '[[' + f + ']]', [y])
    mo = CatMat.kronecker_product(';', m.transpose(), o)
    zm = iso(y, d).inverse() * Xi(mo).transpose() * iso(x, d)
    dd = factorial(d)
    a = solve_to_Xi(x + 1, zm.column(0)[:dd], y + 1)
    b = solve_to_Xi(x + 1, zm.column(0)[dd:], y)
    c = solve_to_Xi(x, zm.column(dd)[dd:], y)
    ret = CatMat.block_matrix([[a, b], [0, c]])
    return ret


FJ_shift = MatrixRepresentation(C, ZZ, FJ_shift_law, target_cat=C)

def FJ_derivative_law(x, f, y):
    topid = [] + d * [d - 1] + [d]
    m = CatMat.identity_matrix(ZZ, D, topid)
    o = CatMat.from_string(ZZ, C, [x], '[[' + f + ']]', [y])
    mo = CatMat.kronecker_product(';', m.transpose(), o)
    zm = iso(y, d).inverse() * Xi(mo).transpose() * iso(x, d)
    dd = factorial(d)
    return solve_to_Xi(x + 1, zm.column(0)[:dd], y + 1) # This was called "a" in FJ_shift


FJ_derivative = MatrixRepresentation(C, ZZ, FJ_derivative_law, target_cat=C)
