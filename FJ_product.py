from FJ import *

# The concatenation operation on FI induces
# a monoidal structure on FJ.  On objects,
# p * q = [p + q, p + q + 1, p + q + 2, ..., p + q + d]

d = 2
D, Xi, solve_to_Xi = FJ(d)
DD = ProductCategory(';', D, D)
C = FI()
CC = ProductCategory(';', C, C)



s = FI_decompositions

# Obtain an FI^op module from Xi(k) \boxtimes Xi(l)
# by restricting along s^op
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
        return outer(s(x, f, y))

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


# k, l = 0, 0
# x, y = 4, 4
#
# us = upsum(k + l, max(x, y))
# skl = skl_rep(k, l)
#
# for f in C.hom(x, y):
#     print(f)
#     assert skl(x, f, y) * iso(k, l, y) == iso(k, l, x) * us(x, f, y)
#     print('pass')

k, l = 0, 0
x, f, y = 2, 'cb', 3
us = upsum(k + l, max(x, y))
skl = skl_rep(k, l)

print()
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


# x, f, y = 2, 'cb', 3
# for fg in DD.hom((0, 0), (0, 1)):
#     mod0 = skl_rep(0, 0)
#     mod1 = skl_rep(0, 1)
#     print(fg)
#     assert fjfj_action(x, (0, 0), fg, (0, 1)) * mod0(x, f, y) == mod1(x, f, y) * fjfj_action(y, (0, 0), fg, (0, 1))
#     print('pass')


def FJ_product_law(x, fg, y):
    xx = x[0] + x[1]
    yy = y[0] + y[1]
    if xx > d or yy > d:
        return CatMat.zero_matrix(ZZ, D, list(range(xx, d + 1)), list(range(yy, d + 1)))
    nat = iso(*y, d).inverse() * fjfj_action(d, x, fg, y) * iso(*x, d)
    df = factorial(d)
    tab = [[solve_to_Xi(i + xx, nat[df * j:df * j + df, df * i : df * i + 1].column(0), j + yy)
            for j in range(d + 1 - yy)] for i in range(d + 1 - xx)]
    return CatMat.block_matrix(tab)


FJ_product = MatrixRepresentation(DD, ZZ, FJ_product_law, target_cat=D)

print()
for x in DD.objects:
    for y in DD.objects:
        for z in DD.objects:
            for f in DD.hom(x, y):
                for g in DD.hom(y, z):
                    fm = FJ_product(x, f, y)
                    gm = FJ_product(y, g, z)
                    ff = CatMat.from_string(ZZ, DD, [x], '[[' + f + ']]', [y])
                    gg = CatMat.from_string(ZZ, DD, [y], '[[' + g + ']]', [z])
                    fgm = FJ_product(ff * gg)
                    print(x, f, y, g, z)
                    assert fm * gm == fgm
                    print()
                    fgm.pp()
                    print()
                    print('pass')
                    print()
                    print()



