from FJ import *

# Calculate a pointwise, exact formula for the (zeroth) tail shift
# of a generic FJ-module.  Precomposing a pointwise FJ-module with
# the tail shift gives an FJ-module that appears as a summand of
# every large-enough shift.
def tail_shift(d):
    D, Xi, solve_to_Xi = FJ(d)
    fjp = FJ_product(d)
    id0 = CatMat.identity_matrix(ZZ, D, [0])
    def tail_shift_law(x, f, y):
        ff = CatMat.from_string(ZZ, D, [x], '[[' + f + ']]', [y])
        id0ff = CatMat.kronecker_product(';', id0, ff)
        return fjp(id0ff)

    return MatrixRepresentation(D, ZZ, tail_shift_law, target_cat=D)


# The identity functor seems to appear in the upper left, followed by zeros.
# This representation picks out the lower right block.
def tail_derivative(d):
    D , _, _ = FJ(d)
    Dm, _, _ = FJ(d - 1)
    ts = tail_shift(d)
    def tail_derivative_law(x, f, y):
        ff = CatMat.from_string(ZZ, Dm, [x], '[[' + f + ']]', [y])
        fff = FJ_lift_matrix(d, ff)
        m = ts(fff)
        entries = [e for i in range(d - x) for j in range(d - y) for e in m.entry_vector(i + 1, j + 1)]
        return CatMat(ZZ, D, m.source[1:], vector(ZZ, entries), m.target[1:])

    return MatrixRepresentation(Dm, ZZ, tail_derivative_law, target_cat=D)

d = 3
D, Xi, solve_to_Xi = FJ(d)
nts = tail_shift(d)
for x in D.objects:
    for y in D.objects:
        for f in D.hom(x, y):
            print(x, f, y)
            nts(x, f, y).pp()
            print()

print('next round')
Dm, _, _ = FJ(d - 1)
ntd = tail_derivative(d)
ntsm = tail_shift(d - 1)
for x in Dm.objects:
    for y in Dm.objects:
        for f in Dm.hom(x, y):
            print(x, f, y)
            ntd(ntsm(x, f, y)).pp()
            print()

for x, y, z in itertools.product(D.objects, D.objects, D.objects):
    for f in D.hom(x, y):
        ff = CatMat.from_string(ZZ, D, [x], '[[' + f + ']]', [y])
        for g in D.hom(y, z):
            gg = CatMat.from_string(ZZ, D, [y], '[[' + g + ']]', [z])
            print(x, f, y, g, z)
            assert nts(ff) * nts(gg) == nts(ff * gg)
            print('pass')
            print()
