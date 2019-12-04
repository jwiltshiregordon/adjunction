from FJ import *

d = 3
D, Xi, solve_to_Xi = FJ(d)
C = FI(range(d + 1))

m = CatMat.from_string(ZZ, C, [2, 1, 0], '[[ab-ba],[b+8a],[*]]', [2])
for i in range(8):
    print(m.coker_at(i))


# This code computes a functorial resolution of a pointwise FJ-module
# by semi-induced FJ-modules that are also given pointwise.
#
# The key lemma: any FJ-module injects into its zeroth tail shift
# (If M is an FI-module, and W is its corresponding FJ-module,
# the zeroth tail shift of W is M(- \sqcup -) \otimes (\Xi(0) \boxtimes -).
# In other words, the zeroth tail shift appears with multiplicity 1
# inside all high-enough shifts of M)
#
# Repeatedly inject the tail derivative into the tail shift.
def id_law(x, f, y):
    return CatMat.from_string(ZZ, D, [x], '[[' + f + ']]', [y])

id = MatrixRepresentation(D, ZZ, id_law, target_cat=D)

def resuptd(d, rep):
    D,  _, _ = FJ(d)
    Dm, _, _ = FJ(d - 1)
    td = tail_derivative(d)
    def law(x, f, y):
        ff = CatMat.from_string(ZZ, D, [x], '[[' + f + ']]', [y])
        return rep(td(ff))
    return MatrixRepresentation(Dm, ZZ, law, target_cat=rep.target_cat)


def resupts(d, rep):
    D,  _, _ = FJ(d)
    ts = tail_shift(d)
    def law(x, f, y):
        ff = CatMat.from_string(ZZ, D, [x], '[[' + f + ']]', [y])
        return rep(ts(ff))
    return MatrixRepresentation(D, ZZ, law, target_cat=rep.target_cat)

print()
print('Original')
rs = resupts(d, id)
for x in rs.cat.objects:
    for y in rs.cat.objects:
        for f in rs.cat.hom(x, y):
            print(x, f, y)
            print()
            rs(x, f, y).pp()
            print()
            print()

print()
print('First')
rs = resupts(d - 1, resuptd(d, id))
for x in rs.cat.objects:
    for y in rs.cat.objects:
        for f in rs.cat.hom(x, y):
            print(x, f, y)
            print()
            rs(x, f, y).pp()
            print()
            print()

print()
print('Second')
rs = resupts(d - 2, resuptd(d - 1, resuptd(d, id)))
for x in rs.cat.objects:
    for y in rs.cat.objects:
        for f in rs.cat.hom(x, y):
            print(x, f, y)
            print()
            rs(x, f, y).pp()
            print()
            print()