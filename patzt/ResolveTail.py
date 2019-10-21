from FJ import *

# Gives a functorial rightward tail-resolution by free FI-modules
# The resolution is infinite

d = 2
D, _, _ = FJ(d)

print('resolve tail')

# First build Sigma X --> Djk X
# then check that the homology vanishes at 2
# then build double complex model of j^! j_! and check that it has the same homology
# Build the adjunction unit 1 --> j^! j_!
# Then take the mapping cone of the inclusion of jk into Djk to get a model for the original cx


der = FJ_derivative(d)
sigma = FJ_leading(d)
shift = FJ_shift(d)
sha = FJ_t(d)


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

for i in range(d + 1):
    connecting(i).pp()
    print()










