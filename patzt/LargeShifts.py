from FJ import *

D = FI()
C = ProductCategory(';', D, D)

# This is the left adjoint to concatenation
decomp = FI_decompositions

def tail_shift(k):
    flat = FI_flat(k)
    def apply_flat_law(xp, fg, yq):
        x, p = xp
        f, g = C.break_string(fg)
        y, q = yq
        ff = CatMat.from_string(ZZ, D, [x], '[[' + f + ']]', [y])
        return CatMat.kronecker_product(ff, flat(p, g, q))


    apply_flat = MatrixRepresentation(C, ZZ, apply_flat_law, target_cat=D)

    def tail_shift_law(x, f, y):
        return apply_flat(decomp(x, f, y))


    return MatrixRepresentation(D, ZZ, tail_shift_law, target_cat=D)


m = CatMat.from_string(ZZ, D, [2, 1, 0], '[[ab-ba],[b+8a],[*]]', [2])



m.pp()
print()


print(m.coker_at(5))

for i in range(3):
    tsh = tail_shift(i)
    tshm = tsh(m)
    print(i, tshm.coker_at(0))










sys.exit(0)
D = FI([0, 1, 2, 3])
C = ProductCategory(';', D, D)


def concat_law(xx, ff, yy):
    x1, x2 = xx
    f1, f2 = C.break_string(ff)
    y1, y2 = yy
    f1 = '' if f1 == '*' else f1
    f2 = '' if f2 == '*' else f2
    f1f2 = '*' if f1 + f2 == '' else f1 + ''.join([chr(ord(v) + y1) for v in f2])
    return CatMat.from_string(ZZ, D, [x1 + x2], '[[' + f1f2 + ']]', [y1 + y2])

concat = MatrixRepresentation(C, ZZ, concat_law, target_cat=D)


ssi = {}
def subsum_indexing(x):
    if x in ssi:
        return ssi[x]
    u = range(x)
    ret = [([i for i in u if i in s], [i for i in u if i not in s]) for s in Subsets(u)]
    ssi[x] = ret
    return ret




def subsum(x):
    return [(len(s), len(t)) for s, t in subsum_indexing(x)]


def subsum_unit(x):
    if x == 0:
        return CatMat.from_string(ZZ, D, [0], '[[*]]', [0])
    idx = D.identity(x)
    ind = subsum_indexing(x)
    entries = ','.join([''.join([idx[st.index(i)] for i in range(x)]) for s, t in ind for st in [s + t]])
    return CatMat.from_string(ZZ, D, [x], '[[' + entries + ']]', [x] * len(ind))


# Now we solve for the left adjoint
#
#

def subsum_law(x, f, y):
    sx = subsum(x)
    sxu = subsum_unit(x)
    sy = subsum(y)
    syu = subsum_unit(y)
    n = len(CatMat.zero_matrix(ZZ, C, sx, sy).data_vector)
    mm = matrix([(sxu * concat(CatMat(ZZ, C, sx, v, sy))).data_vector for v in identity_matrix(ZZ, n).rows()])
    ff = CatMat.from_string(ZZ, D, [x], '[[' + f + ']]', [y])
    w = (ff * syu).data_vector
    u = CatMat.matrix_solve_right(mm.transpose(), matrix(ZZ, len(w), 1, w)).transpose()
    return CatMat(ZZ, C, sx, u.row(0), sy)


decompositions = MatrixRepresentation(D, ZZ, subsum_law, target_cat=C)

decompositions(1, 'b', 3).pp()
decompositions(3, 'acb', 3).pp()



dec = FI_decompositions

dec(1, 'b', 3).pp()

