from sage.all import *
from CatMat import *
from sage.all import vector, matrix, zero_matrix, identity_matrix, block_diagonal_matrix

# TODO: Do I still need any of this code?

def pos_one(x):
    return '*'

def pos_hom(x, y):
    if all([a in y for a in x]):
        return ['*']
    return []

def pos_comp(x, f, y, g, z):
    return '*'

# The three edges of the graph are called 0, 1, 2
# corresponding to the edges 12, 13, 23
# and this builds the poset of all subgraphs
object_list = [tuple(a) for a in Subsets([0, 1, 2])]
print object_list
pos = FiniteCategory(object_list, pos_one, pos_hom, pos_comp)
pt = FiniteCategory(['*'], pos_one, pos_hom, pos_comp)

print


def fsgn(s, t):
    if s.is_face(t):
        return (-1) ** (t.faces().index(s))
    return 0

def graphical_complement_dgModule(max_intersections, removals):
    X = SimplicialComplex([list(facet) for facet in max_intersections])
    def get_faces(x, d):
        omit = ''.join([removals[i] for i in x])
        return [f for f in X.n_faces(d) if all([(p not in omit) for p in f])]

    def f_law(dd, x, f, y):
        try:
            d = dd[0]
        except TypeError:
            d = dd
        source = get_faces(x, d)
        target = get_faces(y, d)
        return matrix(QQ, len(source), len(target), [(1 if s == t else 0) for s in source for t in target])

    def d_law(x, dd):
        try:
            d = dd[0]
        except TypeError:
            d = dd
        source = get_faces(x, d)
        target = get_faces(x, d + 1)
        return matrix(QQ, len(source), len(target), [fsgn(s, t) for s in source for t in target])

    return dgModule(pos, QQ, f_law, [d_law])



# Build the dgModules for various 3-point configuration spaces

cmr_facets = ['AEC', 'BDF', 'AHX', 'AHS', 'BHS', 'BHY', 'CHY', 'CHT', 'DHX', 'DHU', 'EHU', 'EHZ', 'FHT', 'FHZ',
          'BFSZ', 'AESZ', 'BDUY', 'CEUY', 'ACTX', 'DFTX']

cmr_removals = ['HUY', 'HSZ', 'HTX']

circle_mod_rotation = graphical_complement_dgModule(cmr_facets, cmr_removals)

lmt_facets = ['AGJM', 'BHJM', 'CHKM', 'DIKM', 'EILM', 'FGLM']
lmt_removals = ['HLM', 'GKM', 'IJM']

line_mod_translation = graphical_complement_dgModule(lmt_facets, lmt_removals)


# U(1)-equivariant complex plane
#
#                0                       2k+1                       2k+2
# {}             1                                                 z^(k+1)
# {12}           1                      w12*z^k                    z^(k+1)
# {13}           1                      w13*z^k                    z^(k+1)
# {23}           1                      w23*z^k                    z^(k+1)
# {12, 13}       1                 w12*z^k, w13*z^k            z^(k+1), w12*w13*z^k
# {12, 23}       1                 w12*z^k, w23*z^k            z^(k+1), w12*w23*z^k
# {13, 23}       1                 w13*z^k, w23*z^k            z^(k+1), w13*w23*z^k
# {12, 13, 23}   1             w12*z^k, w13*z^k, w23*z^k     z^(k+1), w12*w13*z^k, w12*w23*z^k
#
# The only tricky bit is the relation w12*w23 + w23*w31 + w31*w12 = 0
# or equivalently                     w12*w23 - w13*w23 - w12*w13 = 0
#                                                         w13*w23 = -w12*w13 + w12*w23
# which we use in the definition of f_law for the inclusion of {13, 23} into {12, 13, 23}
# Convention is that d(wij) = z not -z.

def cecp_d_law(x, dd):
    try:
        d = dd[0]
    except TypeError:
        d = dd
    if d <= -2:
        return matrix(QQ, 0, 0, [])
    if d == -1:
        return matrix(QQ, 0, 1, [])
    if len(x) == 0:
        if d == 0:
            return matrix(QQ, 1, 0, [])
        if d % 2 == 0:
            return matrix(QQ, 1, 0, [])
        else:
            return matrix(QQ, 0, 1, [])
    if len(x) == 1:
        if d == 0:
            return matrix(QQ, 1, 1, [0])
        if d % 2 == 0:
            return matrix(QQ, 1, 1, [0])
        else:
            return matrix(QQ, 1, 1, [1])
    if len(x) == 2:
        if d == 0:
            return matrix(QQ, 1, 2, [0, 0])
        if d % 2 == 0:
            return matrix(QQ, 2, 2, [0, 0, -1, 1])
        else:
            return matrix(QQ, 2, 2, [1, 0, 1, 0])
    if len(x) == 3:
        if d == 0:
            return matrix(QQ, 1, 3, [0, 0, 0])
        if d % 2 == 0:
            return matrix(QQ, 3, 3, [0, 0, 0, -1, 1, 0, -1, 0, 1])
        else:
            return matrix(QQ, 3, 3, [1, 0, 0, 1, 0, 0, 1, 0, 0])

even_inclusions = {tuple(): matrix(QQ, 1, 3, [1, 0, 0]),
                   (0,): matrix(QQ, 1, 3, [1, 0, 0]),
                   (1,): matrix(QQ, 1, 3, [1, 0, 0]),
                   (2,): matrix(QQ, 1, 3, [1, 0, 0]),
                   (0, 1): matrix(QQ, 2, 3, [1, 0, 0, 0, 1, 0]),
                   (0, 2): matrix(QQ, 2, 3, [1, 0, 0, 0, 0, 1]),
                   (1, 2): matrix(QQ, 2, 3, [1, 0, 0, 0, -1, 1]),
                   (0, 1, 2): identity_matrix(QQ, 3)}

odd_inclusions = {tuple(): matrix(QQ, 0, 3, []),
                   (0,): matrix(QQ, 1, 3, [1, 0, 0]),
                   (1,): matrix(QQ, 1, 3, [0, 1, 0]),
                   (2,): matrix(QQ, 1, 3, [0, 0, 1]),
                   (0, 1): matrix(QQ, 2, 3, [1, 0, 0, 0, 1, 0]),
                   (0, 2): matrix(QQ, 2, 3, [1, 0, 0, 0, 0, 1]),
                   (1, 2): matrix(QQ, 2, 3, [0, 1, 0, 0, 0, 1]),
                   (0, 1, 2): identity_matrix(QQ, 3)}


def cecp_f_law(dd, x, f, y):
    try:
        d = dd[0]
    except TypeError:
        d = dd
    if d < 0 :
        return matrix(QQ, 0, 0, [])
    if d == 0:
        return matrix(QQ, 1, 1, [1])
    if d % 2 == 0:
        return even_inclusions[y].solve_left(even_inclusions[x])
    else:
        return odd_inclusions[y].solve_left(odd_inclusions[x])

circle_equivariant_complex_plane = dgModule(pos, QQ, cecp_f_law, [cecp_d_law])

# Complex plane (without any group action)
#
#                0                       1                       2
# {}             1
# {12}           1                      w12
# {13}           1                      w13
# {23}           1                      w23
# {12, 13}       1                    w12, w13                w12*w13
# {12, 23}       1                    w12, w23                w12*w23
# {13, 23}       1                    w13, w23                w13*w23
# {12, 13, 23}   1                 w12, w13, w23          w12*w13, w12*w23
#
# The only tricky bit is the relation w12*w23 + w23*w31 + w31*w12 = 0
# or equivalently                     w12*w23 - w13*w23 - w12*w13 = 0
#                                                         w13*w23 = -w12*w13 + w12*w23
# which we use in the definition of f_law for the inclusion of {13, 23} into {12, 13, 23}
# The differential is identically zero.


def cp_d_law(x, dd):
    try:
        d = dd[0]
    except TypeError:
        d = dd
    if d == 0:
        return zero_matrix(QQ, 1, len(x))
    if d == 1:
        return zero_matrix(QQ, len(x), max(0, len(x) - 1))
    if d == 2:
        return zero_matrix(max(0, len(x) - 1), 0)
    if d >= 3:
        return zero_matrix(QQ, 0, 0)


deg1_inclusions = {tuple(): matrix(QQ, 0, 3, []),
                   (0,): matrix(QQ, 1, 3, [1, 0, 0]),
                   (1,): matrix(QQ, 1, 3, [0, 1, 0]),
                   (2,): matrix(QQ, 1, 3, [0, 0, 1]),
                   (0, 1): matrix(QQ, 2, 3, [1, 0, 0, 0, 1, 0]),
                   (0, 2): matrix(QQ, 2, 3, [1, 0, 0, 0, 0, 1]),
                   (1, 2): matrix(QQ, 2, 3, [0, 1, 0, 0, 0, 1]),
                   (0, 1, 2): identity_matrix(QQ, 3)}

deg2_inclusions = {tuple(): matrix(QQ, 0, 2, []),
                   (0,): matrix(QQ, 0, 2, []),
                   (1,): matrix(QQ, 0, 2, []),
                   (2,): matrix(QQ, 0, 2, []),
                   (0, 1): matrix(QQ, 1, 2, [1, 0]),
                   (0, 2): matrix(QQ, 1, 2, [0, 1]),
                   (1, 2): matrix(QQ, 1, 2, [-1, 1]),
                   (0, 1, 2): identity_matrix(QQ, 2)}

def cp_f_law(dd, x, f, y):
    try:
        d = dd[0]
    except TypeError:
        d = dd
    if d == 0:
        return matrix(QQ, 1, 1, [1])
    if d == 1:
        return deg1_inclusions[y].solve_left(deg1_inclusions[x])
    if d == 2:
        return deg2_inclusions[y].solve_left(deg2_inclusions[x])
    if d >= 3:
        return matrix(QQ, 0, 0, [])

complex_plane = dgModule(pos, QQ, cp_f_law, [cp_d_law])


# Ideal generated by z inside circle equivariant complex plane
def zcecp_d_law(x, dd):
    try:
        d = dd[0]
    except TypeError:
        d = dd
    return cecp_d_law(x, d - 2)

def zcecp_f_law(dd, x, f, y):
    try:
        d = dd[0]
    except TypeError:
        d = dd
    return cecp_f_law(d - 2, x, f, y)

z_circle_equivariant_complex_plane = dgModule(pos, QQ, zcecp_f_law, [zcecp_d_law])

# Is there an easy algorithm to find a q.i. dgModule that's much smaller?
# If you are willing to leave pointwise behind then you can resolve every degree and take total complex
# It would be good to prune a pointwise dg-rep, though.
# Anyhow, the big parts of this complex never get computed because of the form of u_res

# dgm = dgModule.outer_tensor_product(circle_mod_rotation, circle_mod_rotation).total_complex()

dgm = dgModule.outer_tensor_product(circle_mod_rotation, circle_mod_rotation).total_complex()

# Then build the double complex for hocolim

def union_full(t):
    return 1 if all([any([(i in p) for p in t]) for i in range(3)]) else 0

def conf_union_law(x, f, y):
    source = union_full(x)
    target = union_full(y)
    return matrix(QQ, source, target, [1]*(source * target))

pos2 = ProductCategory(pos, pos)
print pos2.objects

union_rep = MatrixRepresentation(pos2, QQ, conf_union_law)

print 'computing presentation matrix'
u_res = [union_rep.presentation()]
for i in range(10):
    print 'computing step ' + str(i + 1) + ' of the resolution'
    u_res += [+u_res[i]]

def ud_law_res(_, (d_res, d_rep)):
    return dgm.module_in_degree(d_rep)(u_res[d_res])

def ud_law_rep(_, (d_res, d_rep)):
    b_summands = []
    for x in u_res[d_res].source:
        b_summands += [dgm.differential(x, d_rep)]
    return CatMat.block_diagonal(b_summands, ring=QQ)

def ud_f_law((d_res, d_rep), x, f, y):
    return identity_matrix(QQ, dgm.module_in_degree(d_rep)(u_res[d_res]).nrows())

double_complex = dgModule(pt, QQ, ud_f_law, [ud_law_res, ud_law_rep])

hocolim = double_complex.total_complex()

C = ChainComplex({k:hocolim.differential('*', k).transpose() for k in range(9)})
print C.homology()

#def uf_law(d, x, f, y):
#    return CatMat.identity_matrix(ZZ, pt, u_res[d].source)

#union_resolution = dgModule(pt, ZZ, uf_law, [ud_law], target_cat=pos2)

# Should give a list of differential laws to dgModule
# every other degree specified

hr = (0, 1, 2)

c0 = circle_mod_rotation((hr, '*', hr), (0, 1))
c1 = circle_mod_rotation((hr, '*', hr), (1, 2))
c2 = circle_mod_rotation((hr, '*', hr), (2, 3))

print c0*c1 == zero_matrix(ZZ, c0.nrows(), c1.ncols())
print c1*c2 == zero_matrix(ZZ, c1.nrows(), c2.ncols())

# C = ChainComplex({0: c0.transpose(), 1: c1.transpose(), 2: c2.transpose()})

#print C.homology()

print


