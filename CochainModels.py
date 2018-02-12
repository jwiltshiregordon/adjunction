from sage.all import *
from CatMat import *
from sage.all import vector, matrix, zero_matrix, identity_matrix, block_diagonal_matrix
from sage.all import Matroid


def Vertices(n):
    return range(1, n + 1)
def GraphEdges(n):
    return [(i, j) for i, j in Combinations(Vertices(n), 2)]
def Graphs(n):
    return list(Subsets(GraphEdges(n)))



def G_one(x):
    return '*'
def G_hom(x, y):
    return ['*'] if x.issubset(y) else []
def G_comp(x, f, y, g, z):
    return '*'
# This poset is called \mathcal{G}(n) in the paper
def G(n):
    return FiniteCategory(Graphs(n), G_one, G_hom, G_comp)


# Models available:

# reals
# complexes
# equivariant_complexes
# simplicial_complex(X) for X a simplicial complex





n = 3
V = Vertices(n)
E = GraphEdges(n)
D = G(n)
Dop = D.op()
ring = GF(2)







# Reals via acyclic orientations
def acyclic_orientations(g):
    return [DiGraph([V, z.edges()]) for z in Graph([V, list(g)], format='vertices_and_edges').orientations()
            if z.is_directed_acyclic()]

def reals_f_law((d,), x, f, y):
    if d == 0:
        rows = acyclic_orientations(x)
        cols = acyclic_orientations(y)
        def matrix_entry(r, c):
            return 1 if all([all([p in c.neighbors_out(i) for p in r.neighbors_out(i)]) for i in V]) else 0
        return matrix(ring, len(rows), len(cols), [matrix_entry(r, c) for r in rows for c in cols])
    return matrix(ring, 0, 0, [])

def reals_d_law(x, (d,)):
    if d == -1:
        return matrix(ring, 0, len(acyclic_orientations(x)), [])
    if d == 0:
        return matrix(ring, len(acyclic_orientations(x)), 0, [])
    return matrix(ring, 0, 0, [])

reals = dgModule(D, ring, reals_f_law, [reals_d_law])


# Complex numbers via Orlik-Solomon algebra
def nbc_basis_in_degree(d, g):
    os_algebra = Matroid(graph=Graph([V, list(g)]), groundset=list(g)).orlik_solomon_algebra(ring)
    b = os_algebra.basis()
    return [fs for fs in b.keys() if os_algebra.degree_on_basis(fs) == d]

os_algebra = Matroid(graph=Graph([V, E]), groundset=E).orlik_solomon_algebra(ring)

def complexes_f_law((d,), x, f, y):
    rows = nbc_basis_in_degree(d, x)
    cols = nbc_basis_in_degree(d, y)

    os_algebra_x = Matroid(graph=Graph([V, list(x)]), groundset=list(x)).orlik_solomon_algebra(ring)
    os_algebra_y = Matroid(graph=Graph([V, list(y)]), groundset=list(y)).orlik_solomon_algebra(ring)

    def matrix_entry(r, c):
        return os_algebra_y.subset_image(r).coefficient(c)

    return matrix(ring, len(rows), len(cols), [matrix_entry(r, c) for r in rows for c in cols])

def complexes_d_law(x, (d,)):
    return zero_matrix(ring, len(nbc_basis_in_degree(d, x)), len(nbc_basis_in_degree(d + 1, x)))

complexes = dgModule(D, ring, complexes_f_law, [complexes_d_law])




# Complex numbers // rotation via equivariant Orlik-Solomon algebra
def equivariant_nbc_basis(d, g):
    os_algebra = Matroid(graph=Graph([V, list(g)]), groundset=list(g)).orlik_solomon_algebra(ring)
    b = os_algebra.basis()
    return [fs for fs in b.keys()
            if (os_algebra.degree_on_basis(fs) - d) % 2 == 0 and os_algebra.degree_on_basis(fs) <= d]

def equivariant_complexes_f_law((d,), x, f, y):
    rows = equivariant_nbc_basis(d, x)
    cols = equivariant_nbc_basis(d, y)

    os_algebra_x = Matroid(graph=Graph([V, list(x)]), groundset=list(x)).orlik_solomon_algebra(ring)
    os_algebra_y = Matroid(graph=Graph([V, list(y)]), groundset=list(y)).orlik_solomon_algebra(ring)

    def matrix_entry(r, c):
        return os_algebra_y.subset_image(r).coefficient(c)

    return matrix(ring, len(rows), len(cols), [matrix_entry(r, c) for r in rows for c in cols])

def equivariant_complexes_d_law(x, (d,)):
    rows = equivariant_nbc_basis(d, x)
    cols = equivariant_nbc_basis(d + 1, x)

    def matrix_entry(r, c):
        if c.issubset(r):
            missings = [z for z in r if not (z in c)]
            if len(missings) != 1:
                return 0
            missing = missings[0]
            return (-1)**(sorted(r).index(missing))
        return 0

    return matrix(ring, len(rows), len(cols), [matrix_entry(r, c) for r in rows for c in cols])

equivariant_complexes = dgModule(D, ring, equivariant_complexes_f_law, [equivariant_complexes_d_law])

# This code loads matrixwise information and returns pointwise.
# Use it with OberwolfachPractice-style code.
#
# If you prefer to use the matrixwise dgModules directly,
# then you will want the ProdConf-style code.
# TODO: I don't think this code currently runs
#
# filename should be like 'conf-2-claw'
# and should contain a dict of triples (source, data_vector, target)
# The conventions are a bit different for object names in the loaded file
# They are tuples of tuples.  To make them sets, use Set(edges_tuple).
def load_pruned_model(filename):
    dvs = load(filename + '.sobj')
    ring = dvs[0][1].base_ring()
    diff_dict = {}
    for d in dvs:
        source = [Set(t) for t in dvs[d][0]]
        target = [Set(t) for t in dvs[d][2]]
        diff_dict[d] = CatMat(ring, Dop, source, dvs[d][1], target).transpose()

    def f_law((d,), x, f, y):
        if d in diff_dict:
            fm = D.free_op_module(ring, diff_dict[d].target)
            return fm(y, f, x).transpose()
        return matrix(ring, 0, 0, [])

    def d_law(x, (d,)):
        if d in diff_dict:
            fom = D.free_module(ring, [x])
            return fom(diff_dict[d]).transpose()
        return matrix(ring, 0, 0, [])

    return dgModule(D, ring, f_law, [d_law], target_cat=None)

#
# def load_unpruned_model(scx):
#     cx = simplicial_complex_model(scx)
#
#     def f_law((d,), x, f, y):
#         fm = D.free_module(ring, [Set(s) for s in cx.differential('*', (d,)).source])
#         return fm(x, f, y)
#
#     def d_law(x, (d,)):
#         fom = D.free_op_module(ring, [x])
#         return fom(cx.differential('*', (d,)))
#
#     return dgModule(D, ring, f_law, [d_law], target_cat=None)
#


# If you are going to do a big one
# change the ring to something fast
# cx = simplicial_complex(SimplicialComplex([[1, 2], [1, 3], [1, 4]]))






