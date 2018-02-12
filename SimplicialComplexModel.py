from sage.all import *
from CatMat import *
from CatMat import TerminalCategory
from sage.all import vector, matrix, zero_matrix, identity_matrix, block_diagonal_matrix
from sage.all import Matroid
from datetime import datetime
import sys
sys.path.insert(0, '/Users/jwiltshiregordon/Dropbox/SageUseful')
from ConfigurationSpace import power_complex
from Prune import *

# TODO: This code may have errors.  Rewrite using homology + chains the whole time so you don't get confused again.


def Vertices(n):
    return range(1, n + 1)

def GraphEdges(n):
    return tuple((i, j) for i, j in Combinations(Vertices(n), 2))

def Graphs(n):
    return [tuple(e for e in GraphEdges(n) if e in s) for s in Subsets(GraphEdges(n))]



def G_one(x):
    return '*'

def G_hom(x, y):
    return ['*'] if set(x).issubset(set(y)) else []

def G_comp(x, f, y, g, z):
    return '*'

# This poset is called \mathcal{G}(n) in the paper
def G(n):
    return FiniteCategory(Graphs(n), G_one, G_hom, G_comp)




n = 3
V = Vertices(n)
E = GraphEdges(n)
D = G(n).op()
ring = ZZ










def conf_matrices(n, X):
    pc = power_complex(n, X)

    def build_matrix(simplex):
        mm = matrix(ZZ, simplex.dimension() + 1, n, [p for c in simplex for p in c]).transpose()
        mm.set_immutable()
        return mm

    return [build_matrix(simplex) for d in pc.faces() if d >= 0 for simplex in pc.faces()[d]]


def graphical_conf_matrices(edge_pairs, X):

    def is_gamma_type(m):
        return all(m.row(a - 1) != m.row(b - 1) for a, b in edge_pairs)

    return [m for m in conf_matrices(n, X) if is_gamma_type(m)]


def is_conf_matrix_somehow_minimal(m):
    if m.ncols() == 1:
        return True
    baseline_irps = identical_row_pairs(m)
    for c in range(m.ncols()):
        mm = m.matrix_from_columns(range(c) + range(c + 1, m.ncols()))
        if baseline_irps == identical_row_pairs(mm):
            return False
    return True


def is_column_submatrix(m1, m2):
    cc = m2.columns()
    return all([c in cc for c in m1.columns()])


def conf_matrix_poset(n, X):
    return Poset(data=(conf_matrices(n, X), is_column_submatrix))


def identical_row_pairs(m):
    return [(a, b) for a, b in GraphEdges(n) if m.row(a-1) == m.row(b-1)]


def distinct_row_pairs(m):
    return [(a, b) for a, b in GraphEdges(n) if m.row(a-1) != m.row(b-1)]


def graph_union(list_of_edge_sets):
    return tuple((a, b) for a, b in GraphEdges(n) if any((a, b) in es for es in list_of_edge_sets))


def graph_intersection(list_of_edge_sets):
    return tuple((a, b) for a, b in GraphEdges(n) if all((a, b) in es for es in list_of_edge_sets))


def simplicial_complex_model(X):
    cmp = conf_matrix_poset(n, X)
    max_conf_mats = cmp.maximal_elements()
    somehow_minimals = [cm for cm in cmp if is_conf_matrix_somehow_minimal(cm)]
    vertex_gen_dict = {m: distinct_row_pairs(m) for m in somehow_minimals}

    def are_compat(conf_mats):
        return any(all(is_column_submatrix(cm, mx) for cm in conf_mats) for mx in max_conf_mats)

    prod_model = SimplicialComplex(from_characteristic_function=(are_compat, somehow_minimals))
    print 'prod_model prepared'
    print prod_model

    # A simplex in prod_model begins existing once all of its vertices exist
    def simplex_generator(s):
        return graph_intersection([vertex_gen_dict[v] for v in s])

    def gens_in_degree(d):
        if d < 0:
            return []
        if d in prod_model.faces():
            return [(s, simplex_generator(s)) for s in prod_model.faces()[d]]
        return []

    def f_law((d,), x, f, y):
        return CatMat.identity_matrix(ring, D, [p for (_, p) in gens_in_degree(d)])

    def d_law(x, (d,)):
        table = []
        for r, p in gens_in_degree(d):
            row = []
            for c, q in gens_in_degree(d + 1):
                if r.is_face(c):
                    scalar = ring((-1) ** (c.faces().index(r)))
                    row += [scalar * CatMat.from_string(ring, D, [p], '[[*]]', [q])]
                else:
                    row += [CatMat.zero_matrix(ring, D, [p], [q])]
            table += [row]
        return CatMat.block_matrix(table, ring=ring, cat=D,
                                   sources=[[p] for (_, p) in gens_in_degree(d)],
                                   targets=[[q] for (_, q) in gens_in_degree(d + 1)])

    return dgModule(TerminalCategory, ring, f_law, [d_law], target_cat=D)



# cx_big = simplicial_complex_model(SimplicialComplex([[1, 2]]))
# cx = simplicial_complex_model(SimplicialComplex([[1, 2], [1, 3], [2, 3]]))
#
# print 'big complex computed'
# print str(datetime.now())
#
# top_deg = 100
# cx = prune_dg_module_on_poset(cx_big, (0, top_deg), verbose=True)

# diff_dict = {d: cx.differential('*', (d,)) for d in range(-1, top_deg + 1)}
# save_dict = {d: (diff_dict[d].source, diff_dict[d].data_vector, diff_dict[d].target) for d in range(-1, top_deg + 1)}
#
# save(save_dict, 'conf-3-circle')
# print 'small complex saved'
# print str(datetime.now())
