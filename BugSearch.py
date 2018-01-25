from sage.all import *
from CatMat import *
from CatMat import TerminalCategory
from sage.all import vector, matrix, zero_matrix, identity_matrix, block_diagonal_matrix
from sage.all import Matroid
import sys
sys.path.insert(0, '/Users/jwiltshiregordon/Dropbox/SageUseful')
from ConfigurationSpace import power_complex

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




n = 2
V = Vertices(n)
E = GraphEdges(n)
D = G(n)
ring = QQ







m1 = CatMat.identity_matrix(ring, D, D.objects[1])

print len(CatMat.kronecker_product(m1, m1).cat.objects)







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




def simplicial_complex(X):
    cmp = conf_matrix_poset(n, X)
    max_conf_mats = cmp.maximal_elements()
    somehow_minimals = [cm for cm in cmp if is_conf_matrix_somehow_minimal(cm)]
    vertex_gen_dict = {m: distinct_row_pairs(m) for m in somehow_minimals}

    def are_compat(conf_mats):
        return any(all(is_column_submatrix(cm, mx) for cm in conf_mats) for mx in max_conf_mats)

    prod_model = SimplicialComplex(from_characteristic_function=(are_compat, somehow_minimals))





    # Every simplex s in prod_model begins existing once all of its vertices exist
    def simplex_generator(s):
        return graph_union([vertex_gen_dict[v] for v in s])

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






cx = simplicial_complex(SimplicialComplex([[1, 2]]))


double_complex = dgModule.outer_tensor_product(cx, cx)
print 'ndiff'
print double_complex.n_diff



dd0 = double_complex.differential(('*', '*'), (0, 0), a=0).row(0).column(0)

dd1 = double_complex.differential(('*', '*'), (0, 0), a=1).row(0).column(2)

print 'dd0'
print (dd0.source, dd0.data_vector, dd0.target, len(dd0.cat.objects))
print 'dd1'
print (dd1.source, dd1.data_vector, dd1.target, len(dd1.cat.objects))

print dd1


def is_sane(cm):
    CatMat(cm.ring, cm.cat, cm.source, cm.data_vector, cm.target)
    CatMat.block_matrix([[cm]], sources=[cm.source], targets=[cm.target], cat=cm.cat)
    return True

print 'dd0'
print is_sane(dd0)

print 'dd1'
print is_sane(dd1)

print dd0.source == dd1.source

D_squared = double_complex.target_cat

print (len(dd0.cat.objects), len(D_squared.objects))
print dd0.cat == D_squared

print CatMat.block_matrix([[dd0, dd1]], cat=D_squared)




def full_union_f_law(x, f, y):
    rr = 1 if graph_union(x) == GraphEdges(n) else 0
    cc = 1 if graph_union(y) == GraphEdges(n) else 0
    return matrix(ring, rr, cc, [1] * (rr * cc))

full_union = MatrixRepresentation(D_squared, ring, full_union_f_law)

for x in D_squared.objects:
    for y in D_squared.objects:
        for f in D_squared.hom(x, y):
            print (x, f, y)
            print full_union(x, f, y)
            print


tot = double_complex.total_complex()
print tot.differential(('*', '*'), (0,))

sys.exit(0)






def dg_rep_f_law((d, e), x, f, y):
    return full_union(double_complex.module_in_degree((d, e))(('*', '*'), '(*,*)', ('*', '*')))

def dg_rep_d_law_0(x, (d, e)):
    return full_union(double_complex.differential(x, (d, e), a=0))

def dg_rep_d_law_1(x, (d, e)):
    return full_union(double_complex.differential(x, (d, e), a=1))

dgm = dgModule(TerminalCategory, ring, dg_rep_f_law, [dg_rep_d_law_0, dg_rep_d_law_1]).total_complex()



Ch = ChainComplex({k:dgm.differential('*', (k,)).transpose() for k in range(9)})
print Ch.homology()



