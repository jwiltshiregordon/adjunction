from sage.all import *
from CatMat import *
from CatMat import TerminalCategory
from sage.all import vector, matrix, zero_matrix, identity_matrix, block_diagonal_matrix
from sage.all import Matroid
import sys
sys.path.insert(0, '/Users/jwiltshiregordon/Dropbox/SageUseful')
from ConfigurationSpace import power_complex
from PruneOld import *



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


def load_model(model_name):
    z = load(model_name)

    def f_law((d,), x, f, y):
        return CatMat.identity_matrix(ring, D, z[d][0])

    def d_law(x, (d,)):
        if d in z:
            return CatMat(ring, D, z[d][0], z[d][1], z[d][2])
        else:
            return CatMat.zero_matrix(ring, D, [], [])

    return dgModule(TerminalCategory, ring, f_law, [d_law], target_cat=D)

# Make sure n matches because the code will run anyway
space_X = load_model('conf-3-circle')
space_Y = load_model('conf-3-circle')


double_complex = dgModule.outer_tensor_product(space_X, space_Y)

D_squared = double_complex.target_cat
tot = double_complex.total_complex()




def graph_union(list_of_edge_sets):
    return tuple((a, b) for a, b in GraphEdges(n) if any((a, b) in es for es in list_of_edge_sets))

def full_union_f_law(x, f, y):
    rr = 1 if graph_union(x) == GraphEdges(n) else 0
    cc = 1 if graph_union(y) == GraphEdges(n) else 0
    return matrix(ring, rr, cc, [1] * (rr * cc))

full_union = MatrixRepresentation(D_squared, ring, full_union_f_law)

# TODO: must use resolution for full_union here?



Ch = ChainComplex({k:full_union(tot.differential(('*','*'), (k,))).transpose() for k in range(9)})
h = Ch.homology()
for d in h:
    print h[d]

