from CatMat import *
from CatMat import TerminalCategory
from sage.all import vector, matrix, zero_matrix, identity_matrix, block_diagonal_matrix

# Set these values before running
# The current choices for X_source and Y_source are file names in the current directory.
# For example, you could use 'conf-3-interval' for both sources.
# To generate new files, use GraphicalChainModels.  In this code, models are assumed to be cofibrant.

n = 3
X_source = 'conf-3-plus'
Y_source = 'conf-3-circle-mod-rotation'
ring = ZZ
verbose = True

# Set up our graphs
vertices = range(1, n + 1)
edges = [(i, j) for i, j in Combinations(vertices, 2)]
graphs = list(Subsets(edges))

# Define the poset G(n) as a category
def G_one(x):
    return '*'
def G_hom(x, y):
    if x.issubset(y):
        return ['*']
    return []
def G_comp(x, f, y, g, z):
    return '*'
G = FiniteCategory(graphs, G_one, G_hom, G_comp)
Gop = G.op()


def load_model(model_name):
    z = load(model_name)

    def f_law((d,), x, f, y):
        return CatMat.identity_matrix(ring, Gop, z[d][0])

    def d_law(x, (d,)):
        if d in z:
            return CatMat(ring, Gop, z[d][0], z[d][1], z[d][2])
        else:
            return CatMat.zero_matrix(ring, Gop, [], [])

    return dgModule(TerminalCategory, ring, f_law, [d_law], target_cat=Gop)

space_X = load_model(X_source)
space_Y = load_model(Y_source)

double_complex = dgModule.outer_tensor_product(space_X, space_Y)
D_squared = double_complex.target_cat
tot = double_complex.total_complex()


def graph_union(list_of_edge_sets):
    return [e for e in edges if any(e in g for g in list_of_edge_sets)]


def full_union_f_law(x, f, y):
    rr = 1 if graph_union(x) == edges else 0
    cc = 1 if graph_union(y) == edges else 0
    return matrix(ring, rr, cc, [1] * (rr * cc))

full_union = MatrixRepresentation(D_squared, ring, full_union_f_law)

Ch = ChainComplex({k:full_union(tot.differential(('*','*'), (k,))).transpose() for k in range(9)})
h = Ch.homology()
for d in h:
    print h[d]
