from CatMat import *
from CatMat import TerminalCategory
from sage.all import vector, matrix, zero_matrix, identity_matrix, block_diagonal_matrix
from Prune import prune_dg_module_on_poset

# Set these values before running
# For example, set n = 3 and factor_names = ['conf-3-interval', 'conf-3-interval']
# to compute the homology of three distinct points in the plane.
# To generate new files, use GraphicalChainModels.  In this code, models are assumed to be cofibrant.

n = 2
factor_names = ['conf-2-interval', 'conf-2-circle']
ring = ZZ
save_result = False
filename = 'conf-2-cyl'
verbose = True
top_deg = 30
display_degree = 12

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
        if d in z:
            return CatMat.identity_matrix(ring, Gop, z[d][0])
        else:
            return CatMat.identity_matrix(ring, Gop, [])

    def d_law(x, (d,)):
        if d in z:
            return CatMat(ring, Gop, z[d][0], z[d][1], z[d][2])
        else:
            return CatMat.identity_matrix(ring, Gop, [])

    return dgModule(TerminalCategory, ring, f_law, [d_law], target_cat=Gop)

q = len(factor_names)
spaces = [load_model(X) for X in factor_names]
multi_complex = dgModule.outer_tensor_product(*spaces)
D_power = multi_complex.target_cat
tot = multi_complex.total_complex()

def graph_union(tuple_of_edge_sets):
    u = Set()
    for es in tuple_of_edge_sets:
        u = u.union(es)
    return u

def graph_union_law(x, f, y):
    return (graph_union(x), '*', graph_union(y))

union_functor = Functor(D_power, graph_union_law, Gop)

def holan_d_law(x, (d,)):
    return union_functor(tot.differential(('*',) * q, (d,)))

def holan_f_law((d,), x, f, y):
    return union_functor(tot.module_in_degree(d)(x, f, y))

holan = dgModule(TerminalCategory, ring, holan_f_law, [holan_d_law], target_cat=Gop)

dgm = prune_dg_module_on_poset(holan, (0, top_deg), verbose=verbose, assume_sorted=False)

print
print 'Homological computation begins'
for x in G.objects:
    cofree = Gop.cofree_module(ring, [x])
    print 'Graph ' + str(x)
    print 'computing complex'
    ch = ChainComplex({-(k + 1): cofree(dgm.differential('*', (k,))) for k in range(-1, top_deg)})
    print 'computing homology'
    for i in range(display_degree):
        print 'H_' + str(i) + ' = ' + str(ch.homology(-i))
    print

if save_result:
    diff_dict = {d: dgm.differential('*', (d,)) for d in range(-1, top_deg + 1)}
    save_dict = {d: (diff_dict[d].source, diff_dict[d].data_vector, diff_dict[d].target)
                 for d in range(0, top_deg)}

    save(save_dict, filename)
    print 'small complex saved'
