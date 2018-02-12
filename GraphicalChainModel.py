from sage.all import *
import itertools
from multiprocessing import Pool
from CatMat import FiniteCategory, CatMat, dgModule, TerminalCategory
from Prune import *

# Set these values before running
n = 3
X = SimplicialComplex([[1, 2], [1, 3], [1, 4], [1, 5]])
ring = ZZ
save_result = True
filename = 'conf-3-plus'
verbose = True
parallelize = True

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

# Print out all the homsets
if verbose:
    for x in G.objects:
        for y in G.objects:
            print 'Hom(' + str(x) + ', ' + str(y) + ') = ' + str(G.hom(x, y))

# Build the vertices of X^n

# Given a list of dimensions, this function builds all integer matrices with first column zero,
# last column dim_list, all columns distinct, and where consecutive entries in a row have difference 0 or 1.
gen_prod_mat = {}
def generic_prod_mat(dim_tuple):
    if dim_tuple in gen_prod_mat:
        return gen_prod_mat[dim_tuple]
    k = len(dim_tuple)
    first_column = zero_matrix(ZZ, k, 1)
    last_column = matrix(ZZ, k, 1, [d for d in dim_tuple])
    # If dim_list is all zeros, then return a single matrix of zeros.
    if first_column == last_column:
        return [first_column]
    current_batch = [first_column]
    next_batch = []
    gpms = []
    while len(current_batch) != 0:
        for m in current_batch:
            l = m.ncols()
            next_column_options = [range(m[r, l - 1], min(m[r, l - 1] + 2, dim_tuple[r] + 1)) for r in range(k)]
            new_column_iterator = itertools.product(*next_column_options)
            # we don't want the same column again.
            drop = next(new_column_iterator)
            for next_column_tuple in new_column_iterator:
                next_column = matrix(ZZ, k, 1, next_column_tuple)
                mm = block_matrix([[m, matrix(ZZ, k, 1, next_column)]], subdivide=False)
                if next_column == last_column:
                    gpms += [mm]
                else:
                    next_batch += [mm]
        current_batch = next_batch
        next_batch = []
    gen_prod_mat[dim_tuple] = gpms
    return gpms


# This set will contain a list of all the Gamma-conf matrices
# where Gamma is the empty graph on n nodes.
prod_mats = set()

nonempty_faces = X.face_iterator(increasing=True)
# This line pops off the empty face
next(nonempty_faces)

for simplex_tuple in itertools.product(nonempty_faces, repeat=n):
    dim_tuple = tuple(s.dimension() for s in simplex_tuple)
    for gpm in generic_prod_mat(dim_tuple):
        l = gpm.ncols()
        m = matrix(ZZ, n, l, [simplex_tuple[r][gpm[r, c]] for r in range(n) for c in range(l)])
        m.set_immutable()
        prod_mats.add(m)

# Each prod matrix gets assigned a number.  Build the translation dicts both ways.
# While we're looping, we also compute the row-distinctness graph for each prod matrix
pm_to_nn = {}
nn_to_pm = {}
gammas = {}
nns_by_gamma = {graph:[] for graph in graphs}
for nn, pm in enumerate(prod_mats):
    pm_to_nn[pm] = nn
    nn_to_pm[nn] = pm
    graph = Set((i, j) for i, j in edges if pm.row(vertices.index(i)) != pm.row(vertices.index(j)))
    gammas[nn] = graph
    nns_by_gamma[graph] += [nn]

# The matrix cmb is the combination table.  The (i, j)-entry gives the index of the smallest prod mat that
# contains the columns of the ith and jth prod mat.  If no such prod mat exists, the table gives -1.
pmt = len(prod_mats)
cmb = zero_matrix(ZZ, pmt, pmt)


if verbose:
    print 'Preparing combination table'
    print 'Total number of rows: ' + str(pmt)

# for i in range(pmt):
#     cmb[i, i] = i
# z = 1
# zz = len(prod_mats) * (len(prod_mats) - 1) / 2
# for i in range(pmt):
#     for j in range(i + 1, pmt):
#         if verbose:
#             print '\r' + str(z) + '/' + str(zz),
#             sys.stdout.flush()
#             z += 1
#         p = nn_to_pm[i]
#         q = nn_to_pm[j]
#         both_cols = list(set(p.columns() + q.columns()))
#         both_cols.sort()
#         combined = block_matrix([[matrix(ZZ, n, 1, list(v)) for v in both_cols]], subdivide=False)
#         combined.set_immutable()
#         if combined in prod_mats:
#             cmb[i, j] = pm_to_nn[combined]
#             cmb[j, i] = cmb[i, j]

def prep_cmb_row(i):
    row = zero_matrix(ZZ, 1, pmt)
    p_cols = nn_to_pm[i].columns()
    for j in range(i + 1, pmt):
        q = nn_to_pm[j]
        both_cols = list(set(p_cols + q.columns()))
        both_cols.sort()
        combined = block_matrix([[matrix(ZZ, n, 1, list(v)) for v in both_cols]], subdivide=False)
        combined.set_immutable()
        if combined in prod_mats:
            row[0, j] = pm_to_nn[combined]
        else:
            row[0, j] = -1
    if verbose:
        if i % 100 == 0:
            print 'Finished row ' + str(i)
    return [row]

if parallelize:
    pool = Pool()
    cmb_row_list = pool.map(prep_cmb_row, xrange(pmt))
    pool.close()
    pool.join()
else:
    cmb_row_list = [prep_cmb_row(i) for i in range(pmt)]
cmb = block_matrix(cmb_row_list)
cmb = cmb + cmb.transpose() + diagonal_matrix(range(pmt))


# Check if a list of prod matrices can have their columns assembled into a single prod matrix
def index_compatible(list_of_indices):
    if len(list_of_indices) <= 1:
        return True
    cur = list_of_indices[0]
    for i in list_of_indices[1:]:
        cur = cmb[cur, i]
        if cur == -1:
            return False
    return True


# For each graph Gamma, compute the minimal prod matrices of type Gamma.
min_prod_mat_indices = []
min_prod_mat_indices_by_gamma = {}
for gamma in graphs:
    def leq(i, j):
        return cmb[i, j] == j
    poset = Poset((nns_by_gamma[gamma], leq))
    min_prod_mat_indices_by_gamma[gamma] = poset.minimal_elements()
    min_prod_mat_indices += min_prod_mat_indices_by_gamma[gamma]

# Build the resulting simplicial complex model for the product
if verbose:
    print
    print 'Building the souped-up model for the product'
    print

# My copy of sagemath has a verbose flag for SimplicialComplex, but this is not standard yet
prod_model = SimplicialComplex(from_characteristic_function=(index_compatible, min_prod_mat_indices), verbose=verbose)
dim = prod_model.dimension()


# for graph in graphs:
#     Y = SimplicialComplex(from_characteristic_function=(index_compatible,
#                                                         [i for gamma in graphs if graph.issubset(gamma) for i in min_prod_mat_indices_by_gamma[gamma]]))
#     print 'Graph ' + str(graph)
#     for d in range(Y.dimension() + 1):
#         print 'Faces of dimension ' + str(d) + ': ' + str(len(Y.n_faces(d)))
#     print Y.homology()
#     print
#
#
# sys.exit(0)

if verbose:
    print 'Computing generator degrees'
z = 1
zz = sum(len(prod_model.n_faces(d)) for d in range(dim + 1))
sorted_basis = {}
for d in range(dim + 1):
    sorted_basis[d] = {graph: [] for graph in graphs}
    for f in prod_model.n_faces(d):
        if verbose:
            print '\r' + str(z) + '/' + str(zz),
            sys.stdout.flush()
            z += 1
        gamma = Set(set(edges).intersection(*[set(gammas[m]) for m in f]))
        sorted_basis[d][gamma] += [f]
print

# In degree d, this dict holds a list of faces of prod_model
basis = {}
# labels[d] has the same length as basis[d] and tells you which graph
labels = {}
for d in range(-1, dim + 2):
    basis[d] = []
    labels[d] = []
    if d in range(dim + 1):
        for graph in graphs:
            batch = sorted_basis[d][graph]
            basis[d] += batch
            labels[d] += [graph] * len(batch)

def f_law((d,), x, f, y):
    if d in labels:
        return CatMat.identity_matrix(ring, Gop, labels[d])
    else:
        return CatMat.identity_matrix(ring, Gop, [])

def d_law(x, (d,)):
    if d in range(0, dim + 2):
        def d_entry(r, c):
            if c.is_face(r):
                return (-1) ** r.faces().index(c)
            else:
                return 0
        source = labels[d]
        target = labels[d - 1]
        data_list = [d_entry(r, c) for r, x in zip(basis[d], labels[d]) for c, y in zip(basis[d - 1], labels[d - 1])
                     if len(G.hom(x, y)) == 1]
        return CatMat(ring, G, source, vector(ring, data_list), target).transpose()
    else:
        return CatMat.identity_matrix(ring, Gop, [])

dgm_big = dgModule(TerminalCategory, ring, f_law, [d_law], target_cat=Gop)

# for k in range(0, 9):
#     print 'computing differential in degree ' + str(k)
#     dgm_big.differential('*', (k,))

# for k in range(0, 9):
#     mm = dgm.differential('*', (k,)) * dgm.differential('*', (k + 1,))
#     is_zero = (mm == CatMat.zero_matrix(ring, Gop, mm.source, mm.target))
#     print 'degree ' + str(k) + ' composition is zero: ' + str(is_zero)
#     if not is_zero:
#         view(LatexExpr(mm.to_latex()), tightpage=True)

top_deg = 100
dgm = prune_dg_module_on_poset(dgm_big, (0, top_deg), verbose=verbose, assume_sorted=True)

print
print 'Homological computation begins'
for x in G.objects:
    free = G.free_module(ring, [x])
    print 'Graph ' + str(x)
    print 'computing complex'
    Ch = ChainComplex({k: free(dgm.differential('*', (k,)).transpose()) for k in range(9)})
    print 'computing homology'
    h = Ch.homology()
    print h
    print

if save_result:
    diff_dict = {d: dgm.differential('*', (d,)) for d in range(-1, top_deg + 1)}
    save_dict = {d: (diff_dict[d].source, diff_dict[d].data_vector, diff_dict[d].target) for d in range(-1, top_deg + 1)}

    save(save_dict, filename)
    print 'small complex saved'
