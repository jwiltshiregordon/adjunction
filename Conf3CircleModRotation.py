from sage.all import vector, Combinations, Subsets, Set, SimplicialComplex, ZZ, ChainComplex, save
from CatMat import FiniteCategory, CatMat, dgModule, TerminalCategory
from Prune import prune_dg_module_on_poset

n = 3
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

# The three dashed diagonals in the figure are pink, blue, and green.
# Our convention: the pink line indicates where points 1 and 2 coincide; blue for 1 and 3; and green for 2 and 3.
# This leads to easier names for the objects.  The prefix a_ stands for 'avoid'
a_, a_p, a_b, a_g, a_pb, a_pg, a_bg, a_pbg = Gop.objects

# In the diagram, the maximal overlaps are as follows:
# AEC, BDF, AHX, AHS, BHS, BHY, CHY, CHT, DHX, DHU, EHU, EHZ, FHT, FHZ, BFSZ, AESZ, BDUY, CEUY, ACTX, DFTX
# the pink diagonal 12 slices the opens HUY
# the blue diagonal 13 slices the opens HSZ
#     and the green 23 slices the opens HTX

facets = ['AEC', 'BDF', 'AHX', 'AHS', 'BHS', 'BHY', 'CHY', 'CHT', 'DHX', 'DHU', 'EHU', 'EHZ', 'FHT', 'FHZ',
          'BFSZ', 'AESZ', 'BDUY', 'CEUY', 'ACTX', 'DFTX']

prod_model = SimplicialComplex([list(facet) for facet in facets])

def simplex_degree(s):
    deg = Set(edges)
    for u in s:
        if u in 'HUY':
            deg = deg.difference(Set([(1, 2)]))
        if u in 'HSZ':
            deg = deg.difference(Set([(1, 3)]))
        if u in 'HTX':
            deg = deg.difference(Set([(2, 3)]))
    return Set([e for e in edges if e in deg])

for f in prod_model.face_iterator():
    print f
    print simplex_degree(f)
    print

bases = {}
for d in range(4):
    bases[d] = [(f, s) for s in G.objects for f in prod_model.n_faces(d) if simplex_degree(f) == s]
bases[-1] = []
bases[4] = []

def f_law((d,), x, f, y):
    if d in bases:
        source_target = [p[1] for p in bases[d]]
        return CatMat.identity_matrix(ZZ, Gop, source_target)
    return CatMat.identity_matrix(ZZ, Gop, [])

def d_law(x, (d,)):
    if d in range(-1, 4):
        def d_entry(f, g):
            if f.is_face(g):
                return (-1) ** g.faces().index(f)
            else:
                return 0
        data_vector = [d_entry(f, g) for f, fd in bases[d] for g, gd in bases[d + 1] if len(Gop.hom(fd, gd)) == 1]
        source = [p[1] for p in bases[d]]
        target = [q[1] for q in bases[d + 1]]
        return CatMat(ZZ, Gop, source, vector(ZZ, data_vector), target)
    return CatMat.identity_matrix(ZZ, Gop, [])

dgm_big = dgModule(TerminalCategory, ZZ, f_law, [d_law], target_cat=Gop)
top_deg = 100
dgm = prune_dg_module_on_poset(dgm_big, (0, top_deg), verbose=verbose, assume_sorted=True)

print
print 'Homological computation begins'
for x in G.objects:
    free = G.free_module(ZZ, [x])
    print 'Graph ' + str(x)
    print 'computing complex'
    Ch = ChainComplex({k: free(dgm.differential('*', (k,)).transpose()) for k in range(top_deg)})
    print 'computing homology'
    h = Ch.homology()
    print h
    print

diff_dict = {d: dgm.differential('*', (d,)) for d in range(-1, top_deg + 1)}
save_dict = {d: (diff_dict[d].source, diff_dict[d].data_vector, diff_dict[d].target)
             for d in range(-1, top_deg + 1)}

save(save_dict, 'conf-3-circle-mod-rotation')
print 'small complex saved'
