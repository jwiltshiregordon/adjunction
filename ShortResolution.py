from sage.all import *
from CatMat import *
from sage.all import vector, matrix, zero_matrix, identity_matrix, block_diagonal_matrix


def pos_one(x):
    return '*'

def pos_hom(x, y):
    if all([a in y for a in x]):
        return ['*']
    return []

def pos_comp(x, f, y, g, z):
    return '*'

def GraphEdges(n):
    return [str(i + 1) + str(j + 1) for i in range(n) for j in range(i + 1, n)]


def Graphs(n):
    return [tuple(sorted(tuple(a))) for a in Subsets(GraphEdges(n))]
    #return [a for a in Subsets(GraphEdges(n))]


# This poset is called \mathcal{G}(n) in the paper
def PosetOfGraphs(n):
    edge_set = GraphEdges(n)
    graph_list = Graphs(n)
    return FiniteCategory(graph_list, pos_one, pos_hom, pos_comp)


def union_full(n, t):
    return all([any([edge in graph for graph in t]) for edge in GraphEdges(n)])


def TuplesWithFullUnion(n, k):
    return [t for t in list(itertools.product(*([Graphs(n)] * k))) if union_full(n, t)]

print list(itertools.product(*([Graphs(3)] * 2)))
print union_full(3, (tuple(), ('12', '13', '23')))
print TuplesWithFullUnion(3, 2)

# For generating good LaTeX in the case n=3
def draw_little_triangle(x):
    if x == tuple():
        return r'\tinytriangle'
    if x == ('12',):
        return r'\tinytriangleab'
    if x == ('13',):
        return r'\tinytriangleac'
    if x == ('23',):
        return r'\tinytrianglebc'
    if x == ('12', '13'):
        return r'\tinytriangleabac'
    if x == ('12', '23'):
        return r'\tinytriangleabbc'
    if x == ('13', '23'):
        return r'\tinytriangleacbc'
    if x == ('12', '13', '23'):
        return r'\tinytriangleabacbc'
    return 'problem'


def object_latex_law(t):
    return r'' + draw_little_triangle(t[0]) + '\;' + draw_little_triangle(t[1]) + r''

def morphism_latex_law(x, f, y):
    return '1'

G3_squared = ProductCategory(PosetOfGraphs(3), PosetOfGraphs(3))


def pair_hom(x, y):
    if len(pos_hom(x[0], y[0])) == 1 and len(pos_hom(x[1], y[1])) == 1:
        return ['*']
    return []


def P(n, k):
    return FiniteCategory(TuplesWithFullUnion(n, k), pos_one, pair_hom, pos_comp,
                          object_latex_law=object_latex_law,
                          morphism_latex_law=morphism_latex_law)

def constant_presheaf_law(x, f, y):
    return matrix(QQ, 1, 1, [1])


constant_presheaf = MatrixRepresentation(P(3, 2), QQ, constant_presheaf_law)

print 'computing presentation matrix'
u_res = [constant_presheaf.presentation()]
for i in range(10):
    print 'computing step ' + str(i + 1) + ' of the resolution'
    u_res += [+u_res[i]]

for m in u_res:
    print
    print m.to_latex()

print
P32 = P(3, 2)
PosetP32 = Poset((P32.objects, lambda p, q: len(P32.hom(p, q)) == 1))
print PosetP32
print PosetP32.is_meet_semilattice()
print PosetP32.is_join_semilattice()



