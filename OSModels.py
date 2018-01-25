from sage.all import *
from sage.all import Matroid


ring = ZZ

g1 = Graph([[1, 2], [[1, 2]]])
g2 = Graph([[1, 2, 3], [[1, 2], [1, 3], [2, 3]]])


def nbc_basis_in_degree(d, g):
    os_algebra = Matroid(g).orlik_solomon_algebra(ring)
    b = os_algebra.basis()
    return [fs for fs in b.keys() if os_algebra.degree_on_basis(fs) == d]




print nbc_basis_in_degree(1, g1)
print nbc_basis_in_degree(1, g2)

rows = nbc_basis_in_degree(1, g1)
cols = nbc_basis_in_degree(1, g2)

os_algebra1 = Matroid(g1).orlik_solomon_algebra(ring)
os_algebra2 = Matroid(g2).orlik_solomon_algebra(ring)


def matrix_entry(r, c):
    return os_algebra2.subset_image(r).coefficient(c)

print [matrix_entry(r, c) for r in rows for c in cols]


os = Matroid(g1).orlik_solomon_algebra(ring)
print os.basis()
print os._broken_circuits

print list(Matroid(g1).circuits())

print list(Matroid(graph=g1, groundset=[(i, j) for i, j, k in g1.edge_iterator()]).groundset())
print list(Matroid(g2).groundset())
#print Matroid(g1).no_broken_circuits_sets([(1, 2, None)])
