from sage.all import *
from CatMat import *

from CochainModels import *

print n
print V
print E


print D

for x in D.objects:
    print x

print

print equivariant_complexes

for x in D.objects:
    for y in D.objects:
        for f in D.hom(x, y):
            print 'map induced by ' + str(f) + ': ' + str(x) + ' ---> ' + str(y)
            print equivariant_complexes.module_in_degree((2,))(x, f, y)



D_squared = ProductCategory(D, D)


decompositions_of_kn = [(a, b) for a, b in D_squared.objects if union(a, b) == E]
print 'Pairs of graphs that union to complete graph: ' + str(decompositions_of_kn)

space_X = equivariant_complexes
space_Y = equivariant_complexes

iota = D_squared.full_subcategory_inclusion(decompositions_of_kn)
outer = dgModule.outer_tensor_product(space_X, space_Y)
dgm = iota.upper_star()(outer)


double_complex = dgm.hocolim()
hocolim = double_complex.total_complex()


Ch = ChainComplex({k:hocolim.differential('*', (k,)).transpose() for k in range(9)})
for d in Ch.homology():
    print Ch.homology()[d]
