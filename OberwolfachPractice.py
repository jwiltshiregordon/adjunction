from sage.all import *
from CatMat import *

# Load up the models and examine the givens
from CochainModels import *


print n
print V
print E
print

print D
print D.objects
print

for x in D.objects:
    for y in D.objects:
        print 'hom(' + str(x) + ', ' + str(y) + ') = ' + str(D.hom(x, y))


print
print





# Examine two models

print reals

for x in D.objects:
    for y in D.objects:
        for f in D.hom(x, y):
            print 'map induced by ' + str(f) + ': ' + str(x) + ' ---> ' + str(y)
            print reals.module_in_degree((0,))(x, f, y)


print
print


print complexes

for x in D.objects:
    for y in D.objects:
        for f in D.hom(x, y):
            print 'map induced by ' + str(f) + ': ' + str(x) + ' ---> ' + str(y)
            print complexes.module_in_degree((1,))(x, f, y)


print
print



# Compute the homotopy colimit


D_squared = ProductCategory(D, D)
print D_squared
print D.objects
print

for x in D_squared.objects:
    for y in D_squared.objects:
        print 'hom(' + str(x) + ', ' + str(y) + ') = ' + str(D_squared.hom(x, y))


print
print


claw = SimplicialComplex([[1, 2], [1, 3], [1, 4]])
interval = SimplicialComplex([[1, 2]])
# claw_model = simplicial_complex(claw)


# space_X = simplicial_complex(interval)
space_Y = load_pruned_model('conf-3-circle')
# space_Y = equivariant_complexes
space_X = load_pruned_model('conf-3-circle')
# space_X = load_unpruned_model(SimplicialComplex([[1, 2]]))
# space_Y = load_pruned_model('conf-2-interval')





decompositions_of_kn = [(a, b) for a, b in D_squared.objects if union(a, b) == E]
print 'Pairs of graphs that union to complete graph: ' + str(decompositions_of_kn)

iota = D_squared.full_subcategory_inclusion(decompositions_of_kn)
outer = dgModule.outer_tensor_product(space_X, space_Y)
dgm = iota.upper_star()(outer)


double_complex = dgm.hocolim()
hocolim = double_complex.total_complex()


Ch = ChainComplex({k:hocolim.differential('*', (k,)).transpose() for k in range(9)})
for d in Ch.homology():
    print Ch.homology()[d]























sys.exit(0)


# we get a category D to play with
# and models to play with
# Then build a rep to see how it's done
# resolve trivial rep to see



# Build the poset of subgraphs of a graph





# Build the trivial rep

# Resolve projectively

# Examine the resolution

# Examine the model for the reals


# Compute cohomology of Conf(2, reals x reals)



D2 = ProductCategory(D, D)
iota = D2.full_subcategory_inclusion([(a, b) for a, b in D2.objects if union(a, b) == E])
outer = dgModule.outer_tensor_product(equivariant_complexes, cx)
dgm = iota.upper_star()(outer)
double_complex = dgm.hocolim()

hocolim = double_complex.total_complex()

Ch = ChainComplex({k:hocolim.differential('*', (k,)).transpose() for k in range(9)})
print Ch.homology()


#view(LatexExpr(aui.to_latex()), tightpage=True)