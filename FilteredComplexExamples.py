from SpectralSequences import *

def list_filtration(list_of_spaces):
    def filtration(s):
        q = s.dimension()
        for i, X in enumerate(list_of_spaces):
            if s in X.n_cells(q):
                print s, i
                return i
        return len(list_of_spaces)
    return filtration

X0 = SimplicialComplex([[1], [2]])
X1 = SimplicialComplex([[1, 2], [1, 3], [2, 3]])

def X(p):
    if p <= 1:
        return [X0, X1][p]
    z = p + max(X1.vertices()) - 1
    return SimplicialComplex([list(s) + [z] for s in X(p - 2).facets()] + [list(s) for s in X(p - 1).facets()])
Xall = [X(p) for p in range(11)]
print filtered_complex_SS(Xall[-1], list_filtration(Xall), 'example-SS',
                          p_range=11, q_range=(-6, 1), number_of_pages=7)
sys.exit(0)
# The following example encompasses all Hopf fibrations.
# The total sphere is filtered as follows:
#    in degree 0, ..., fiber_sphere: the fiber sphere included as an equator
#    in higher degrees             : the total sphere itself.
# If we happen to be in the situation of a Hopf fibreation, then this
# filtration coincides with the Serre filtration of the total space by
# the preimages of a CW-complex decomposition of the base, and so we
# obtain the Serre spectral sequence.  In this degenerate case, it will
# also be a Thom-Gysin sequence and a Wang long exact sequence.
# For example, taking base_sphere = 4 and fiber_sphere = 3, we have a Hopf
# fibration of the form
#    S^3 -----> S^7
#                |
#                |
#                |
#                v
#               S^4
# and so we obtain the Serre spectral sequence in this case.
base_sphere_dim = 4
fiber_sphere_dim = 3
total_space = simplicial_complexes.Sphere(base_sphere_dim + fiber_sphere_dim)
fiber = simplicial_complexes.Sphere(fiber_sphere_dim)

def wang_filtration(s):
    if s in fiber.n_cells(s.dimension()):
        return 0
    return base_sphere_dim

print filtered_complex_SS(total_space, wang_filtration, filename='Hopf-S7-Serre-SS')


# Conf(2, manifold) ---> manifold
# is a Serre fibration
RP2 = simplicial_complexes.RealProjectivePlane()
manifold = RP2
square = manifold.product(manifold, rename_vertices=False)
# We use that the diagonal is a full subcomplex together with a lemma of Munkres
non_diag = square.generated_subcomplex([v for v in square.vertices() for (a, b) in [v] if a != b])

def serre_filtration(s):
    return len(set([a for (a, b) in s])) - 1


print filtered_complex_SS(non_diag, serre_filtration,
                          filename='Conf2-to-1-RP2-Serre-SS', spacing='[26em]', p_range=3, q_range=(0, 2))


# Suppose each vertex is given a weight; we may then filter a complex by declaring that each face
# sits in filtration degree equal to the sum of the weights of its vertices.
X = simplicial_complexes.SurfaceOfGenus(2)
# haphazard assignment of weights
weights = {v: i % 3 for i, v in enumerate(X.vertices())}
def haphazard_filtration(s):
    return sum([weights[v] for v in s])

print filtered_complex_SS(X, haphazard_filtration,
                          filename='Haphazard-Sigma-2', spacing='[7em]', p_range=6, q_range=(-3, 2))


Y = simplicial_complexes.Sphere(2).product(RP2)
weights = {v: i % 3 for i, v in enumerate(Y.vertices())}
print filtered_complex_SS(Y, haphazard_filtration,
                          filename='Haphazard-S2-times-RP2', spacing='[75em]',
                          p_range=10, q_range=(-5, 3), number_of_pages=7)
