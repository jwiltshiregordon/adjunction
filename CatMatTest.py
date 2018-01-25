from CatMat import *
from PruneOld import *
from sage.all import vector, matrix


# The next three functions define the category of finite sets
def finOne(x):
    return '*' if x == 0 else ''.join([chr(v + 97) for v in range(x)])


def finHom(x, y):
    return ['*'] if x == 0 else [''.join([chr(v + 97) for v in w]) for w in
                                 tuple(itertools.product(*([range(0, y)] * x)))]


def finComp(x, f, y, g, z):
    return '*' if x == 0 else ''.join([tuple(g)[ord(c) - 97] for c in tuple(f)])


# Here we define the full subcategory on a few objects
fin = FiniteCategory([1, 2, 3], finOne, finHom, finComp)



au = CatMat.from_string(ZZ, fin, [2], '[[-cc]]', [3])
aui = get_inverse(au)
print aui
#view(LatexExpr(aui.to_latex()), tightpage=True)
sys.exit(0)

h0 = CatMat.from_string(ZZ, fin, [1], '[[b-a]]', [2])
f0 = h0
g0 = CatMat.from_string(ZZ, fin, [2], '[[ab+bc]]', [3])
t0 = CatMat.from_string(ZZ, fin, [2], '[[aa-bb+ab-ba]]', [2])
s0 = CatMat.from_string(ZZ, fin, [3], '[[aab+bbc-bba-ccb]]', [3])

y0 = CatMat.from_string(ZZ, fin, [1, 2], '[[a-b,a+b],[aa+bb,ab-ba]]', [2, 2])


h1 = g0
f1 = +f0
g1 = +g0

h2 = f1 >> (g0 * g1)

print (f1 * h2).data_vector
print (h1 * g1).data_vector

print

pc = ProductCategory(fin, fin)
pch = pc.hom((2, 2), (2, 2))
print pch
ff = pch[4]
gg = pch[5]
print ff
print gg
print pc.compose((2, 2), ff, (2, 2), gg, (2, 2))

sm = matrix(ZZ, 2, 3, [1, 2, 3, 4, 5, 6])

kp = CatMat.kronecker_product(y0, y0, y0)
print kp

view(LatexExpr(kp.to_latex()), tightpage=True)

# cm = +CatMat.kronecker_product(h0, h0)
# print cm
# a0 = g0 >> t0
# z0 = s0 << g0
# view(LatexExpr(z0.to_latex()))

sys.exit(0)

# Three little one-dim chain complexes
# Circle mod rotation
# line mod translation
# plane mod rotation

# Current plan
# Get it all set up as a homotopy colimit
# and compute it that way.

# It is true that you can compute from the other side
# and build a substitutional version to compute hocolim
# for a certain diagram shape by resolving its trivial rep

# I should program both of these options.

# cmblk = CatMat.block_diagonal([h0, h1, h2])
# view(LatexExpr(cmblk.to_latex()))

# svrt = rs1 >> cmy
# view(LatexExpr(rs1.to_latex() + ' \cdot ' + svrt.to_latex() + ' = ' + cmy.to_latex()))

# Generate every basis for ambient thing
# Generate every matrix that we might kernel by
# Generate basis for each joint degree
# Define the function circle_mod_rotation_cochains_law using solve_right:

# cmr means "circle mod rotation"

# We take care to omit the differential forms like xdx
# because these are coboundaries of forms like (1/2)x^2dx
# which we have not included in the complex
def affine_linear_differentials(n, k):
    return [(tuple(), tuple(c)) for c in Combinations(range(n), k)] + \
           [((c[i],), c[:i] + c[i + 1:]) for c in Combinations(range(n), k + 1) for i in range(k + 1)]

def cmr_ambient_basis(n, k):
    it = itertools.product(Permutations(range(n)), affine_linear_differentials(n, k))
    return [(tuple(perm), lin, exterior) for (perm, (lin, exterior)) in it]


def cmr_differential(n, k):
    rows = cmr_ambient_basis(n, k)
    cols = cmr_ambient_basis(n, k + 1)

    def entry(s, t):
        if s[0] != t[0]:
            return 0
        if len(s[1]) == 1 and len(t[1]) == 0:
            if all([p in t[2] for p in s[2]]) and s[1][0] in t[2]:
                return (-1) ** t[2].index(s[1][0])
            else:
                return 0
        else:
            return 0

    return matrix(ZZ, len(rows), len(cols), [entry(s, t) for s in rows for t in cols])


def circle_mod_rotation_cochains_law((x, f, y), (d, e)):
    pass

#
# print cmr_differential(3, 1).str()
# print cmr_differential(3, 1).rank()
# print
# print cmr_differential(3, 2).str()
# print cmr_differential(3, 2).rank()
# print
# print cmr_differential(3, 1).dimensions()
# print cmr_differential(3, 2).dimensions()
#
# #print cmr_ambient_basis(3,2)

