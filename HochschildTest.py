from CatMat import *
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
fin = FiniteCategory([1, 2], finOne, finHom, finComp)

# Build the identity functor on fin
# and then ask for its presentation?

def id_law(x, f, y):
    return CatMat.from_string(QQ, fin, [x], '[[' + f + ']]', [y])

id_rep = MatrixRepresentation(fin, QQ, id_law, target_cat=fin)
print


cm = id_rep.presentation()
view(LatexExpr(cm.to_latex()))
