from CatMat import *
from sage.all import vector, matrix

X = SimplicialComplex([[1,2,3]])


def catOne(x):
    return '*'

def catHom(x, y):
    if x.is_face(y):
        return ['*']
    return []

def catComp(x, f, y, g, z):
    return '*'


nonempty_faces = [f for f in X.face_iterator() if f.dimension() != -1]
cat = FiniteCategory(nonempty_faces, catOne, catHom, catComp)

def tarOne(x):
    return '*'

def tarHom(x, y):
    if x <= y:
        return ['*']
    else:
        return []

def tarComp(x, f, y, g, z):
    return '*'

tar = FiniteCategory([0, 1, 2], tarOne, tarHom, tarComp)

print nonempty_faces

def law(x, f, y):
    return matrix(ZZ, 1, 1, [1])

rep = MatrixRepresentation(cat, ZZ, law)

# cm = rep.presentation()
# view(LatexExpr(cm.to_latex()))



def ex_law(x, f, y):
    rk_dict = {Simplex([1]): [0],
               Simplex([2]): [1],
               Simplex([3]): [2],
               Simplex([2, 3]): [2],
               Simplex([1, 3]): [1],
               Simplex([1, 2]): [0],
               Simplex([1, 2, 3]): [0]}
    if x == Simplex([1]):
        if y == Simplex([1, 2]):
            return CatMat(ZZ, tar.op(), rk_dict[x], vector(ZZ, [-1]), rk_dict[y])
    if x == Simplex([2]):
        if y == Simplex([1, 2]):
            return CatMat(ZZ, tar.op(), rk_dict[x], vector(ZZ, [2]), rk_dict[y])
    if x == Simplex([3]):
        if y == Simplex([2, 3]):
            return CatMat(ZZ, tar.op(), rk_dict[x], vector(ZZ, [4]), rk_dict[y])
        if y == Simplex([1, 3]):
            return CatMat(ZZ, tar.op(), rk_dict[x], vector(ZZ, [9]), rk_dict[y])
    if x == Simplex([2, 3]):
        if y == Simplex([1, 2, 3]):
            return CatMat(ZZ, tar.op(), rk_dict[x], vector(ZZ, [9]), rk_dict[y])
    if x == Simplex([1, 3]):
        if y == Simplex([1, 2, 3]):
            return CatMat(ZZ, tar.op(), rk_dict[x], vector(ZZ, [4]), rk_dict[y])

    if x == y:
        return CatMat.identity_matrix(ZZ, tar.op(), rk_dict[x])
    else:
        return CatMat.zero_matrix(ZZ, tar.op(), rk_dict[x], rk_dict[y])

ex_rep = MatrixRepresentation(cat, ZZ, ex_law, target_cat=tar.op())
print


cm = ex_rep.presentation()
view(LatexExpr(cm.to_latex()))
