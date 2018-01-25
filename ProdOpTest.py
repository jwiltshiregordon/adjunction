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

print nonempty_faces
s2, s3, s1, s13, s12, s23, s123 = nonempty_faces

h0 = CatMat.from_string(ZZ, cat, [s1], '[[*,*]]', [s12, s13])
cm = +CatMat.kronecker_product(h0, h0.transpose())

view(LatexExpr(cm.transpose().to_latex()))

print cat.op().op().op() == cat.op()
cc = ProductCategory(cat, cat, cat)
ccc = ProductCategory(cat.op(), cat.op(), cat.op()).op()
print cc == ccc

print 3*3


