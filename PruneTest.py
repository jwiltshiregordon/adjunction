from sage.all import *
from CatMat import *
from CatMat import TerminalCategory
from SimplicialComplexModel import *
from PruneOld import *

print

print


cx = simplicial_complex_model(SimplicialComplex([[1, 2]]))



cxp = prune_dg_module(cx, (0, 2))


d0 = cxp.differential(('*', '*'), (0,))
d1 = cxp.differential(('*', '*'), (1,))


view(LatexExpr(d0.to_latex()), tightpage=True)
view(LatexExpr(d1.to_latex()), tightpage=True)



