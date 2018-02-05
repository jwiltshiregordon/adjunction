from sage.all import matrix
from CatMat import *
from CatMat import TerminalCategory
from SimplicialComplexModel import *
from Prune import *

print
print





cx = simplicial_complex_model(SimplicialComplex([[1, 2], [1, 3], [1, 4]]))

#d0 = cx.differential(('*', '*'), (0,))
#d1 = cx.differential(('*', '*'), (1,))

#view(LatexExpr(d0.to_latex()), tightpage=True)
#view(LatexExpr(d1.to_latex()), tightpage=True)



cxp = prune_dg_module_on_poset(cx, (0, 8), verbose=True)




d0 = cxp.differential(('*', '*'), (0,))
d1 = cxp.differential(('*', '*'), (1,))


view(LatexExpr(d0.to_latex()), tightpage=True)
view(LatexExpr(d1.to_latex()), tightpage=True)

view(LatexExpr((d0 * d1).to_latex()), tightpage=True)

