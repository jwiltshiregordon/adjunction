from FJ import *

d = 2
D, Xi, solve_to_Xi = FJ(d)
C = FI()

print(D)
#D.test()

m = CatMat.identity_matrix(ZZ, C, [2, 2, 2, 3])
o = CatMat.from_string(ZZ, D, [2], '[[t^0{a,b}]]', [0])


mo = CatMat.kronecker_product(m.transpose(), o)
mo.pp()

print
print(Xi(mo))

o = CatMat.from_string(ZZ, D, [2], '[[5t^0{a,b}]]', [0])
print(o.coker_at(0))
print(o.coker_at(1))
print(o.coker_at(2))

print
o = CatMat.from_string(ZZ, D, [2], '[[t^0ab-t^0ba]]', [2])
print(o.coker_at(0))
print(o.coker_at(1))
print(o.coker_at(2))

print(D.hom(0, 2))


res = FJ_restrict(d, d - 2)
#res.test()

sh = FJ_shift(d)
#sh.test()

der = FJ_derivative(d)
#der.test()

lead = FJ_leading(d)
#lead.test()
