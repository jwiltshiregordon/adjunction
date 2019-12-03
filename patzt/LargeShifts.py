from FJ import *

D = FI([0, 1, 2, 3])
C = ProductCategory(';', D, D)

# This is the left adjoint to concatenation
decomp = FI_decompositions


m = CatMat.from_string(ZZ, D, [2, 1, 0], '[[ab-ba],[b+8a],[*]]', [2])



m.pp()
print()


print(m.coker_at(5))

for i in range(3):
    tsh = FI_tail_shift(i)
    tshm = tsh(m)
    print(i, tshm.coker_at(1))

m0 = FI_tail_shift(0)(m)
m1 = FI_tail_shift(1)(m)
m2 = FI_tail_shift(2)(m)

for m in [m0, m1, m2]:
    m.cat.objects = [0, 1, 2, 3]

m0.pp()
print()
(+m0).pp()
print()
(+m1).pp()
print()
(+m2).pp()


