from CatMat import *

# Implementation of the spectral sequence of a filtered complex.

cyclic = [1, 2, 3, 4, 1]
X0 = SimplicialComplex([[1]])
X1 = SimplicialComplex([[1, 2], [2, 3], [3, 4], [1, 4]])
X2 = SimplicialComplex([[cyclic[i], cyclic[i + 1], j] for i in range(4) for j in [5, 6]])

def X(p):
    if p <= -1:
        return SimplicialComplex([])
    if p == 0:
        return X0
    if p == 1:
        return X1
    if p >= 2:
        return X2

# +m
def syz(m):
    return CatMat.matrix_step_right(m)

# a >> b
def solve_right(a, b):
    return CatMat.matrix_solve_right(a, b)


def sgn(n):
    return 1 if n % 2 == 0 else -1


def show_coker(m):
    return str(ChainComplex({-1: m}).homology(0)).ljust(10)


def Xfaces(p, n):
    return list(X(p)._n_cells_sorted(n)) if n != -1 else []


def pi(p, n):
    rows = Xfaces(p, n)
    cols = Xfaces(p, n) + Xfaces(p - 1, n - 1)
    entries = [1 if r == c else 0 for r in rows for c in cols]
    return matrix(ZZ, len(rows), len(cols), entries)


def phi(p, n):
    rows = Xfaces(p - 1, n)
    cols = Xfaces(p, n)
    entries = [1 if r == c else 0 for r in rows for c in cols]
    return matrix(ZZ, len(rows), len(cols), entries)


def iota(p, n):
    rows = Xfaces(p + 1, n + 1) + Xfaces(p, n)
    cols = Xfaces(p, n)
    entries = [1 if r == c else 0 for r in rows for c in cols]
    return matrix(ZZ, len(rows), len(cols), entries)


def delta(p, n):
    rows = Xfaces(p, n + 1)
    cols = Xfaces(p, n)
    entries = [sum([sgn(k) if f == c else 0 for k, f in enumerate(r.faces())]) for r in rows for c in cols]
    return matrix(ZZ, len(rows), len(cols), entries)


def epsilon(p, n):
    dp = delta(p, n)
    dpm = delta(p - 1, n - 1)
    zz = zero_matrix(ZZ, dp.nrows(), dpm.ncols())
    return block_matrix([[dp, zz], [sgn(n) * phi(p, n), dpm]])


for p in range(-10, 10):
    for n in range(-10, 10):
        # Check that these compose
        phi(p, n) * pi(p, n)
        iota(p, n) * pi(p, n)
        pi(p + 1, n + 1) * iota(p, n)
        # Check that these commute
        assert delta(p - 1, n) * phi(p, n) == phi(p, n + 1) * delta(p, n)
        assert delta(p, n) * pi(p, n) == pi(p, n + 1) * epsilon(p, n)
        assert epsilon(p + 1, n + 1) * iota(p, n) == iota(p, n + 1) * delta(p, n)


def zeta(p, n):
    return syz(delta(p, n))


def xi(p, n):
    return syz(epsilon(p, n))



#D(p, q, r) = H(p, q, r) * F(p, q, r)
#Z(p, q, r) = [0  1] * ( +[E(p+r, q-r+1, r)  D(p, q, r) ])
#Y(p, q, r) = [ E(p, q, r)  Z(p, q, r) ]
#W(p, q, r) = [0  1] * ( +Y(p, q, r) )
#L(p, q, r) = [0  1] * ( Y >> D(p-r, q+r-1, r) )
D_dict = {}
Z_dict = {}
W_dict = {}
L_dict = {}

E_dict = {}
C_dict = {}
F_dict = {}
G_dict = {}
H_dict = {}

def D(p, q, r):
    if (p, q, r) in D_dict:
        return D_dict[p, q, r]
    ret = H(p, q, r) * F(p, q, r)
    D_dict[p, q, r] = ret
    return ret


def Z(p, q, r):
    if (p, q, r) in Z_dict:
        return Z_dict[p, q, r]
    Em = E(p + r, q - r + 1, r)
    Dm = D(p, q, r)
    proj = block_matrix([[zero_matrix(ZZ, Dm.ncols(), Em.ncols()), identity_matrix(ZZ, Dm.ncols())]])
    blk = block_matrix([[Em, Dm]])
    ret = proj * syz(blk)
    Z_dict[p, q, r] = ret
    return ret


def Y(p, q, r):
    return block_matrix([[E(p, q, r), Z(p, q, r)]])


def W(p, q, r):
    if (p, q, r) in W_dict:
        return W_dict[p, q, r]
    ec = E(p, q, r).ncols()
    zc = Z(p, q, r).ncols()
    proj = block_matrix([[zero_matrix(ZZ, zc, ec), identity_matrix(ZZ, zc)]])
    ret = proj * syz(Y(p, q, r))
    W_dict[p, q, r] = ret
    return ret


def L(p, q, r):
    if (p, q, r) in L_dict:
        return L_dict[p, q, r]
    ec = E(p, q, r).ncols()
    zc = Z(p, q, r).ncols()
    proj = block_matrix([[zero_matrix(ZZ, zc, ec), identity_matrix(ZZ, zc)]])
    ret = proj * solve_right(Y(p, q, r), D(p - r, q + r - 1, r))
    L_dict[p, q, r] = ret
    return ret


def E(p, q, r):
    if (p, q, r) in E_dict:
        return E_dict[p, q, r]
    if r == 1:
        xippq = xi(p, p + q)
        ret = block_matrix([[syz(xippq), solve_right(xippq, epsilon(p, p + q - 1))]])
        E_dict[p, q, r] = ret
        return ret
    return block_matrix([[W(p, q, r - 1), L(p, q, r - 1)]])


def C(p, q, r):
    if (p, q, r) in C_dict:
        return C_dict[p, q, r]
    if r == 1:
        zppq = zeta(p, p + q)
        ret = block_matrix([[syz(zppq), solve_right(zppq, delta(p, p + q - 1))]])
    else:
        cc = C(p, q, r - 1).ncols()
        gc = G(p + 1, q - 1, r - 1).ncols()
        proj = block_matrix([[zero_matrix(ZZ, gc, cc), identity_matrix(ZZ, gc)]])
        CG = block_matrix([[C(p, q, r - 1), G(p + 1, q - 1, r - 1)]])
        ret = block_matrix([[C(p + 1, q - 1, r - 1), proj * syz(CG)]])
    C_dict[p, q, r] = ret
    return ret


def F(p, q, r):
    if (p, q, r) in F_dict:
        return F_dict[p, q, r]
    if r == 1:
        ret = solve_right(zeta(p, p + q), pi(p, p + q) * xi(p, p + q))
    else:
        cc = C(p, q, r - 1).ncols()
        gc = G(p + 1, q - 1, r - 1).ncols()
        proj = block_matrix([[zero_matrix(ZZ, gc, cc), identity_matrix(ZZ, gc)]])
        CG = block_matrix([[C(p, q, r - 1), G(p + 1, q - 1, r - 1)]])
        ret = proj * solve_right(CG, F(p, q, r - 1) * Z(p, q, r - 1))
    F_dict[p, q, r] = ret
    return ret


def G(p, q, r):
    if (p, q, r) in G_dict:
        return G_dict[p, q, r]
    if r == 1:
        ret = solve_right(zeta(p - 1, p + q), phi(p, p + q) * zeta(p, p + q))
        G_dict[p, q, r] = ret
        return ret
    return G(p + 1, q - 1, r - 1)


def H(p, q, r):
    if (p, q, r) in H_dict:
        return H_dict[p, q, r]
    if r == 1:
        ret = solve_right(xi(p + 1, p + q + 1), iota(p, p + q) * zeta(p, p + q))
    else:
        ec = E(p + r, q - r + 1, r - 1).ncols()
        zc = Z(p + r, q - r + 1, r - 1).ncols()
        proj = block_matrix([[zero_matrix(ZZ, zc, ec), identity_matrix(ZZ, zc)]])
        ret = proj * solve_right(Y(p + r, q - r + 1, r - 1), H(p + 1, q - 1, r - 1))
    H_dict[p, q, r] = ret
    return ret


for r in range(1, 4):
    print 'E_' + str(r) + ' page:'
    for q in range(5, -5, -1):
        print ('q = ' + str(q) + ': ').ljust(10),
        for p in range(7):
            print show_coker(E(p, q, r)),
        print
    print

