from CatMat import *
from Prune import *
from random import shuffle
import time

# Implementation of the spectral sequence of a filtered complex.
# We use the method of exact couples.
initial_prune = True
initial_prune_verbose = False
ongoing_prune = True
show_aux = False
show_timing = True
start = time.time()

base_sphere = 4
fiber_sphere = 3
manifold = simplicial_complexes.Sphere(base_sphere + fiber_sphere)
fiber = simplicial_complexes.Sphere(fiber_sphere)
steps = base_sphere
Xtop = manifold
print

# Conf(2, manifold) ---> manifold
# is a Serre fibration
#manifold = simplicial_complexes.SurfaceOfGenus(1)
#steps = manifold.dimension()
#square = manifold.product(manifold, rename_vertices=False)
#non_diag = square.generated_subcomplex([v for v in square.vertices() for (a, b) in [v] if a != b])
#verts = list(non_diag.vertices())
#Xtop = non_diag

def serre_filtration(s):
    return len(set([a for (a, b) in s])) - 1


def wang_filtration(s):
    if s in fiber.n_cells(s.dimension()):
        return 0
    return steps
filtration = wang_filtration
#filtration = serre_filtration
#def X(p):
#     if p <= -1:
#         return SimplicialComplex([])
#     def serre_filtration(s):
#         return len(set([a for (a, b) in s])) <= p + 1 and (Simplex(s) in non_diag.n_faces(len(s) - 1))
#     return SimplicialComplex(from_characteristic_function=(serre_filtration, verts))



# +m
def syz(m):
    return CatMat.matrix_step_right(m)

# a >> b
def solve_right(a, b):
    return CatMat.matrix_solve_right(a, b)


def sgn(n):
    return 1 if n % 2 == 0 else -1


def show_coker(m):
    return str(ChainComplex({-1: m}).homology(0))


def simplify_cokernel(m):
    d, w, _ = m.smith_form()
    u = matrix(ZZ, w.inverse())
    diagonal_entries = d.diagonal()
    units = diagonal_entries.count(1)
    zeros = diagonal_entries.count(0)
    torsions = len(diagonal_entries) - zeros - units

    b = d[units:, units:units + torsions]
    frees = b.nrows() - torsions
    ui = u[:, units:]
    pw = w[units:, :]
    summands = diagonal_entries[units:units + torsions] + frees * [0]
    tex = '\\oplus'.join(['\\mathbb{Z}' if x == 0 else '\\mathbb{Z}/' + str(x) for x in summands])
    return ui, b, pw, summands, LatexExpr(tex)


def Xfaces(p, n):
    return list(X(p)._n_cells_sorted(n)) if n != -1 else []


def N_one(x):
    return '*'
def N_hom(x, y):
    return ['*'] if x <= y else []
def N_comp(x, f, y, g, z):
    return '*'

N = FiniteCategory(range(steps + 1), N_one, N_hom, N_comp)


def d_law(x, (d, )):
    rows = Xtop._n_cells_sorted(d) if d >= 0 else []
    cols = Xtop._n_cells_sorted(d + 1) if d + 1 >= 0 else []
    row_degrees = [filtration(r) for r in rows]
    col_degrees = [filtration(c) for c in cols]
    entries = [sum([sgn(i) for i, f in enumerate(c.faces()) if r == f]) for r, rr in zip(rows, row_degrees)
               for c, cc in zip(cols, col_degrees)
               if rr <= cc]
    return CatMat(ZZ, N, row_degrees, vector(ZZ, entries), col_degrees)

def f_law((d, ), x, f, y):
    rows = Xtop._n_cells_sorted(d) if d >= 0 else []
    degrees = [filtration(r) for r in rows]
    return CatMat.identity_matrix(ZZ, N, degrees)

dgm_big = dgModule(TerminalCategory, ZZ, f_law, [d_law], target_cat=N)
top_deg = 100
if initial_prune:
    dgm = prune_dg_module_on_poset(dgm_big, (0, top_deg), verbose=initial_prune_verbose)
else:
    dgm = dgm_big


def f_law((d, ), x, f, y):
    f_mat = CatMat.from_string(ZZ, N, [x], '[[' + f + ']]', [y])
    return CatMat.matrix_postcompose(dgm.rank((-d,), '*'), f_mat)


def d_law(x, (d, )):
    return CatMat.matrix_precompose(dgm.differential('*', (-d - 1,)), [x])


dgm_explode = dgModule(N, ZZ, f_law, [d_law])


def pi(p, n):
    #rows = Xfaces(p, n)
    #cols = Xfaces(p, n) + Xfaces(p - 1, n - 1)
    #entries = [1 if r == c else 0 for r in rows for c in cols]
    #return matrix(ZZ, len(rows), len(cols), entries)
    pn = dgm_explode.rank((-n,), p)
    pnm = dgm_explode.rank((-n + 1,), p - 1)
    return block_matrix([[identity_matrix(ZZ, pn), zero_matrix(ZZ, pn, pnm)]])


def phi(p, n):
    #rows = Xfaces(p - 1, n)
    #cols = Xfaces(p, n)
    #entries = [1 if r == c else 0 for r in rows for c in cols]
    #return matrix(ZZ, len(rows), len(cols), entries)
    return dgm_explode.module_in_degree((-n,))(p - 1, '*', p)


def iota(p, n):
    #rows = Xfaces(p + 1, n + 1) + Xfaces(p, n)
    #cols = Xfaces(p, n)
    #entries = [1 if r == c else 0 for r in rows for c in cols]
    #return matrix(ZZ, len(rows), len(cols), entries)
    pnp = dgm_explode.rank((-n - 1,), p + 1)
    pn = dgm_explode.rank((-n,), p)
    return block_matrix([[zero_matrix(ZZ, pnp, pn)], [identity_matrix(ZZ, pn)]])


def delta(p, n):
    #rows = Xfaces(p, n + 1)
    #cols = Xfaces(p, n)
    #entries = [sum([sgn(k) if f == c else 0 for k, f in enumerate(r.faces())]) for r in rows for c in cols]
    #return matrix(ZZ, len(rows), len(cols), entries)
    return dgm_explode.differential(p, (-n - 1,))


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

if ongoing_prune:
    E_prune_dict = {}
    C_prune_dict = {}

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
    else:
        ret = block_matrix([[W(p, q, r - 1), L(p, q, r - 1)]])
    if ongoing_prune and r >= 1:
        E_prune_dict[p, q, r] = simplify_cokernel(ret)
        ret = E_prune_dict[p, q, r][1]
    E_dict[p, q, r] = ret
    return ret


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
    if ongoing_prune and r >= 1:
        C_prune_dict[p, q, r] = simplify_cokernel(ret)
        ret = C_prune_dict[p, q, r][1]
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
    if ongoing_prune and r >= 1:
        E(p, q, r)
        C(p, q, r)
        uiE = E_prune_dict[p, q, r][0]
        pwC = C_prune_dict[p, q, r][2]
        ret = pwC * ret * uiE
    F_dict[p, q, r] = ret
    return ret


def G(p, q, r):
    if (p, q, r) in G_dict:
        return G_dict[p, q, r]
    if r == 1:
        ret = solve_right(zeta(p - 1, p + q), phi(p, p + q) * zeta(p, p + q))
    else:
        ret = G(p + 1, q - 1, r - 1)
    if ongoing_prune and r >= 1:
        C(p, q, r)
        C(p - 1, q + 1, r)
        uiC = C_prune_dict[p, q, r][0]
        pwC = C_prune_dict[p - 1, q + 1, r][2]
        ret = pwC * ret * uiC
    G_dict[p, q, r] = ret
    return ret


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
    if ongoing_prune and r >= 1:
        C(p, q, r)
        E(p + r, q - r + 1, r)
        uiC = C_prune_dict[p, q, r][0]
        pwE = E_prune_dict[p + r, q - r + 1, r][2]
        ret = pwE * ret * uiC
    H_dict[p, q, r] = ret
    return ret

print 'Initial prune: ' + str(initial_prune)
print 'Ongoing prune: ' + str(ongoing_prune)
print time.time() - start
for r in range(1, 6):
    print 'E_' + str(r) + ' page:'
    for q in range(6, -6, -1):
        print ('q = ' + str(q) + ': ').ljust(10),
        for p in range(8):
            print show_coker(E(p, q, r)).ljust(10),
        print
    print time.time() - start
    if show_aux:
        print 'aux'
        for q in range(6, -6, -1):
            print ('q = ' + str(q) + ': ').ljust(10),
            for p in range(8):
                print show_coker(C(p, q, r)).ljust(10),
            print
        print time.time() - start
        print
