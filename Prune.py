from sage.all import matrix
from CatMat import *



# This code currently assumes that no two objects are isomorphic
# i.e. that the category is skeletal
def find_invertible_entry(cm):
    for i, x in enumerate(cm.source):
        for j, y in enumerate(cm.target):
            if x == y: # Here is the skeletal assumption
                entry = cm.row(i).column(j)
                inv = entry.inverse()
                if not (inv is None):
                    return i, j, inv
    return None


# Gives a smaller representative in the derived category
# Currently dgm has a single differential
# and its source cat must be trivial
# and [a, b] gives an interval in which dgm is supported
def prune_dg_module(dgm, (a, b), verbose=False):
    tv = dgm.cat.objects[0]
    #diff_dict = {d:dgm.differential(tv, (d,)) for d in range(a - 1, b + 1)}
    diff_dict = {}
    for d in range(a - 1, b + 1):
        if verbose:
            print 'computing differential in degree ' + str(d)
        diff_dict[d] = dgm.differential(tv, (d,))
    if verbose:
        print 'original differentials computed'
    for d in range(a, b):
        while True:
            invertible_entry = find_invertible_entry(diff_dict[d])
            if invertible_entry is None:
                break
            i, j, inv = invertible_entry
            colj = diff_dict[d].column(j)
            prev_cols = diff_dict[d - 1].columns()
            drop_col_i = prev_cols[:i] + prev_cols[i + 1:]
            diff_dict[d - 1] = CatMat.block_matrix([drop_col_i], ring=dgm.ring, cat=dgm.target_cat,
                                              sources=[diff_dict[d - 1].source])
            next_rows = diff_dict[d + 1].rows()
            drop_row_j = next_rows[:j] + next_rows[j + 1:]
            diff_dict[d + 1] = CatMat.block_matrix([[r] for r in drop_row_j], ring=dgm.ring, cat=dgm.target_cat,
                                              targets=[diff_dict[d + 1].target])
            cur_cols = diff_dict[d].columns()
            drop_col_j = cur_cols[:j] + cur_cols[j + 1:]
            diff_dict[d] = CatMat.block_matrix([drop_col_j], ring=dgm.ring, cat=dgm.target_cat,
                                               sources=[diff_dict[d].source])
            cur_rows = diff_dict[d].rows()
            cur_row_i = cur_rows[i]
            new_rows = []
            for p, x in enumerate(colj.source):
                if p != i:
                    row = cur_rows[p] + dgm.ring(-1) * colj.row(p) * inv * cur_row_i
                    new_rows += [row]
            diff_dict[d] = CatMat.block_matrix([[r] for r in new_rows], ring=dgm.ring, cat=dgm.target_cat,
                                               targets=[diff_dict[d].target])


            if verbose:
                print [len(diff_dict[p].source) for p in range(a, b + 1)]

    def pruned_f_law((d,), x, f, y):
        if d in range(a, b):
            return CatMat.identity_matrix(dgm.ring, dgm.cat, diff_dict[d].source)
        return CatMat.identity_matrix(dgm.ring, dgm.cat, [])

    def pruned_d_law(x, (d,)):
        if d in range(a - 1, b + 1):
            return diff_dict[d]
        return CatMat.zero_matrix(dgm.ring, dgm.cat, [], [])

    return dgModule(TerminalCategory, dgm.ring, pruned_f_law, [pruned_d_law], target_cat=dgm.target_cat)



# In a poset, there is a much faster pruning algorithm available
# Look at the blocks where the row-label matches the column label
# find an invertible submatrix in there using usual linear algebra

# Here m is a sagemath matrix over ZZ or a field
# and our job is to find row ops and col ops that remove as many ZZ --- 1 ---> ZZ summands as possible.
# The function returns x, y so that x * m * y is rectangular diagonal, and with all leading 1's deleted.
# The kernel and cokernel of x * m * y should be isomorphic to those of m.


# print x.inverse() * d * y.inverse()
def prune_matrix(m):
    d, x, y = m.smith_form()
    ring = m.base_ring()
    p = len([i for i in range(min(*d.dimensions())) if d[i, i] == ring(1)])
    return p, matrix(ring, x.inverse())[:, p:], x, y, matrix(ring, y.inverse())[p:, :]


def prune_dg_module_on_poset(dgm, (a, b), verbose=False):
    tv = dgm.cat.objects[0]
    ring = dgm.ring
    cat = dgm.target_cat
    #diff_dict = {d:dgm.differential(tv, (d,)) for d in range(a - 1, b + 1)}
    diff_dict = {}
    for d in range(a - 1, b + 1):
        if verbose:
            print 'computing differential in degree ' + str(d)
        diff_dict[d] = dgm.differential(tv, (d,))
    if verbose:
        print 'original differentials computed'

    # Since we assume that cat is a poset,
    # we may convert the differentials to usual sagemath matrices
    # as long as we keep track of the row labels.
    #
    triv = cat.trivial_representation(ring)
    m_dict = {}
    for d in range(a - 1, b + 1):
        m_dict[d] = triv(diff_dict[d])
    # This dict will keep track of the row labels
    m_source = {}
    # and dict will keep track of the target labels
    m_target = {}

    # Time to sort the rows
    for d in range(a - 1, b + 1):
        targ = m_dict[d].ncols()
        rows = m_dict[d].rows()
        new_rows = []
        for x in cat.objects:
            m_source[d, x] = 0
            for i, r in enumerate(rows):
                if diff_dict[d].source[i] == x:
                    m_source[d, x] += 1
                    new_rows += [r]
        if len(new_rows) == 0:
            m_dict[d] = zero_matrix(ring, 0, targ)
        else:
            m_dict[d] = block_matrix(ring, [[matrix(ring, 1, targ, list(r))] for r in new_rows])

    # and now the columns
    for d in range(a - 1, b + 1):
        sour = m_dict[d].nrows()
        cols = m_dict[d].columns()
        new_cols = []
        for x in cat.objects:
            m_target[d, x] = 0
            for i, c in enumerate(cols):
                if diff_dict[d].target[i] == x:
                    m_target[d, x] += 1
                    new_cols += [c]
        if len(new_cols) == 0:
            m_dict[d] = zero_matrix(ring, sour, 0)
        else:
            m_dict[d] = block_matrix(ring, [[matrix(ring, sour, 1, list(c)) for c in new_cols]])

    if verbose:
        for d in range(a - 1, b + 1):
            print
            print [m_source[d, x] for x in cat.objects]
            for r in m_dict[d]:
                print r
            print [m_target[d, x] for x in cat.objects]

    # Find the desired row- and column-operations
    # and change the labels (slightly prematurely)
    for d in range(a, b):
        scop = {}
        srop = {}
        tcop = {}
        trop = {}
        eblock = {}
        dropped = {}
        zs = 0
        zt = 0
        for x in cat.objects:
            eblock[x] = m_dict[d][zs:zs + m_source[d, x], zt:zt + m_target[d, x]]
            zs += m_source[d, x]
            zt += m_target[d, x]
        for x in cat.objects:
            if verbose:
                print 'Computing Smith form for a matrix with dimensions ' + str(eblock[x].dimensions()) + '...'
            dropped[x], scop[x], srop[x], tcop[x], trop[x] = prune_matrix(eblock[x])
            if verbose:
                print 'Complete. Dropping ' + str(dropped)
            m_target[d - 1, x] -= dropped[x]
            #m_source[d, x] -= dropped[x]
            #m_target[d, x] -= dropped[x]
            m_source[d + 1, x] -= dropped[x]
        sc = block_diagonal_matrix([scop[x] for x in cat.objects])
        sr = block_diagonal_matrix([srop[x] for x in cat.objects])
        tc = block_diagonal_matrix([tcop[x] for x in cat.objects])
        tr = block_diagonal_matrix([trop[x] for x in cat.objects])

        m_dict[d - 1] = m_dict[d - 1] * sc
        m_dict[d] = sr * m_dict[d] * tc
        m_dict[d + 1] = tr * m_dict[d + 1]

        # So now we have a bunch of identity matrices in m_dict[d] but they are all spread out
        # time to put them all at the front.
        #
        # Start by moving the rows
        new_rows = []
        old_rows = m_dict[d].rows()
        zs = 0
        for x in cat.objects:
            new_rows += old_rows[zs:zs + dropped[x]]
            zs += m_source[d, x]
        zs = 0
        for x in cat.objects:
            new_rows += old_rows[zs + dropped[x]:zs + m_source[d, x]]
            zs += m_source[d, x]
        if len(new_rows) == 0:
            # No need to rebuild it in this case
            # since it is fine already!
            pass
        else:
            targ = m_dict[d].ncols()
            m_dict[d] = block_matrix(ring, [[matrix(ring, 1, targ, list(r))] for r in new_rows])
        #
        # And now the columns
        new_cols = []
        old_cols = m_dict[d].columns()
        zt = 0
        for x in cat.objects:
            new_cols += old_cols[zt:zt + dropped[x]]
            zt += m_target[d, x]
        zt = 0
        for x in cat.objects:
            new_cols += old_cols[zt + dropped[x]:zt + m_target[d, x]]
            zt += m_target[d, x]
        if len(new_cols) == 0:
            # No need to rebuild it in this case
            # since it is fine already!
            pass
        else:
            sour = m_dict[d].nrows()
            m_dict[d] = block_matrix(ring, [[matrix(ring, sour, 1, list(c)) for c in new_cols]])

        z = 0
        for x in cat.objects:
            z += dropped[x]

        m_dict[d] = m_dict[d][z:, z:] - m_dict[d][z:, :z] * m_dict[d][:z, z:]

        for x in cat.objects:
            m_source[d, x] -= dropped[x]
            m_target[d, x] -= dropped[x]


    for d in range(a - 1, b + 1):
        source = [x for x in cat.objects for _ in range(m_source[d, x])]
        target = [x for x in cat.objects for _ in range(m_target[d, x])]
        dv = [w for i, r in enumerate(m_dict[d].rows()) for j, w in enumerate(r)
              if len(cat.hom(source[i], target[j])) == 1]
        data_vector = vector(ring, dv)
        diff_dict[d] = CatMat(ring, cat, source, data_vector, target)

    def pruned_f_law((d,), x, f, y):
        if d in range(a - 1, b + 1):
            return CatMat.identity_matrix(ring, cat, diff_dict[d].source)
        return dgm.module_in_degree((d,))(x, f, y)

    def pruned_d_law(x, (d,)):
        if d in range(a - 1, b + 1):
            return diff_dict[d]
        return dgm.differential((d,))

    return dgModule(TerminalCategory, ring, pruned_f_law, [pruned_d_law], target_cat=cat)
