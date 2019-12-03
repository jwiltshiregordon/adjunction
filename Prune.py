from sage.all import matrix, zero_matrix, block_diagonal_matrix, block_matrix, vector, identity_matrix
from CatMat import *


# TODO: Use Smith form to find a large invertible matrix after a suitable change of basis

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
def prune_dg_module(dgm, ab, verbose=False):
    a, b = ab
    tv = dgm.cat.objects[0]
    #diff_dict = {d:dgm.differential(tv, (d,)) for d in range(a - 1, b + 1)}
    diff_dict = {}
    for d in range(a - 1, b + 1):
        if verbose:
            print('computing differential in degree ' + str(d))
        diff_dict[d] = dgm.differential(tv, (d,))
    if verbose:
        print('original differentials computed')
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
                print([len(diff_dict[p].source) for p in range(a, b + 1)])

    def pruned_f_law(d_singleton, x, f, y):
        d = d_singleton[0]
        if d in range(a, b):
            return CatMat.identity_matrix(dgm.ring, dgm.cat, diff_dict[d].source)
        return CatMat.identity_matrix(dgm.ring, dgm.cat, [])

    def pruned_d_law(x, d_singleton):
        d = d_singleton[0]
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


def prune_dg_module_on_poset(dgm, ab, verbose=False, assume_sorted=False):
    a, b = ab
    tv = dgm.cat.objects[0]
    ring = dgm.ring
    cat = dgm.target_cat
    #diff_dict = {d:dgm.differential(tv, (d,)) for d in range(a - 1, b + 1)}
    diff_dict = {}
    for d in range(a - 1, b + 1):
        if verbose:
            print('computing differential in degree ' + str(d))
        diff_dict[d] = dgm.differential(tv, (d,))
    if verbose:
        print('original differentials computed')

    # Since we assume that cat is a poset,
    # we may convert the differentials to usual sagemath matrices
    # as long as we keep track of the row labels.
    #
    # triv = cat.trivial_representation(ring)
    # m_dict = {}
    # for d in range(a - 1, b + 1):
    #     m_dict[d] = triv(diff_dict[d])

    m_dict = {}
    for d in range(a - 1, b + 1):
        if verbose:
            print('Expanding the differential in degree ' + str(d))
        entries = []
        z = 0
        dv = diff_dict[d].data_vector
        source = diff_dict[d].source
        target = diff_dict[d].target
        for x in source:
            for y in target:
                if len(cat.hom(x, y)) == 1:
                    entries += [dv[z]]
                    z += 1
                else:
                    entries += [ring(0)]
        m_dict[d] = matrix(ring, len(source), len(target), entries)

    # This dict will keep track of the row labels
    m_source = {}
    # and dict will keep track of the target labels
    m_target = {}

    if assume_sorted:
        for d in range(a - 1, b + 1):
            for x in cat.objects:
                m_source[d, x] = 0
                m_target[d, x] = 0
                for y in diff_dict[d].source:
                    if x == y:
                        m_source[d, x] += 1
                for y in diff_dict[d].target:
                    if x == y:
                        m_target[d, x] += 1
            source_assumed = [x for x in cat.objects for _ in range(m_source[d, x])]
            if diff_dict[d].source != source_assumed:
                raise ValueError('This dgModule is not sorted in degree ' + str(d))
    else:
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

    # if verbose:
    #     for d in range(a - 1, b + 1):
    #         print
    #         print [m_source[d, x] for x in cat.objects]
    #         for r in m_dict[d]:
    #             print r
    #         print [m_target[d, x] for x in cat.objects]

    # Find the desired row- and column-operations
    # and change the labels (slightly prematurely)
    for d in range(a, b):
        for x in cat.objects:
            upper_left = m_dict[d][:m_source[d, x], :m_target[d, x]]
            if verbose:
                print('Computing Smith form of a matrix with dimensions ' + str(upper_left.dimensions()))
            dropped, sc, sr, tc, tr = prune_matrix(upper_left)
            if verbose:
                print('Dropping ' + str(dropped) + ' out of ' + str(m_source[d, x]) + \
                      ' occurrences of ' + str(x) + ' in degree ' + str(d - 1))
            m_target[d - 1, x] -= dropped
            m_source[d + 1, x] -= dropped
            cid = m_dict[d - 1].ncols() - sc.nrows()
            zul = zero_matrix(ring, sc.nrows(), cid)
            zlr = zero_matrix(ring, cid, sc.ncols())
            m_dict[d - 1] = m_dict[d - 1] * block_matrix([[zul, sc], [identity_matrix(ring, cid), zlr]])
            rid = m_dict[d + 1].nrows() - tr.ncols()
            zul = zero_matrix(ring, rid, tr.ncols())
            zlr = zero_matrix(ring, tr.nrows(), rid)
            m_dict[d + 1] = block_matrix([[zul, identity_matrix(ring, rid)], [tr, zlr]]) * m_dict[d + 1]

            row_rest = m_dict[d].nrows() - m_source[d, x]
            col_rest = m_dict[d].ncols() - m_target[d, x]

            m_dict[d] = block_diagonal_matrix([sr, identity_matrix(ring, row_rest)]) * m_dict[d]
            m_dict[d] = m_dict[d] * block_diagonal_matrix([tc, identity_matrix(ring, col_rest)])

            rest_rest = m_dict[d][m_source[d, x]:, m_target[d, x]:]
            rest_dropped = m_dict[d][m_source[d, x]:, :dropped]
            dropped_rest = m_dict[d][:dropped, m_target[d, x]:]
            rest_kept = m_dict[d][m_source[d, x]:, dropped:m_target[d, x]]
            kept_rest = m_dict[d][dropped:m_source[d, x], m_target[d, x]:]
            kept_kept = m_dict[d][dropped:m_source[d, x], dropped:m_target[d, x]]
            m_dict[d] = block_matrix(ring, [[rest_rest - rest_dropped * dropped_rest, rest_kept],
                                            [kept_rest,                               kept_kept]])
            m_source[d, x] -= dropped
            m_target[d, x] -= dropped

    for d in range(a - 1, b + 1):
        source = [x for x in cat.objects for _ in range(m_source[d, x])]
        target = [x for x in cat.objects for _ in range(m_target[d, x])]
        dv = [w for i, r in enumerate(m_dict[d].rows()) for j, w in enumerate(r)
              if len(cat.hom(source[i], target[j])) == 1]
        data_vector = vector(ring, dv)
        diff_dict[d] = CatMat(ring, cat, source, data_vector, target)

    def pruned_f_law(d_singleton, x, f, y):
        d = d_singleton[0]
        if d in range(a - 1, b + 1):
            return CatMat.identity_matrix(ring, cat, diff_dict[d].source)
        return dgm.module_in_degree((d,))(x, f, y)

    def pruned_d_law(x, d_singleton):
        d = d_singleton[0]
        if d in range(a - 1, b + 1):
            return diff_dict[d]
        return dgm.differential(x, (d,))

    return dgModule(TerminalCategory, ring, pruned_f_law, [pruned_d_law], target_cat=cat)
