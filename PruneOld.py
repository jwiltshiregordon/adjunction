from sage.all import *
from CatMat import *


# Returns either None or the inverse of a CatMat
def get_inverse(cm):
    source_id = CatMat.identity_matrix(cm.ring, cm.cat, cm.source)
    target_id = CatMat.identity_matrix(cm.ring, cm.cat, cm.target)
    try:
        inv = cm.solve_right(source_id)
        if cm * inv == target_id:
            return inv
        else:
            return None
    except ValueError:
        return None


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


def row_operation(i, inv, colj):
    sources = [[x] for p, x in enumerate(colj.source) if p != i]
    targets = [[y] for y in colj.source]
    table = []
    for p, x in enumerate(colj.source):
        if p != i:
            row = []
            for q, y in enumerate(colj.source):
                if p == q:
                    row += [CatMat.identity_matrix(colj.ring, colj.cat, [x])]
                elif q == i:
                    row += [colj.ring(-1) * colj.row(p) * inv]
                else:
                    row += [CatMat.zero_matrix(colj.ring, colj.cat, [x], [y])]
            table += [row]
    return CatMat.block_matrix(table, ring=colj.ring, cat=colj.cat, sources=sources, targets=targets)


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
            # These two operations should be performed in the opposite order
            diff_dict[d] = row_operation(i, inv, colj) * diff_dict[d]
            cur_cols = diff_dict[d].columns()
            drop_col_j = cur_cols[:j] + cur_cols[j + 1:]
            diff_dict[d] = CatMat.block_matrix([drop_col_j], ring=dgm.ring, cat=dgm.target_cat,
                                               sources=[diff_dict[d].source])
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

