
# This class is for the computation and storage of the matrices
# that arise in the bilinearized composition law of a category


class StructureMatricesOLD(object):
    def __init__(self, finite_category, ring):
        self.cat = finite_category
        self.ring = ring
        self.ractDict = {}
        self.lactDict = {}
        self.prodDict = {}
        self.resolution_of_trivial_module = {}

    def ract(self, x, y, f, z):
        if (x, y, f, z) in self.ractDict:
            return self.ractDict[(x, y, f, z)]
        rows = self.cat.hom(x, y)
        cols = self.cat.hom(x, z)
        ret = matrix(self.ring, len(rows), len(cols), [self.ring(1) if self.cat.compose(x, r, y, f, z) == c
                                                        else self.ring(0) for r in rows for c in cols])
        self.ractDict[(x, y, f, z)] = ret
        return ret

    def lact(self, x, f, y, z):
        if (x, f, y, z) in self.lactDict:
            return self.lactDict[(x, f, y, z)]
        rows = self.cat.hom(y, z)
        cols = self.cat.hom(x, z)
        ret = matrix(self.ring, len(rows), len(cols), [self.ring(1) if self.cat.compose(x, f, y, r, z) == c
                                                        else self.ring(0) for r in rows for c in cols])
        self.lactDict[(x, f, y, z)] = ret
        return ret

    def prod(self, x, f, z, y):
        if (x, f, z, y) in self.prodDict:
            return self.prodDict[(x, f, z, y)]
        rows = self.cat.hom(x, y)
        cols = self.cat.hom(y, z)
        ret = matrix(self.ring, len(rows), len(cols), [self.ring(1) if self.cat.compose(x, r, y, c, z) == f
                                                       else self.ring(0) for r in rows for c in cols])
        self.prodDict[(x, f, z, y)] = ret
        return ret

    def free_right_module(self, degrees):
        if not (type(degrees) == list):
            return self.free_right_module([degrees])

        def law(x, f, y):
            ret = matrix(self.ring, 0, 0, [])
            for d in degrees:
                ret = ret.block_sum(self.ract(d, x, f, y))
            return ret

        return PointwiseFreeRightModule(self, law)

    # Action forced to be on row vectors
    # might be more natural to have a left
    # action be on column vectors
    def cofree_right_module(self, degrees):
        if not (type(degrees) == list):
            return self.cofree_right_module([degrees])

        def law(x, f, y):
            ret = matrix(self.ring, 0, 0, [])
            for d in degrees:
                ret = ret.block_sum(self.lact(x, f, y, d))
            return ret.transpose()

        return PointwiseFreeRightModule(self, law)

    #def morphism_to_vector(self, x, f, y):
    #    k = self.cat.morphism_to_number(x, f, y)
    #    l = len(self.cat.hom(x, y))
    #    return vector(self.ring, {l - 1: 0, k: 1})

    def string_to_ring_OLD(self, s):
        if s == '':
            return self.ring(1)
        if s[0] == '+':
            return self.string_to_ring_OLD(s[1:])
        if s == '-':
            return self.ring(-1)
        return self.ring(s)

    def entry_to_monomials_OLD(self, x, entry, y):
        ss = entry.replace(' ', '')
        if ss == '0':
            return [], []
        hom_list = list(self.cat.hom(x, y))
        hom_list.sort(key=len, reverse=True)

        def read_next_morphism(string):
            for f in hom_list:
                k = len(f)
                if string[:k] == f:
                    return string[:k], string[k:]
            raise SyntaxError('Failed to find any of the morphisms ' + str(hom_list) +
                              ' as an initial segment of ' + string)

        scalar_strings = ['+', '-'] + [str(n) for n in range(10)]

        def read_next_scalar(string):
            for i in range(len(string)):
                if string[i] not in scalar_strings:
                    return string[:i], string[i:]
            return '', string

        current_string = '+' + ss
        current_morphs = []
        current_coeffs = []
        while len(current_string) != 0:
            scalar, current_string = read_next_scalar(current_string)
            current_coeffs.append(self.string_to_ring_OLD(scalar))
            morphism, current_string = read_next_morphism(current_string)
            current_morphs.append(morphism)
        return current_coeffs, current_morphs

    def matrix_to_entries_OLD(self, source, matrix_string, target):
        r = len(source)
        c = len(target)

        def read_next(s, t, string):
            ss = string
            hom_list = list(self.cat.hom(s, t))
            hom_list.sort(key=len, reverse=True)
            for f in hom_list:
                ss = ss.replace(f, '~' * len(f))
            end_codon_position = [ss.find(','), ss.find(']')]
            return min([x for x in end_codon_position if x != -1])

        left_to_parse = matrix_string
        if left_to_parse[0] != '[':
            raise SyntaxError('Matrix must start with the symbol \'[\'' + matrix_string + '\n' + left_to_parse)
        left_to_parse = left_to_parse[1:]
        output_matrix = []
        for i in range(r - 1):
            s = source[i]
            if left_to_parse[0] != '[':
                raise SyntaxError('Row must start with the symbol \'[\'' + matrix_string + '\n' + left_to_parse)
            left_to_parse = left_to_parse[1:]
            row = []
            for j in range(c - 1):
                t = target[j]
                k = read_next(s, t, left_to_parse)
                row.append(left_to_parse[:k])
                left_to_parse = left_to_parse[k:]
                if left_to_parse[0] != ',':
                    raise SyntaxError('Row ended before ' + str(c) + ' entries.'
                                      + matrix_string + '\n' + left_to_parse)
                left_to_parse = left_to_parse[1:]
            t = target[c - 1]
            k = read_next(s, t, left_to_parse)
            row.append(left_to_parse[:k])
            left_to_parse = left_to_parse[k:]
            if left_to_parse[0] != ']':
                raise SyntaxError('Row should have ended after ' + str(c) + ' entries: '
                                  + matrix_string + '\n' + left_to_parse)
            left_to_parse = left_to_parse[1:]
            output_matrix.append(row)
            if left_to_parse[0] != ',':
                raise SyntaxError('Rows must be separated with the symbol \',\'' + matrix_string + '\n' + left_to_parse)
            left_to_parse = left_to_parse[1:]
        s = source[r - 1]
        if left_to_parse[0] != '[':
            raise SyntaxError('Row must start with the symbol \'[\'' + matrix_string + '\n' + left_to_parse)
        left_to_parse = left_to_parse[1:]
        row = []
        for j in range(c - 1):
            t = target[j]
            k = read_next(s, t, left_to_parse)
            row.append(left_to_parse[:k])
            left_to_parse = left_to_parse[k:]
            if left_to_parse[0] != ',':
                raise SyntaxError('Row ended before ' + str(c) + ' entries.' + matrix_string + '\n' + left_to_parse)
            left_to_parse = left_to_parse[1:]
        t = target[c - 1]
        k = read_next(s, t, left_to_parse)
        row.append(left_to_parse[:k])
        left_to_parse = left_to_parse[k:]
        if left_to_parse[0] != ']':
            raise SyntaxError('Row should have ended after ' + str(c) + ' entries.'
                              + matrix_string + '\n' + left_to_parse)
        left_to_parse = left_to_parse[1:]
        if left_to_parse != ']':
            raise SyntaxError('Matrix should have ended after ' + str(r) + ' rows.'
                              + matrix_string + '\n' + left_to_parse)
        output_matrix.append(row)
        return output_matrix

    def vector_to_entry_OLD(self, x, v, y):
        morphs = self.cat.hom(x, y)
        ret = ''
        for (i, s) in enumerate(v.list()):
            if s != self.ring(0):
                ss = str(s)
                if ss[0] != '-':
                    ss = '+' + ss
                if ss == '+1':
                    ss = '+'
                if ss == '-1':
                    ss = '-'
                ret = ret + ss + morphs[i]
        if ret == '':
            return '0'
        if ret[0] == '+':
            return ret[1:]
        return ret

    # Here, vv is a list of vectors that become the columns of a matrix
    def vector_to_matrix(self, source, vv, target):
        if len(source) == 0 or len(target) == 0:
            return '[]'
        ww = [v for v in vv]
        ret = '['
        for x in source:
            ret += '['
            for (i, y) in enumerate(target):
                h = len(self.cat.hom(x, y))
                ret = ret + self.vector_to_entry_OLD(x, ww[i][:h], y) + ','
                ww[i] = ww[i][h:]
            ret = ret[:-1]
            ret += '],'
        ret = ret[:-1]
        ret += ']'
        return ret

    def yoneda_map(self, degrees, vv, rep):
        if not (type(degrees) is list):
            return self.yoneda_map([degrees], [vv], rep)

        def claw(p):
            ret = []
            for (i, d) in enumerate(degrees):
                for f in self.cat.hom(d, p):
                    ret += [vv[i] * rep(d, f, p)]
            return matrix(self.ring, ret)

        return MapOfMatrixRepresentations(self, self.free_right_module(degrees), claw, rep)

    def matrix_to_map_of_frees(self, source, matrix, target):
        target_rep = self.free_right_module(source)
        source_rep = self.free_right_module(target)

        def law(x):
            ev = self.cofree_right_module(x)
            return ev(source, matrix, target).transpose()

        return MapOfMatrixRepresentations(self, source_rep, law, target_rep)

    def trivial_representation(self):
        def rep_law(x, f, y):
            return identity_matrix(self.ring, 1)

        return PointwiseFreeRightModule(self, rep_law)

    def resolve_trivial_module(self, steps, progress_report=False):
        if steps - 1 in self.resolution_of_trivial_module:
            print 'steps in already:'
            print self.resolution_of_trivial_module.keys()
            return
        tv = self.trivial_representation()
        coch = tv.resolution(steps, progress_report=progress_report)
        for i, (x, f, y) in enumerate(coch):
            self.resolution_of_trivial_module[i] = (x, f, y)
        return None

    def resolution_differential(self, d):
        if d in self.resolution_of_trivial_module:
            return self.resolution_of_trivial_module[d]
        else:
            self.resolve_trivial_module(d)
        return self.resolution_of_trivial_module[d]



class PointwiseFreeRightModule(object):
    def __init__(self, cat, ring, law):
        self.cat = cat
        self.ring = ring
        self.law = law
        self.pre = {}
        self.dims = {}

    def __call__(self, *args):
        if len(args) == 3:
            x, f, y = args
            if (x, f, y) in self.pre:
                return self.pre[(x, f, y)]
            else:
                ret = self.law(x, f, y)
                self.pre[(x, f, y)] = ret
                return ret
        if not (len(args) == 1 and isinstance(args[0], CatMat)):
            raise SyntaxError('Evaluate a representation on a triple (x, f, y) or on a CatMat')
        cm = args[0]
        assert isinstance(cm, CatMat)
        block_rows = []
        for (i, x) in enumerate(cm.source):
            block_row = []
            for (j, y) in enumerate(cm.target):
                e = cm.entry_vector(i, j)
                block_entry = matrix(self.ring, self.rank(x), self.rank(y))
                for (k, f) in enumerate(self.cat.hom(x, y)):
                    if self.ring(e[k]) != self.ring(0):
                        block_entry += e[k] * self(x, f, y)
                block_row += [block_entry]
            block_rows += [block_row]
        return block_matrix(block_rows)

    def rank(self, x):
        if self.dims.has_key(x):
            return self.dims[x]
        ret = len(self.law(x, self.cat.identity(x), x).rows())
        self.dims[x] = ret
        return ret

    def findNewVector(self, listOfSubspanners, progress_report=False):
        for (i, subspanners) in enumerate(listOfSubspanners):
            o = self.sm.cat.objects[i]
            ad = self.rank(o)
            cd = subspanners.nrows()
            if ad != cd:
                stm = subspanners.stack(identity_matrix(ad))
                pvr = stm.pivot_rows()
                return (i, o, stm.row(pvr[-1]))
        return (None, None, None)

    def addVector(self, listOfSubspanners, i, o, v, progress_report=False):
        ret = [m for m in listOfSubspanners]
        if progress_report:
            print
        for (j, p) in enumerate(self.sm.cat.objects):
            if progress_report:
                sys.stdout.write('\raddVector on object ' + str(j + 1) + '/' + str(len(self.sm.cat.objects)))
            ad = ret[j].ncols()
            for f in self.sm.cat.hom(o, p):
                old = ret[j]
                cd = old.nrows()
                ret[j] = ret[j].stack(v * self(o, f, p))
                ret[j] = ret[j].echelon_form()
                if ret[j].row(cd) == vector(self.field, ad):
                    ret[j] = old
        if progress_report:
            print
        return ret

    def generators(self, progress_report=False):
        subrep = [matrix(self.field, 0, self.rank(o)) for o in self.sm.cat.objects]
        retd = []
        retv = []
        (i, p, v) = self.findNewVector(subrep)
        while not (v is None):
            retd = retd + [p]
            retv = retv + [v]
            subrep = self.addVector(subrep, i, p, v, progress_report=progress_report)
            (i, p, v) = self.findNewVector(subrep)
        return (retd, retv)

    def presentation(self, progress_report=False):
        degs, gens = self.generators(progress_report=progress_report)
        surj = self.sm.yoneda_map(degs, gens, self)
        incl, krep, nope = surj.kernel_OLD()
        szd, szg = krep.generators(progress_report=progress_report)
        return (degs, self.sm.vector_to_matrix(degs, [szg[i] * incl(szd[i]) for i in range(len(szd))], szd), szd)

    def resolution(self, steps, progress_report=False):
        degs, gens = self.generators(progress_report=progress_report)
        surj = self.sm.yoneda_map(degs, gens, self)
        incl, krep, nope = surj.kernel_OLD()
        return self.resolve_step(degs, incl, krep, steps, progress_report=progress_report)

    def resolve_step(self, degs, incl, krep, steps, progress_report=False):
        if steps == 0:
            return []
        if progress_report:
            print 'Resolution steps left ' + str(steps)
        szd, szg = krep.generators(progress_report=progress_report)
        surj = self.sm.yoneda_map(szd, szg, krep)
        zincl, zkrep, nope = surj.kernel_OLD()
        return [(degs, self.sm.vector_to_matrix(degs, [szg[i] * incl(szd[i]) for i in range(len(szd))], szd), szd)] + \
               self.resolve_step(szd, zincl, zkrep, steps - 1, progress_report=progress_report)

    def identity(self):
        def law(x):
            return self(x, self.sm.cat.identity(x), x)
        return MapOfMatrixRepresentations(self.sm, self, law, self)


class MapOfMatrixRepresentations(object):
    def __init__(self, source, law, target):
        self.source = source
        self.law = law
        self.target = target
        self.ring = self.source.ring
        self.pre = {}
    def __call__(self, o):
        return self.component(o)
    def component(self, o):
        if self.pre.has_key(o):
            return self.pre[o]
        ret = self.law(o)
        self.pre[o] = ret
        return ret
    def kernel_OLD(self):
        assert(self.ring in PrincipalIdealDomains())
        #Find the pointwise kernels.
        #This gives the law for the natural morphism ker-->V
        def ilaw(o):
            oc = self.component(o)
            lk = oc.left_kernel()
            return matrix(self.ring, lk.dimension(), oc.nrows(), [e for b in lk.basis() for e in b])
        inclusion = MapOfMatrixRepresentations(self.sm, None, ilaw, self.source)
        def rlaw(x, f, y):
            kx = inclusion(x)
            ky = inclusion(y)
            am = self.source(x, f, y)
            return ky.solve_left(kx * am)
        #The final None should be replaced with a rule giving the universal property of the kernel
        #One day this will be implemented using the unit and counit of right kan extension
        #from a single arrow to a chain complex.
        krep = PointwiseFreeRightModule(self.sm, rlaw)
        inclusion.source = krep
        return (inclusion, krep, None)



# To build a MatrixRepresentation you supply a law which is a function of the form
#      law(x, f, y)
# where x and y are objects and f is a string representing some morphism from x to y.


class PointwiseFreeRightModule(object):
    def __init__(self, cat, ring, law):
        self.cat = cat
        self.ring = ring
        self.law = law
        self.pre = {}
        self.dims = {}

    def __call__(self, *args):
        if len(args) == 3:
            x, f, y = args
            if (x, f, y) in self.pre:
                return self.pre[(x, f, y)]
            else:
                ret = self.law(x, f, y)
                self.pre[(x, f, y)] = ret
                return ret
        if not (len(args) == 1 and isinstance(args[0], CatMat)):
            raise SyntaxError('Evaluate a representation on a triple (x, f, y) or on a CatMat')
        cm = args[0]
        assert isinstance(cm, CatMat)
        block_rows = []
        for (i, x) in enumerate(cm.source):
            block_row = []
            for (j, y) in enumerate(cm.target):
                e = cm.entry_vector(i, j)
                block_entry = matrix(self.ring, self.rank(x), self.rank(y))
                for (k, f) in enumerate(self.cat.hom(x, y)):
                    if self.ring(e[k]) != self.ring(0):
                        block_entry += e[k] * self(x, f, y)
                block_row += [block_entry]
            block_rows += [block_row]
        return block_matrix(block_rows)

    def rank(self, x):
        if self.dims.has_key(x):
            return self.dims[x]
        ret = len(self.law(x, self.cat.identity(x), x).rows())
        self.dims[x] = ret
        return ret

    def findNewVector(self, listOfSubspanners, progress_report=False):
        for (i, subspanners) in enumerate(listOfSubspanners):
            o = self.sm.cat.objects[i]
            ad = self.rank(o)
            cd = subspanners.nrows()
            if ad != cd:
                stm = subspanners.stack(identity_matrix(ad))
                pvr = stm.pivot_rows()
                return (i, o, stm.row(pvr[-1]))
        return (None, None, None)

    def addVector(self, listOfSubspanners, i, o, v, progress_report=False):
        ret = [m for m in listOfSubspanners]
        if progress_report:
            print
        for (j, p) in enumerate(self.sm.cat.objects):
            if progress_report:
                sys.stdout.write('\raddVector on object ' + str(j + 1) + '/' + str(len(self.sm.cat.objects)))
            ad = ret[j].ncols()
            for f in self.sm.cat.hom(o, p):
                old = ret[j]
                cd = old.nrows()
                ret[j] = ret[j].stack(v * self(o, f, p))
                ret[j] = ret[j].echelon_form()
                if ret[j].row(cd) == vector(self.field, ad):
                    ret[j] = old
        if progress_report:
            print
        return ret

    def generators(self, progress_report=False):
        subrep = [matrix(self.field, 0, self.rank(o)) for o in self.sm.cat.objects]
        retd = []
        retv = []
        (i, p, v) = self.findNewVector(subrep)
        while not (v is None):
            retd = retd + [p]
            retv = retv + [v]
            subrep = self.addVector(subrep, i, p, v, progress_report=progress_report)
            (i, p, v) = self.findNewVector(subrep)
        return (retd, retv)

    def presentation(self, progress_report=False):
        degs, gens = self.generators(progress_report=progress_report)
        surj = self.sm.yoneda_map(degs, gens, self)
        incl, krep, nope = surj.kernel_OLD()
        szd, szg = krep.generators(progress_report=progress_report)
        return (degs, self.sm.vector_to_matrix(degs, [szg[i] * incl(szd[i]) for i in range(len(szd))], szd), szd)

    def resolution(self, steps, progress_report=False):
        degs, gens = self.generators(progress_report=progress_report)
        surj = self.sm.yoneda_map(degs, gens, self)
        incl, krep, nope = surj.kernel_OLD()
        return self.resolve_step(degs, incl, krep, steps, progress_report=progress_report)

    def resolve_step(self, degs, incl, krep, steps, progress_report=False):
        if steps == 0:
            return []
        if progress_report:
            print 'Resolution steps left ' + str(steps)
        szd, szg = krep.generators(progress_report=progress_report)
        surj = self.sm.yoneda_map(szd, szg, krep)
        zincl, zkrep, nope = surj.kernel_OLD()
        return [(degs, self.sm.vector_to_matrix(degs, [szg[i] * incl(szd[i]) for i in range(len(szd))], szd), szd)] + \
               self.resolve_step(szd, zincl, zkrep, steps - 1, progress_report=progress_report)

    def identity(self):
        def law(x):
            return self(x, self.sm.cat.identity(x), x)
        return MapOfMatrixRepresentations(self.sm, self, law, self)


class MapOfMatrixRepresentations(object):
    def __init__(self, source, law, target):
        self.source = source
        self.law = law
        self.target = target
        self.ring = self.source.ring
        self.pre = {}
    def __call__(self, o):
        return self.component(o)
    def component(self, o):
        if self.pre.has_key(o):
            return self.pre[o]
        ret = self.law(o)
        self.pre[o] = ret
        return ret















# A dgModule with source category C and target category D is a functor
# from C to the category of nonnegatively-graded cochain complexes of D-matrices.
#
# The two main constructions on a dgModule are called resolution and substitution
# Resolution makes the source category trivial, and substitution makes the target
# category trivial.
#
# Resolution:
# Adds a new differential direction, and eliminates the source category while
# upgrading the target category to the product C x D
#
#
# Substitution:
# The functor tensor product for a pair of dgModules with opposite targets.  The
# result gives a dgModule with trivial target.
#
# Two kinds of casework make this code harder to read but easier to use:
# A dgModule can have values in CatMats or in sagemath matrices (cat_mat = True or False)
# A dgModule M with n_diff==0 may be called using M(x, f, y)
# instead of M((x, f, y), ((), ())) which is not convenient.
# If the source is the terminal category, then only the differential remains.  Should this be a third case?
# TODO: test all four combinations of these cases
class dgModule(object):
    # law gives the structure maps.  law((x, f, y), (d, e))
    # Here d and e are multidegrees given as tuples of integers.
    # Each multidegree has length n_diff, which is the number of differentials
    # When n_diff=0, this thing is just a module for cat (since there are no differentials)
    # cat_mat tells you if the values are in CatMats.  If this is set to false,
    # then the dgModule uses usual sage matrices.
    # law will only be called on pairs (d, e) that are different by exactly one in a single coordinate
    # so you do not need to supply a full accounting.
    # If n_diff=0 (which is the default) then law takes the form law(x, f, y)
    def __init__(self, ring, cat, law, target_cat=None, n_diff=0):
        self.ring = ring
        self.cat = cat
        self.law = law
        self.n_diff = n_diff
        self.target_cat = target_cat
        self.cat_mat = not (target_cat is None)
        # This dictionary stores the basic differentials
        # the ones where the multidegree changes in exactly one place.
        # A typical key is (x, d, a)
        # where x is an object, d is a multidegree, and a is a number in range(n_diff)
        self.dpre = {}
        self.spre = {}
        # If cat_mat is true, then this dictionary keeps tuples of objects instead of ranks.
        self.ranks = {}

    # This is for remembering the ranks of any induced map that has been computed incidentally
    def learn_rank(self, (x, d), m, (y, e)):
        if (x, d) not in self.ranks:
            if self.cat_mat:
                self.ranks[(x, d)] = m.source
            else:
                self.ranks[(x, d)] = m.nrows()

        if (y, e) not in self.ranks:
            if self.cat_mat:
                self.ranks[(y, e)] = m.target
            else:
                self.ranks[(y, e)] = m.ncols()

    # Compute differentials using __call__
    #
    # Here x is an object of cat
    # d is a multidegree
    # and a is in range(n_diff)
    def basic_differential(self, x, d, a):
        if a >= self.n_diff:
            # This error also applies if you try to compute the differential
            # of a dgModule that has no differential.
            raise ValueError('The third argument must be less than ' + str(self.n_diff))
        if (x, d, a) in self.dpre:
            return self.dpre[(x, d, a)]
        else:
            e = d
            e[a] += 1
            ret = self.law((x, self.cat.identity(x), x), (d, e))
            self.learn_rank((x, d), ret, (x, d))
            self.dpre[(x, d, a)] = ret
            return ret

    # Compute structure maps using __call__
    #
    # Here x, f, y is a morphism of cat
    # and d is a multidegree
    def basic_structure_map(self, x, f, y, d=tuple()):
        if (x, f, y, d) in self.spre:
            return self.spre[(x, f, y, d)]
        else:
            if self.n_diff == 0:
                ret = self.law(x, f, y)
            else:
                ret = self.law((x, f, y), (d, d))
            self.learn_rank((x, d), ret, (y, d))
            self.spre[(x, f, y, d)] = ret
            return ret

    # Here mlaw takes 3 arguments (x, f, y)
    # and it is understood that all other degrees are zero
    @classmethod
    def concentrated_in_degree(cls, ring, cat, mlaw, degree, target_cat=None):

        def law((x, f, y), (d, e)):
            if d == degree:
                if e == degree:
                    return mlaw(x, f, y)
                else:
                    return zero_matrix(ring, mlaw(x, cat.identity(x), x).nrows(), 0)
            else:
                if e == degree:
                    return zero_matrix(ring, 0, mlaw(y, cat.identity(y), y).nrows(), 0)
                else:
                    return identity_matrix(ring, 0)

        return dgModule(ring, cat, law, target_cat=target_cat, n_diff=len(degree))

    # Here *complexes is a tuple of dgModules given directly as the arguments
    # This builds a module for the target category, retaining all gradings.
    @classmethod
    def outer_tensor_product(cls, ring, *complexes):
        new_source = ProductCategory(*[dgm.cat for dgm in complexes])
        # Some of the complexes may take values in usual sagemath matrices
        # and so the target category omits those factors
        target_factors = [dgm.target_cat for dgm in complexes if dgm.cat_mat]
        if len(target_factors) == 0:
            new_target = None
        else:
            new_target = ProductCategory(*target_factors)
        q = len(complexes)
        pi_functors = [new_source.pi(k) for k in range(q)]

        # lower and upper for the differentials
        flower = []
        fupper = []

        # Find the total number of differentials in the outer product
        # and figure out the lower and upper index of each factor
        n = 0
        for i, cx in enumerate(complexes):
            flower += [n]
            n += cx.n_diff
            fupper += [n]

        new_n_diff = n

        # If there are no differentials:
        if new_n_diff == 0:

            def new_law(x, f, y):
                tensor_factors = [cx(*pi_functors[k](x, f, y)) for k in range(q)]
                return CatMat.kronecker_product(tensor_factors, ring=ring)

            return dgModule(ring, new_source, new_law, target_cat=new_target)

        # In this case, new_n_diff > 0
        def new_law((x, f, y), (d, e)):
            tensor_factors = []
            for k, cx in enumerate(complexes):
                if cx.n_diff == 0:
                    tensor_factors += [cx(*pi_functors[k](x, f, y))]
                else:
                    tensor_factors += [cx(pi_functors[k], (d[flower[k]:fupper[k]], e[flower[k]:fupper[k]]))]
            return CatMat.kronecker_product(tensor_factors, ring=ring)

        return dgModule(ring, new_source, new_law, target_cat=new_target, n_diff=new_n_diff)

    def rank(self, x, d):
        if (x, d) in self.ranks:
            return self.ranks[(x, d)]
        if self.n_diff == 0:
            ret = self.law(x, self.cat.identity(x), x).nrows()
        else:
            ret = self.law((x, self.cat.identity(x), x), (d, d)).nrows()
        self.ranks[(x, d)] = ret
        return ret

    def differential(self, x, (d, e)):
        if d == e:
            return identity_matrix(self.ring, self.rank(x, d))
        if d + 1 == e:
            if (x, (d, e)) in self.dpre:
                return self.dpre[(x, (d, e))]
            ret = self.law((x, self.cat.identity(x), x), (d, e))
            self.dpre[(x, (d, e))] = ret
            return ret
        return zero_matrix(self.ring, self.rank(x, d), self.rank(x, e))

    # arg is allowed to be (x, f, y) or a CatMat
    def __call__(self, arg, degree_pair=(tuple(), tuple())):
        d, e = degree_pair

        if isinstance(arg, CatMat):
            # build up a block matrix for the degree d induced map
            # then multiply by the appropriate differentials
            # and return.

            # First compute structure_part
            block_rows = []
            for i, x in enumerate(arg.source):
                block_row = []
                for j, y in enumerate(arg.target):
                    if self.cat_mat:
                        block_entry = CatMat.zero_matrix(self.ring, self.target_cat, self.rank(x, d), self.rank(y, d))
                    else:
                        block_entry = zero_matrix(self.ring, self.rank(x, d), self.rank(y, d))
                    coefs = arg.entry_vector(i, j)
                    for k, f in enumerate(arg.cat.hom(x, y)):
                        block_entry += coefs[k] * self.basic_structure_map(x, f, y, d)
                    block_row += [block_entry]
                block_rows += [block_row]
            if self.cat_mat:
                sources = [self.rank(x, d) for x in arg.source]
                targets = [self.rank(y, d) for y in arg.target]
                structure_part = CatMat.block_matrix(block_rows, self.ring, self.target_cat, sources, targets)
            else:
                rows = sum([self.rank(x, d) for x in arg.source])
                cols = sum([self.rank(y, d) for y in arg.target])
                if rows * cols == 0:
                    structure_part = matrix(self.ring, rows, cols, [])
                else:
                    structure_part = block_matrix(block_rows)

            # Now compute differential_part
            blocks = [self((y, self.cat.identity(y), y), (d, e)) for y in arg.target]
            if self.cat_mat:
                sources = [self.rank(y, d) for y in arg.target]
                targets = [self.rank(y, e) for y in arg.target]
                differential_part = CatMat.block_diagonal(blocks, self.ring, self.target_cat)
            else:
                differential_part = matrix(self.ring, 0, 0, [])
                for block in blocks:
                    differential_part = differential_part.block_sum(block)
            return structure_part * differential_part



        # If arg is not a CatMat
        # then we should be able to unpack:
        x, f, y = arg
        if d == e:
            return self.basic_structure_map(x, f, y, d)

        d_directions = []
        for i in range(self.n_diff):
            if e[i] not in [d[i], d[i] + 1]:
                if self.cat_mat:
                    return CatMat.zero_matrix(self.ring, self.target_cat, self.rank(x, d), self.rank(y, e))
                else:
                    return zero_matrix(self.ring, self.rank(x, d), self.rank(y, e))
            if e[i] == d[i] + 1:
                d_directions += [i]

        # Possible improvement here:
        # check which factorization goes through the smallest things
        # and compute it that way.

        ret = self.basic_structure_map(x, f, y, d) # Should it be d=d?
        cur_deg = d
        for i in d_directions:
            ret = ret * self.basic_differential(y, cur_deg, i)
            cur_deg[i] += 1
        return ret

    # Gives a list of pairs (x, i)
    # basis positions that generate the degree d part
    # using the structure maps.
    def degreewise_generators(self, d=tuple()):
        # Start with presentation matrix
        # this code has two steps
        # Original thing is covariant, takes C morphisms to D morphisms
        # but now we surject
        if self.cat_mat:
            potential_gens = [(x, i) for x in self.cat.objects for i in range(len(self.rank(x, d)))]
        else:
            potential_gens = [(x, i) for x in self.cat.objects for i in range(self.rank(x, d))]
        npg = len(potential_gens)
        pointwise_spans = dict()
        for x, i in potential_gens:
            for y in self.cat.objects:
                rows = []
                for f in self.cat.hom(x, y):
                    # The following line works for both CatMats and sagemath matrices
                    rows += [self.basic_structure_map(x, f, y, d).row(i)]
                if self.cat_mat:
                    sources = [self.rank(x, d)[i]] * len(rows)
                    targets = [self.rank(y, d)]
                    pointwise_spans[x, i, y] = CatMat.block_matrix([[r] for r in rows],
                                                                   self.ring, self.cat, sources, targets)
                else:
                    if len(rows) == 0:
                        pointwise_spans[x, i, y] = zero_matrix(self.ring, 0, self.rank(y, d))
                    else:
                        pointwise_spans[x, i, y] = block_matrix([[matrix(self.ring, 1, len(r), list(r))] for r in rows])
        prices = [None] * npg
        for g, (x, i) in enumerate(potential_gens):
            price = 0
            for y in self.cat.objects:
                # The following line works for CatMats and sagemath matrices
                price += pointwise_spans[x, i, y].nrows()
            prices[g] = ((x, i), price)
        prices.sort(key=lambda p: p[1], reverse=True)
        greedy_order = [(x, i) for (x, i), _ in prices]
        current_gens = {(x, i): True for x, i in potential_gens}
        for x, i in greedy_order:
            current_gens[x, i] = False
            for y in self.cat.objects:
                my_table = [[pointwise_spans[xx, ii, y]] for xx, ii in potential_gens if current_gens[xx, ii]]
                if self.cat_mat:
                    sources = [[self.ranks(xx, d)[ii]] for xx, ii in potential_gens if current_gens[xx, ii]]
                    targets = [self.ranks(y, d)]
                    my = CatMat.block_matrix(my_table, self.ring, self.cat, sources, targets)
                    try:
                        pointwise_spans[x, i, y] << my
                    except ValueError:
                        current_gens[x, i] = True
                        break
                else:
                    if len(my_table) == 0:
                        my = zero_matrix(self.ring, 0, self.ranks(y, d))
                    else:
                        my = block_matrix(my_table)
                    if not pointwise_spans[x, i, y].row_space().is_submodule(my.row_space()):
                        current_gens[x, i] = True
                        break
        chosen_gens = [(x, i) for x, i in potential_gens if current_gens[x, i]]
        return chosen_gens

    # Gives the qth step in a resolution of the multidegree d part of self.
    # If q=0, this gives a presentation matrix for the C-rep in degree d
    # This makes sense directly if not cat_mat
    # and still makes enough sense if cat_mat.
    def degreewise_syzygy_matrix(self, q, d):
        pass

    # This code produces a new dgModule
    # whose source category is trivial
    # and with an extra differential.
    # The new target category is the old source
    def resolve(self):
        # use the presentation matrices
        # and syzygies precomputed
        pass



    # Here's a fragment that is probably not useful


    chosen_rows = dict()
    chosen_row_sources = dict()
    for x in self.cat.objects:
        chosen_rows[x] = []
        if self.cat_mat:
            chosen_row_sources[x] = []
        else:
            chosen_row_sources[x] = 0

    for x, i in chosen_gens:
        chosen_rows += subspanners[x].row(i)
        if self.cat_mat:
            chosen_row_sources[x] += [self.rank(x)[i]]
        else:
            chosen_row_sources[x] += 1

    ret = dict()
    for x in self.cat.objects:
        if self.cat_mat:
            sources = [[s] for s in chosen_row_sources[x]]
            targets = [self.rank(x)]
            table = chosen_rows[x]
            ret[x] = CatMat.block_matrix(table, self.ring, self.target_cat, sources, targets)
        else:
            if chosen_row_sources[x] == 0:
                ret[x] = zero_matrix(self.ring, 0, self.rank(x))
            else:
                ret[x] = block_matrix(chosen_rows[x])
    return ret

