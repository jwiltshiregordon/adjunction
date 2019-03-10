from sage.all import *
from sage.all import matrix, vector, identity_matrix, block_matrix, zero_vector, zero_matrix, block_diagonal_matrix
import sys
import itertools
from collections import Iterable

# This code is for computing the homology of a finite category with coefficients in a functor.
# For example, it can compute homotopy colimits in the category of cochain complexes over the integers.
# The rough steps for use: define a finite category that indexes your diagram of cochain complexes,
# and then use resolution and substitution to build a multicomplex whose total complex is your hocolim.


# TODO: support for unit-counit tensor-hom adjunction for bimodules
# TODO: bring the ring into the category to get additive categories
# TODO: preadditive categories with homs that are free abelian
# TODO: eventually, dg-categories

# TODO: main next steps: fix product categories; introduce preadditive cats
# TODO: sparse vs. dense matrices.  Reimplement CatMat to be sparse, I think
# TODO: parallel computation
# TODO: indexed matrices should be a category whose objects are injective tuples
# TODO: so that we obtain unique compatible reorderings whenever required.

# TODO: new version should not have functions as arguments, but instead use overload


# Constructing a FiniteCategory using __init__
#
# object_list
# The list of objects in the category.  These objects must be hashable.
#
# one_law
# This argument tells the FiniteCategory what the identity morphisms are.  It must be a
# function that takes an object and returns a string that represents the identity at
# that object.
#
# hom_law
# This argument tells the FiniteCategory how to compute hom between two objects.  It must be a
# function that takes a pair of objects and returns a list of morphisms from one to the other.
# The morphisms are represented as strings.
#
# composition_law
# This argument tells the FiniteCategory how to compose.  It is a function of the following
# form:
#        composition_law(x, f, y, g, z)
# where x, y, and z are objects, and f : x --> y and g : y --> z are morphisms represented
# as strings.
#
class FiniteCategory(object):
    def __init__(self, object_list, one_law, hom_law, composition_law,
                 object_latex_law=None, morphism_latex_law=None,
                 cache=True):
        self.objects = object_list
        self.basic_hom = hom_law
        self.basic_one = one_law
        self.basic_composition = composition_law
        self.one_dict = {}
        self.hom_dict = {}
        self.mns = {}
        self.msn = {}

        self.lact = {}
        self.mact = {}
        self.ract = {}
        self.op_cat = OppositeCategory(self)

        self.cache = cache

        def default_object_latex_law(o):
            #return '\\texttt{' + str(o) + '}'
            return latex(o)

        def default_morphism_latex_law(x, f, y):
            return '\\scalebox{.7}{\\fbox{\\texttt{' + f + '}}}'
        self.object_latex_law = object_latex_law or default_object_latex_law
        self.morphism_latex_law = morphism_latex_law or default_morphism_latex_law

    def identity(self, x):
        if x in self.one_dict:
            return self.one_dict[x]
        ret = self.basic_one(x)
        self.one_dict[x] = ret
        return ret

    def hom(self, x, y):
        if (x, y) in self.hom_dict:
            return self.hom_dict[(x, y)]
        ret = self.basic_hom(x, y)
        self.hom_dict[(x, y)] = ret
        return ret

    def compose(self, x, f, y, g, z):
        return self.basic_composition(x, f, y, g, z)

    def morphism_to_number(self, x, f, y):
        if (x, f, y) in self.msn:
            return self.msn[(x, f, y)]
        h = self.hom(x, y)
        try:
            k = h.index(f)
        except ValueError:
            raise SyntaxError("The string '" + f + "' doesn't define a morphism " + str(x) + " -----> " + str(y))
        self.msn[(x, f, y)] = k
        return k

    def object_to_latex(self, o):
        return self.object_latex_law(o)

    def morphism_to_latex(self, x, f, y):
        return self.morphism_latex_law(x, f, y)

    # This function is used to parse linear combinations of morphisms
    # from the category.  It greedily searches for morphisms in a string
    # and returns a list of morphisms appearing, as well as a list of
    # between strings.  If n morphisms appear in the string, then
    # morphs will be a list of length n giving these strings in order.
    # In this case, len(coeffs) = n + 1.
    # The function satisfies
    #    entry_string = coefficients[0] + morphisms[0] + coefficients[1] + ... + morphisms[n - 1] + coefficients[n]
    def split_string_on_morphisms(self, x, entry_string, y):
        ss = entry_string
        hom_list = list(self.hom(x, y))
        hom_list.sort(key=len, reverse=True)
        for f in hom_list:
            ss = ss.replace(f, '~' * len(f))
        tt = ''
        for i, c in enumerate(ss):
            if c == '~':
                tt += entry_string[i]
            else:
                tt += '~'
        import re
        morphs = re.split(r'~+', tt)
        coeffs = re.split(r'~+', ss)
        return morphs, coeffs

    def left_action_matrix(self, x, f, y, z):
        if self.cache and (x, f, y, z) in self.lact:
            return self.lact[(x, f, y, z)]
        rows = self.hom(y, z)
        cols = self.hom(x, z)
        ret = matrix(ZZ, len(rows), len(cols), [1 if self.compose(x, f, y, r, z) == c
                                                else 0 for r in rows for c in cols])
        self.lact[(x, f, y, z)] = ret
        return ret

    def middle_action_matrix(self, x, f, z, y):
        if self.cache and (x, f, z, y) in self.mact:
            return self.mact[(x, f, z, y)]
        rows = self.hom(x, y)
        cols = self.hom(y, z)
        ret = matrix(ZZ, len(rows), len(cols), [1 if self.compose(x, r, y, c, z) == f
                                                else 0 for r in rows for c in cols])
        self.mact[(x, f, z, y)] = ret
        return ret

    def right_action_matrix(self, x, y, f, z):
        if self.cache and (x, y, f, z) in self.ract:
            return self.ract[(x, y, f, z)]
        rows = self.hom(x, y)
        cols = self.hom(x, z)
        ret = matrix(ZZ, len(rows), len(cols), [1 if self.compose(x, r, y, f, z) == c
                                                else 0 for r in rows for c in cols])
        self.ract[(x, y, f, z)] = ret
        return ret

    def op(self):
        return self.op_cat

    # Bug: since objects of the category might be iterable
    # you must always give a list of degrees.
    # TODO: go through code and fix every appearance of free_module(ring, single_degree)
    def free_module(self, ring, degrees):
        try:
            iter(degrees)
        except TypeError:
            print 'Warning! You have passed a non-iterable list of degrees to free_module.'
            print 'Figure out when it happend, and fix it!'
            return self.free_module(ring, (degrees,))

        def law(x, f, y):
            ret = matrix(ring, 0, 0, [])
            for d in degrees:
                ret = ret.block_sum(self.right_action_matrix(d, x, f, y))
            return ret

        return MatrixRepresentation(self, ring, law, target_cat=None)

    def free_op_module(self, ring, degrees):
        return self.op_cat.free_module(ring, degrees)

    def cofree_module(self, ring, degrees):
        try:
            iter(degrees)
        except TypeError:
            return self.cofree_module(ring, (degrees,))

        def law(x, f, y):
            ret = matrix(ring, 0, 0, [])
            for d in degrees:
                ret = ret.block_sum(self.left_action_matrix(x, f, y, d).transpose())
            return ret

        # The module is not really a dgModule
        # since the number of differentials is zero.
        # target_cat=None since we output usual sage matrices
        # instead of CatMats, as is allowed with dgModules.
        return MatrixRepresentation(self, ring, law, target_cat=None)

    # This should be reimplemented to avoid recomputing structure matrices
    def full_subcategory_inclusion(self, objects):
        def full_subcat_one(x):
            return self.identity(x)

        def full_subcat_hom(x, y):
            return self.hom(x, y)

        def full_subcat_comp(x, f, y, g, z):
            return self.compose(x, f, y, g, z)

        full_subcat = FiniteCategory(objects, full_subcat_one, full_subcat_hom, full_subcat_comp)

        def law(x, f, y):
            return x, f, y

        return Functor(full_subcat, law, self)

    def trivial_representation(self, ring):
        def law(x, f, y):
            return matrix(ring, 1, 1, [1])
        return MatrixRepresentation(self, ring, law, target_cat=None)

    def test(self):
        for x in self.objects:
            if self.identity(x) not in self.hom(x, x):
                print 'The identity morphism for the object ' + str(x) + \
                      ', which is supposed to be given by the string ' + self.identity(x) + \
                      ', fails to appear in the hom-set ' + str(self.hom(x, x)) + '.'
        for x in self.objects:
            for y in self.objects:
                for z in self.objects:
                    for f in self.hom(x, y):
                        for g in self.hom(y, z):
                            if self.compose(x, f, y, g, z) not in self.hom(x, z):
                                print 'The composition ' + str((x, f, y, g, z)) + ', which is supposed ' + \
                                    'to be given by the string ' + self.compose(x, f, y, g, z) + \
                                    ', fails to appear in the hom-set ' + str(self.hom(x, z)) + '. '
        for w, x, y, z in itertools.product(*([self.objects] * 4)):
            for f in self.hom(w, x):
                for g in self.hom(x, y):
                    for h in self.hom(y, z):
                        left = self.compose(w, f, x, self.compose(x, g, y, h, z), z)
                        right = self.compose(w, self.compose(w, f, x, g, y), y, h, z)
                        if left != right:
                            print 'The following triple of morphisms do not associate:'
                            print (w, f, x, g, y, h, z)





# More efficient than naively recomputing
class OppositeCategory(FiniteCategory):

    def __init__(self, cat):
        self.op_cat = cat
        self.objects = cat.objects
        def oll(o):
            return self.op_cat.object_latex_law(o) + '^{op}'

        def mll(x, f, y):
            return self.op_cat.morphism_latex_law(y, f, x) + '^{op}'
        self.object_latex_law = oll
        self.morphism_latex_law = mll

    def identity(self, x):
        return self.op_cat.identity(x)

    def hom(self, x, y):
        return self.op_cat.hom(y, x)

    def compose(self, x, f, y, g, z):
        return self.op_cat.compose(z, g, y, f, x)

    def left_action_matrix(self, x, f, y, z):
        return self.op_cat.right_action_matrix(z, y, f, x)

    def middle_action_matrix(self, x, f, z, y):
        return self.op_cat.middle_action_matrix(z, f, x, y).transpose()

    def right_action_matrix(self, x, y, f, z):
        return self.op_cat.left_action_matrix(z, f, y, x)

    def object_to_latex(self, o):
        return self.op_cat.object_latex_law(o)

    def morphism_to_latex(self, x, f, y):
        return self.op_cat.morphism_latex_law(x, f, y)

    def morphism_to_number(self, x, f, y):
        return self.op_cat.morphism_to_number(y, f, x)

    def op(self):
        return self.op_cat

    def free_module(self, ring, degrees):
        try:
            iter(degrees)
        except TypeError:
            return self.free_module(ring, (degrees,))

        def law(x, f, y):
            ret = matrix(ring, 0, 0, [])
            for d in degrees:
                ret = ret.block_sum(self.right_action_matrix(d, x, f, y))
            return ret
        return MatrixRepresentation(self, ring, law, target_cat=None)

    def free_op_module(self, ring, degrees):
        return self.op_cat.free_module(ring, degrees)





# Here we build the terminal category
def terminal_one(x):
    return '*'

def terminal_hom(x, y):
    return '*'

def terminal_comp(x, f, y, g, z):
    return '*'

TerminalCategory = FiniteCategory(['*'], terminal_one, terminal_hom, terminal_comp)


# More efficient than naively recomputing
class ProductCategory(FiniteCategory):

    def __init__(self, arg0, *list_of_cats):
        if type(arg0) is str:
            self.left = '('
            self.sep = arg0
            self.right = ')'
            self.cats = list(list_of_cats)
        else:
            self.left = '('
            self.sep = ','
            self.right = ')'
            self.cats = [arg0] + list(list_of_cats)
        self.ecats = list(enumerate(self.cats))
        self.n_factors = len(self.cats)
        # If the number of factors is one
        # the convention is to have the same objects
        # not one-objects tuples.
        if self.n_factors == 1:
            self.objects = list_of_cats[0].objects
        else:
            self.objects = list(itertools.product(*[cat.objects for cat in self.cats]))

        def oll(o):
            if self.n_factors == 1:
                return self.cats[0].object_to_latex(o)
            z = self.left
            for i, x in enumerate(o):
                z += self.cats[i].object_latex_law(x)
                z += self.sep
            z = z[:-1] + self.right
            return z

        def mll(x, f, y):
            if self.n_factors == 1:
                return self.cats[0].morphism_to_latex(x, f, y)
            z = self.left
            for i, ff in enumerate(self.break_string(f)):
                z += self.cats[i].morphism_latex_law(x[i], ff, y[i])
                z += self.sep
            z = z[:-1] + self.right
            return z
        self.object_latex_law = oll
        self.morphism_latex_law = mll
        self.op_cat = None

        self.mns = {}
        self.msn = {}

    def identity(self, x):
        if self.n_factors == 1:
            return self.cats[0].identity(x)
        return self.combine_strings(*[cat.identity(x[i]) for i, cat in self.ecats])

    def hom(self, x, y):
        if self.n_factors == 1:
            return self.cats[0].hom(x, y)
        return [self.combine_strings(*ss) for ss in itertools.product(*[cat.hom(x[i], y[i]) for i, cat in self.ecats])]

    def compose(self, x, f, y, g, z):
        if self.n_factors == 1:
            return self.cats[0].compose(x, f, y, g, z)
        fb = self.break_string(f)
        gb = self.break_string(g)
        return self.combine_strings(*[cat.compose(x[i], fb[i], y[i], gb[i], z[i]) for i, cat in self.ecats])

    # Projection functor onto the nth factor
    def pi(self, n):
        def law(x, f, y):
            return x[n], self.break_string(f)[n], y[n]
        return Functor(self, law, self.cats[n])

    def combine_strings(self, *strings):
        if len(strings) != self.n_factors:
            raise ValueError('Wrong number of factors for this product category: '
                             + str((len(strings), self.n_factors)))
        if len(strings) == 0:
            return '*'
        if len(strings) == 1:
            return strings[0]
        ts = self.left
        for s in strings:
            ts += s + self.sep
        return ts[:-1] + self.right

    # TODO: This code is badly broken for products of products
    def break_string(self, s):
        # If the string is not a tuple, then we may have a zero- or one-fold product
        if s[:len(self.left)] != self.left or s[-len(self.right):] != self.right:
            return [s]
        return s[1:-1].split(self.sep)

    def left_action_matrix(self, x, f, y, z):
        ret_n_rows = 1
        ret_n_cols = 1
        ret = matrix(ZZ, 1, 1, [1])
        fb = self.break_string(f)
        kfactors = []
        for i, cat in self.ecats:
            kf = cat.left_action_matrix(x[i], fb[i], y[i], z[i])
            ret_n_rows *= kf.nrows()
            ret_n_cols *= kf.ncols()
            kfactors += [kf]
        # This is to avoid a 0-dim bug present in my version of sage
        if ret_n_rows * ret_n_cols == 0:
            return matrix(ZZ, ret_n_rows, ret_n_cols, [])
        for kf in kfactors:
            ret = ret.tensor_product(kf)
        return ret

    def middle_action_matrix(self, x, f, z, y):
        ret_n_rows = 1
        ret_n_cols = 1
        ret = matrix(ZZ, 1, 1, [1])
        fb = self.break_string(f)
        for i, cat in self.ecats:
            kf = cat.middle_action_matrix(x[i], fb[i], z[i], y[i])
            ret_n_rows *= kf.nrows()
            ret_n_cols *= kf.ncols()
            if ret_n_rows * ret_n_cols != 0:
                ret = ret.tensor_product(kf)
        # This is to avoid a 0-dim bug present in my version of sage
        if ret_n_rows * ret_n_cols == 0:
            return matrix(ZZ, ret_n_rows, ret_n_cols, [])
        return ret

    def right_action_matrix(self, x, y, f, z):
        ret_n_rows = 1
        ret_n_cols = 1
        kfactors = []
        fb = self.break_string(f)

        for i, cat in self.ecats:
            kf = cat.right_action_matrix(x[i], y[i], fb[i], z[i])
            ret_n_rows *= kf.nrows()
            ret_n_cols *= kf.ncols()
            kfactors += [kf]
        # This is to avoid a 0-dim bug present in my version of sage
        if ret_n_rows * ret_n_cols == 0:
            return matrix(ZZ, ret_n_rows, ret_n_cols, [])
        ret = matrix(ZZ, 1, 1, [1])
        for kf in kfactors:
            ret = ret.tensor_product(kf)
        return ret

    def op(self):
        if self.op_cat is None:
            self.op_cat = ProductCategory(*[cat.op() for cat in self.cats])
            self.op_cat.op_cat = self
        return self.op_cat


class Functor(object):
    # To build a functor, you supply a source category,
    # a target category, and a law
    # law(x, f, y)
    # that returns a triple (x', f', y')
    # and must be functorial.

    def __init__(self, source, law, target):
        self.source = source
        self.law = law
        self.target = target
        self.objs = {}
        self.acts = {}

    def action_matrix(self, x, y):
        if (x, y) in self.acts:
            return self.acts[(x, y)]
        rows = self.source.hom(x, y)
        xx = self(x)
        yy = self(y)
        cols = self.target.hom(xx, yy)
        ret = matrix(ZZ, len(rows), len(cols), [1 if self.law(x, r, y) == (xx, c, yy) else 0 for r in rows for c in cols])
        self.acts[(x, y)] = ret
        return ret

    # Can be called on a single object
    # or on a triple (x, f, y)
    # or on a CatMat
    def __call__(self, *args):
        if len(args) == 1:
            if isinstance(args[0], CatMat):
                cm = args[0]
                ring = cm.ring
                vd = []
                for i, x in enumerate(cm.source):
                    for j, y in enumerate(cm.target):
                        vd += cm.entry_vector(i, j) * self.action_matrix(x, y)
                new_source = [self(x) for x in cm.source]
                new_target = [self(y) for y in cm.target]
                return CatMat(ring, self.target, new_source, vector(cm.ring, vd), new_target)
            o = args[0]
            if o in self.objs:
                return self.objs[o]
            ret = self.law(o, self.source.identity(o), o)[0]
            self.objs[o] = ret
            return ret

        if len(args) == 3:
            return self.law(*args)

        raise SyntaxError('Arguments could not be interpreted: ' + str(args))

    # Should return a functor of some kind
    # but current implementation is very crude
    # and just returns a function that accepts MatrixRepresentations and dgModules
    def upper_star(self):
        def upper_star_function(module):
            if isinstance(module, MatrixRepresentation):
                def law(x, f, y):
                    return module(*self(x, f, y))
                return MatrixRepresentation(self.source, module.ring, law, target_cat=module.target_cat)

            if isinstance(module, dgModule):
                def d_laws(k):
                    def d_law(x, dd):
                        return module.differential(x, dd, a=k)
                    return d_law

                def f_law(dd, x, f, y):
                    return module.module_in_degree(dd)(*self(x, f, y))

                return dgModule(self.source, module.ring, f_law,
                                [d_laws(k) for k in range(module.n_diff)], target_cat=module.target_cat)

        return upper_star_function

    def test(self):
        for x in self.source.objects:
            for y in self.source.objects:
                for z in self.source.objects:
                    for f in self.source.hom(x, y):
                        for g in self.source.hom(y, z):
                            if self(x, self.source.compose(x, f, y, g, z), z)[1] != \
                              self.target.compose(self(x), self(x, f, y)[1], self(y), self(y, g, z)[1], self(z)):
                                print 'Functoriality fails for the morphisms ' + str((x, f, y, g, z)) + '.'


# CatMat is the class for matrices over a category
# Main job is to implement M*N, M<<N, M>>N, ~M, and +M
# Also has classmethods for these operations with sagemath matrices
class CatMat(object):

    # source and target are the row and column labels
    # v a vector whose entries give the matrix
    # The ordering:
    #   upper left entry is first.
    #   then the entry just right of it,
    #   then the rest of the first row,
    #   then the next row, left to right.
    #   etc.
    # If you don't want to deal with that, then use the
    # class method from_string.
    #
    # Actually, though, on reflection I think rows and columns
    # should certainly not be (always) indexed 0, 1, 2, ..., k
    # since we often will want more interesting indexing data
    # The source objects and target objects should be allowed
    # to be dictionaries once I get around to it.
    #
    # TODO: reimplement so that the entries are stored as a dict of entries
    # TODO: and where the source and target can be lists of hashable things
    # TODO: and then implement slicing
    def __init__(self, ring, cat, source, data_vector, target):
        """

        :type cat: FiniteCategory
        """
        self.cat = cat
        self.ring = ring
        self.source = source
        self.target = target
        # I think sparse vectors are allowed here
        # but I haven't tested this.
        self.data_vector = data_vector
        self.intervals = {}
        self.m_to_n = {}
        self.n_to_m = {}
        # We should also have a dict going
        # where we have evaluated (-,d) and (d,-) on self
        count = 0
        for i, x in enumerate(source):
            for j, y in enumerate(target):
                h = self.cat.hom(x, y)
                self.intervals[(i, j)] = (count, count + len(h))
                for f in h:
                    self.m_to_n[(i, f, j)] = count
                    self.n_to_m[count] = (i, f, j)
                    count += 1
        self.ambient_rank = count
        if len(data_vector) != count:
            raise SyntaxError('Matrix cannot be built from this data_vector, which has rank '
                              + str(len(data_vector)) + '.  Expected rank: ' + str(count))

        self.res = {0: self}

    def nrows(self):
        return len(self.source)

    def ncols(self):
        return len(self.target)

    @classmethod
    def identity_matrix(cls, ring, cat, source_target):
        vd = []
        for i, x in enumerate(source_target):
            for j, y in enumerate(source_target):
                h = len(cat.hom(x, y))
                if i == j:
                    one_position = cat.morphism_to_number(x, cat.identity(x), x)
                    vd += [0] * one_position
                    vd += [1]
                    vd += [0] * (h - one_position - 1)
                else:
                    vd += [0] * h
        return CatMat(ring, cat, source_target, vector(ring, vd), source_target)

    @classmethod
    def zero_matrix(cls, ring, cat, source, target):
        if cat is None:
            return zero_matrix(ring, source, target)
        z = 0
        for x in source:
            for y in target:
                z += len(cat.hom(x, y))
        return CatMat(ring, cat, source, zero_vector(ring, z), target)

    @classmethod
    def from_string(cls, ring, cat, source, matrix_string, target):
        matrix_string = matrix_string.replace(' ', '')
        r = len(source)
        c = len(target)

        def read_next(s, t, string):
            ss = string
            hom_list = list(cat.hom(s, t))
            hom_list.sort(key=len, reverse=True)
            for f in hom_list:
                ss = ss.replace(f, '~' * len(f))
            end_codon_position = [ss.find(','), ss.find(']')]
            # What happens if this codon is not found?
            # It would mean that some morphism has characters
            # that imitate the syntax of a matrix.
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
        # output matrix is still strings.
        return CatMat.from_string_entries(ring, cat, source, output_matrix, target)

    # Here list_of_lists_of_strings must be len(source)
    # lists of vectors, with each list of length len(target).
    # We don't fall into the 0 x n trap because the source and target are given.
    @classmethod
    def from_string_entries(cls, ring, cat, source, list_of_lists_of_strings, target):
        r = len(source)
        c = len(target)
        lls = list_of_lists_of_strings
        if len(lls) != r:
            raise SyntaxError('Incorrect number of rows.  Found '
                              + str(len(lls)) + ', expected ' + str(r) + '.')
        for i, row in enumerate(lls):
            if len(row) != c:
                raise SyntaxError('Incorrect number of columns in row ' + str(i) +
                                  '.  Found ' + str(len(row)) + ', expected ' + str(c) + '.')

        def string_to_ring(ss):
            s = ss.replace(' ', '')
            if s == '':
                return ring(1)
            if s[0] == '+':
                return string_to_ring(s[1:])
            if s == '-':
                return ring(-1)
            return ring(s)
        llv = []
        for i, x in enumerate(source):
            lv = []
            for j, y in enumerate(target):
                h = cat.hom(x, y)
                v = zero_vector(ring, len(h))
                if lls[i][j] == '0':
                    lv.append(v)
                    continue
                morphs, coeffs = cat.split_string_on_morphisms(x, lls[i][j], y)
                if morphs[0] == '':
                    morphs = morphs[1:]
                for k, f in enumerate(morphs):
                    try:
                        ring_element = string_to_ring(coeffs[k])
                    except TypeError as e:
                        raise TypeError('While parsing the coefficient of the morphism "' + morphs[k] +
                                        '" which appears as term ' + str(k) + ' in entry ' + str((i, j)) +
                                        ', the following error was generated: ' + e.message)
                    v[cat.morphism_to_number(x, f, y)] += ring_element
                lv.append(v)
            llv.append(lv)
        return CatMat.from_vector_entries(ring, cat, source, llv, target)

    # Here list_of_lists_of_vectors must be len(source)
    # lists of vectors, with each list of length len(target).
    # We don't fall into the 0 x n trap because the source and target are given.
    @classmethod
    def from_vector_entries(cls, ring, cat, source, list_of_lists_of_vectors, target):
        r = len(source)
        c = len(target)
        llv = list_of_lists_of_vectors
        if len(llv) != r:
            raise SyntaxError('Incorrect number of rows.  Found '
                              + str(len(llv)) + ', expected ' + str(r) + '.')
        for i, row in enumerate(llv):
            if len(row) != c:
                raise SyntaxError('Incorrect number of columns in row ' + str(i) +
                                  '.  Found ' + str(len(row)) + ', expected ' + str(c) + '.')
        vd = []
        for lv in llv:
            for v in lv:
                vd.extend(v)

        return cls(ring, cat, source, vector(ring, vd), target)

    # Here table is a list of lists of CatMats
    # to be assembled into a single CatMat.
    # If an entry is not a CatMat, it will be replaced with a zero matrix.
    # TODO: that's horrible
    # In all but casual usage: provide ring, cat, sources, and targets up front
    # to avoid the 0 x n and n x 0 traps.  Otherwise these will be inferred
    # by looking at table.
    @classmethod
    def block_matrix(cls, table, ring=None, cat=None, sources=None, targets=None):
        if ring is None:
            try:
                ring = table[0][0].ring
            except AttributeError:
                ring = table[0][0].base_ring()
        if cat is None:
            try:
                cat = table[0][0].cat
            except AttributeError:
                # TODO: This line is probably falling in the 0 x n trap
                return block_matrix(table)
        if sources is None:
            sources = []
            for i, row in enumerate(table):
                found = False
                for entry in row:
                    if isinstance(entry, CatMat):
                        sources += [entry.source]
                        found = True
                        break
                if not found:
                    # TODO:
                    # There is another way to infer sources and targets
                    # when a nonzero scalar appears in the table
                    # we know that multiple of the identity matrix goes there
                    # and so that block is square.
                    # It makes sense to use this information in practice.
                    raise SyntaxError('Could not infer source of row ' + str(i))
        if targets is None:
            targets = []
            for j in range(len(table[0])):
                found = False
                for i in range(len(table)):
                    if isinstance(table[i][j], CatMat):
                        targets += [table[i][j].target]
                        found = True
                        break
                if not found:
                    raise SyntaxError('Could not infer target of column ' + str(j))
        for i, row in enumerate(table):
            for j, entry in enumerate(row):
                if isinstance(entry, CatMat):
                    if list(entry.source) != list(sources[i]):
                        raise SyntaxError('Entry ' + str((i, j)) + ' has wrong source.  Found ' +
                                          str(entry.source) + ', expected ' + str(sources[i]) + ".")
                    if list(entry.target) != list(targets[j]):
                        raise SyntaxError('Entry ' + str((i, j)) + ' has wrong target.  Found ' +
                                          str(entry.target) + ', expected ' + str(targets[i]) + ".")
                else:
                    try:
                        ring(entry)
                    except:
                        raise SyntaxError('Could not interpret entry ' + str((i, j)) + ' as either ' +
                                          'a CatMat or a scalar.')
                    if ring(entry) == ring(0):
                        table[i][j] = CatMat.zero_matrix(ring, cat, sources[i], targets[j])
                    else:
                        if sources[i] == targets[j]:
                            table[i][j] = ring(entry) * CatMat.identity_matrix(ring, cat, sources[i])
                        else:
                            raise SyntaxError('A nonzero scalar is only permitted in an entry where ' +
                                              'an identity matrix makes sense; this is not the case ' +
                                              'for block entry ' + str((i, j)))
        vd = []
        for i, s in enumerate(sources):
            for k in range(len(s)):
                for j, t in enumerate(targets):
                    for l in range(len(t)):
                        vd.extend(table[i][j].entry_vector(k, l))

        source = []
        for s in sources:
            for x in s:
                source += [x]

        target = []
        for t in targets:
            for y in t:
                target += [y]

        return cls(ring, cat, source, vector(ring, vd), target)

    # If there's any chance that cat_mats might have length zero
    # then it is important to provide the three optional arguments
    @classmethod
    def block_row(cls, cat_mats, ring=None, cat=None, source=None):
        if (ring is None or cat is None or source is None) and len(cat_mats) == 0:
            raise ValueError('Cannot infer optional arguments since no columns were given.')
        if ring is None:
            ring = cat_mats[0].ring
        if cat is None:
            try:
                cat = cat_mats[0].cat
            except AttributeError:
                return block_matrix([cat_mats], ring=ring)
        if source is None:
            source = cat_mats[0].source
        return CatMat.block_matrix([cat_mats], ring=ring, cat=cat,
                                   sources=[source], targets=[m.target for m in cat_mats])

    # If cat=None, then we assume that these cat_mats are actually sagemath matrices
    @classmethod
    def block_diagonal(cls, cat_mats, ring=None, cat=None):
        k = len(cat_mats)
        # This code is in flux.  TODO: cat=None should mean it's a sagemath matrix
        if False:
            raise ValueError('Cannot infer optional arguments since no blocks were given.')
        if ring is None:
            try:
                ring = cat_mats[0].ring
            except AttributeError:
                return block_diagonal_matrix(cat_mats)
        if cat is None:
            try:
                return block_diagonal_matrix(cat_mats)
            # AttributeError?
            except (TypeError, AttributeError):
                cat = cat_mats[0].cat

        sources = [m.source for m in cat_mats]
        targets = [m.target for m in cat_mats]
        table = [[cat_mats[i] if i == j else 0 for j in range(k)] for i in range(k)]
        return CatMat.block_matrix(table, ring=ring, cat=cat, sources=sources, targets=targets)

    @classmethod
    def kronecker_product(cls, *mats_pre):
        if type(mats_pre[0]) is str:
            sep = mats_pre[0]
            mats = mats_pre[1:]
        else:
            sep = ','
            mats = mats_pre
        row_counts = [range(m.nrows()) for m in mats]
        col_counts = [range(m.ncols()) for m in mats]

        #zero_dim_matrix = any([(m.nrows() == 0) or (m.ncols() == 0) for m in mats])

        cmf = [i for i, m in enumerate(mats) if isinstance(m, CatMat)]
        cat_factors = [mats[i].cat for i in cmf]
        prod_cat = ProductCategory(sep, *cat_factors)

        one_fold = (len(cat_factors) == 1)


        if len(mats) == 0:
            # ZZ is the initial ring, so this is reasonable
            return matrix(ZZ, 1, 1, [1])

        # From now on mats cannot be empty
        # so we can set about detecting the ring
        if len(cmf) == 0:
            ring = mats[0].base_ring()
        else:
            ring = mats[cmf[0]].ring

        # Check if every factor is a usual sagemath matrix;
        # in this case build and return the usual kronecker_product
        # with care to handle 0xn and nx0 traps
        if len(cmf) == 0:
            source = 1
            target = 1
            for m in mats:
                source *= m.nrows()
                target *= m.ncols()

            # No sense running the loops if the output has no entries
            if source == 0 or target == 0:
                return matrix(ring, source, target, [])

            entries = []
            for r in itertools.product(*row_counts):
                for c in itertools.product(*col_counts):
                    e = ring(1)
                    for f, (i, j) in enumerate(zip(r, c)):
                        e *= mats[f][i, j]
                    entries += [e]

            # This is the correct order to give the entries of a sagemath matrix
            return matrix(ring, source, target, entries)


        # From now on, we may assume that there is at least one CatMat factor
        # and so the output will be a CatMat.
        #
        # Prepare sources and targets
        source = []
        sources = dict()
        for r in itertools.product(*row_counts):
            sources[r] = tuple([mats[i].source[j] for i, j in enumerate(r) if i in cmf])
            if one_fold:
                sources[r] = sources[r][0]
            source += [sources[r]]

        target = []
        targets = dict()
        for c in itertools.product(*col_counts):
            targets[c] = tuple([mats[i].target[j] for i, j in enumerate(c) if i in cmf])
            if one_fold:
                targets[c] = targets[c][0]
            target += [targets[c]]

        # If the resulting matrix has no entries, then we are done:
        if len(source) == 0 or len(target) == 0:
            return CatMat.zero_matrix(ring, prod_cat, source, target)

        # We may now assume that the matrix has at least one row
        # and at least one column.
        blocks = []
        for r in itertools.product(*row_counts):
            block_row = []
            for c in itertools.product(*col_counts):
                dvs = []
                for f, (i, j) in enumerate(zip(r, c)):
                    if f in cmf:
                        dvs += [mats[f].entry_vector(i, j)]
                    else:
                        dvs += [vector(ring, [mats[f][i, j]])]
                # We rely on this vector matching the morphism ordering
                # used in the definition of ProductCategory
                dv = vector(ring, [prod(et) for et in itertools.product(*dvs)])
                block_row += [CatMat(ring, prod_cat, [sources[r]], dv, [targets[c]])]
            blocks += [block_row]

        return CatMat.block_matrix(blocks, cat=prod_cat)

    # Returns a CatMat with a single column
    def column(self, j):
        vd = []
        for i, x in enumerate(self.source):
            vd.extend(self.entry_vector(i, j))
        return CatMat(self.ring, self.cat, self.source, vector(self.ring, vd), [self.target[j]])

    # Returns a list of column CatMats
    def columns(self):
        columns = []
        for j, y in enumerate(self.target):
            columns += [self.column(j)]
        return columns

    # Returns a CatMat with a single row
    def row(self, i):
        vd = []
        for j, y in enumerate(self.target):
            vd.extend(self.entry_vector(i, j))
        return CatMat(self.ring, self.cat, [self.source[i]], vector(self.ring, vd), self.target)

    # Returns a list of row CatMats
    def rows(self):
        rows = []
        for i, x in enumerate(self.source):
            rows += [self.row(i)]
        return rows

    def monomial_to_number(self, i, f, j):
        return self.m_to_n[(i, f, j)]

    def number_to_monomial(self, n):
        return self.n_to_m[n]

    # returns a vector giving the coefficients for an entry
    def entry_vector(self, i, j):
        x = self.source[i]
        y = self.target[j]
        a, b = self.intervals[(i, j)]
        return self.data_vector[a:b]

    def entry_to_latex(self, i, j):
        x = self.source[i]
        y = self.target[j]
        h = self.cat.hom(x, y)
        v = self.entry_vector(i, j)
        ret = ''
        for i, a in enumerate(v):
            if a != self.ring(0):
                if a == self.ring(1):
                    ret += ' + ' + self.cat.morphism_to_latex(x, h[i], y)
                    continue
                if a == self.ring(-1):
                    ret += ' - ' + self.cat.morphism_to_latex(x, h[i], y)
                    continue
                ret += ' + ' + str(a) + self.cat.morphism_to_latex(x, h[i], y)
        if ret == '':
            return '0'
        if ret[0:3] == ' + ':
            ret = ret[3:]
        ret = ret.replace(' + -', ' - ')
        return ret

    def to_latex(self):
        if len(self.source) == 0 or len(self.target) == 0:
            ret = '\\mbox{A CatMat of format '
            ret += '$' + str([self.cat.object_to_latex(o) + '\\,' for o in self.source])
            ret += ' \\to '
            ret += str([self.cat.object_to_latex(o) + '\\,' for o in self.target]) + '$}'
            return ret
        latex.add_to_preamble("\\usepackage{blkarray}")
        ret = ''
        # ret = '\left(\n'
        ret += '\\begin{blockarray}{' + ('c'*(len(self.target) + 1)) + '}'
        for y in self.target:
            ret += ' & '
            ret += self.cat.object_to_latex(y)
        ret += '\\' + '\\' + '\n'
        ret += '\\begin{block}{c[' + ('c'*(len(self.target))) + ']}\n'
        for i, x in enumerate(self.source):
            ret += self.cat.object_to_latex(x)
            for j, y in enumerate(self.target):
                ret += ' & ' + self.entry_to_latex(i, j)
            ret += '\\' + '\\' + '\n'
        ret += '\\end{block}\n'
        ret += '\\end{blockarray}'
        # ret += '\\right)'
        return ret

    def show(self, title=None):
        if title is None:
            view([LatexExpr(self.to_latex())], tightpage=True)
        else:
            view([LatexExpr(title), LatexExpr(self.to_latex())], title=title, tightpage=True)

    def output_latex(self, filename):
        f = open(filename, 'w')
        f.write('\\documentclass{standalone}\n\\usepackage{blkarray}\n\\usepackage{graphics}\\begin{document}\n$$')
        f.write(self.to_latex())
        f.write('\n$$\n\\end{document}')
        f.close()

    def __str__(self):
        # Should return a string for printing
        # but for now we return the latex string
        return self.to_latex()

    # Considering this CatMat as a presentation matrix for a self.cat module,
    # returns a string describing the module at object x
    def coker_at(self, x):
        mi = self.cat.cofree_module(self.ring, [x])(self)
        mc = ChainComplex({-1: mi})
        return mc.homology(0)

    def im_at(self, x):
        mi = self.cat.cofree_module(self.ring, [x])(self)
        fm = FreeModule(self.ring, mi.ncols())
        return fm.submodule(mi.rows())

    def ker_at(self, x):
        mi = self.cat.cofree_module(self.ring, [x])(self)
        mc = ChainComplex({0: mi})
        return mc.homology(0)

    # TODO: if other is a scalar, then scale.  If it is a sagemath matrix, then perform a col op
    def __mul__(self, other):
        if len(self.target) != len(other.source):
            raise ValueError('Number of columns does not match number of rows: ' +
                             str((len(self.target), len(other.source))))
        for j, y in enumerate(self.target):
            if y != other.source[j]:
                raise ValueError('Column ' + str(j) + ' of the first matrix does not ' +
                                 'match its corresponding row in the second matrix')

        a = self.source
        b = self.target
        c = other.target

        def product_entry_summand(i, j, k):
            vd = [self.entry_vector(i, j) * self.cat.middle_action_matrix(a[i], f, c[k], b[j]) *
                  other.entry_vector(j, k)
                  for f in self.cat.hom(a[i], c[k])]
            return vector(self.ring, vd)

        def product_entry(i, k):
            ret = zero_vector(self.ring, len(self.cat.hom(a[i], c[k])))
            for j in range(len(b)):
                ret += product_entry_summand(i, j, k)
            return ret
        product_data = []
        for i in range(len(a)):
            for k in range(len(c)):
                product_data += product_entry(i, k)
        return CatMat(self.ring, self.cat, a, vector(self.ring, product_data), c)

    def __add__(self, other):
        if self.source != other.source or self.target != other.target:
            raise ValueError('Matrices have different row- or column-labels and cannot be added')
        return CatMat(self.ring, self.cat, self.source, self.data_vector + other.data_vector, self.target)

    def __eq__(self, other):
        return self.source == other.source and self.target == other.target and self.data_vector == other.data_vector

    # TODO: if the argument is a sagemath matrix instead of a scalar, then it should do a row operation
    # row op should be... first find the rows as data_vectors; then build a sagemath matrix; then multiply; reassemble.
    # Scaling a matrix should happen on the left
    def __rmul__(self, scalar):
        return CatMat(self.ring, self.cat, self.source, self.data_vector * scalar, self.target)

    # Returns the transpose
    # which is a matrix over the opposite category
    def transpose(self):
        return CatMat.from_vector_entries(self.ring, self.cat.op(), self.target,
                                   [[self.entry_vector(i, j) for i in range(len(self.source))]
                                                      for j in range(len(self.target))], self.source)

    # Returns a matrix M so that
    # M * self = 0
    # and this composition is exact whenever you apply (d,-)
    # This is the first step in a projective resolution by free left modules
    def step_left(self):
        return (self.transpose().step_right()).transpose()

    # If you have a usual sage matrix and you want to step right
    # this is what you do.
    @classmethod
    def matrix_step_right(cls, m):
        rk_gens = m.right_kernel().gens()
        if len(rk_gens) == 0:
            return zero_matrix(m.base_ring(), m.ncols(), 0)
        return matrix(rk_gens).transpose()

    @classmethod
    def matrix_step_left(self, m):
        return CatMat.matrix_step_right(m.transpose()).transpose()


    # TODO: do this with rows instead of columns?
    # Returns a matrix N so that
    # self * N = 0
    # and this composition is exact whenever you apply (-,d)
    # This is the first step in a projective resolution by free right modules
    def step_right(self):
        potential_columns = []
        for d in self.cat.objects:
            # Apply (-,o) to self
            # to get an ordinary block matrix
            fo = self.cat.cofree_module(self.ring, (d,))
            #ker = matrix(fo(self).right_kernel().gens()).transpose()
            ker = CatMat.matrix_step_right(fo(self))
            cols = []
            for col in ker.columns():
                cols += [CatMat(self.ring, self.cat, self.target, col, [d])]
            potential_columns += cols
        npc = len(potential_columns)

        column_evals = {}
        prices = [0] * npc
        for d in self.cat.objects:
            fd = self.cat.cofree_module(self.ring, (d,))
            column_evals[d] = [fd(col) for col in potential_columns]
            for i, m in enumerate(column_evals[d]):
                prices[i] += m.ncols()
        index_price = list(enumerate(prices))
        # We try to drop expensive columns first.
        # If we do have to keep one, then at least we will get lots of benefit from it.
        index_price.sort(key=lambda p: p[1], reverse=True)
        greedy_order = [p[0] for p in index_price]
        current_columns = [True] * npc
        for i in greedy_order:
            current_columns[i] = False
            for d in self.cat.objects:
                md = block_matrix([[column_evals[d][j] for j in range(npc) if current_columns[j]]])
                if not column_evals[d][i].column_space().is_submodule(md.column_space()):
                    current_columns[i] = True
                    break
        chosen_columns = [potential_columns[j] for j in range(npc) if current_columns[j]]
        targets = [[col.target[0]] for col in chosen_columns]
        return CatMat.block_matrix([chosen_columns], cat=self.cat, ring=self.ring,
                                   sources=[self.target], targets=targets)

    def solve_left(self, other):
        return (self.transpose().solve_right(other.transpose())).transpose()

    @classmethod
    def matrix_solve_right(cls, m, other):
        f = Hom(m.base_ring()**m.ncols(), m.base_ring()**m.nrows())(m.transpose())
        ret = matrix(m.base_ring(), m.ncols(), 0, [])
        # If other is a single column and not a matrix, then other.columns() will fail.
        try:
            cols = other.columns()
        except AttributeError:
            cols = [other]
        for j, one_col in enumerate(cols):
            try:
                solve_vec = vector(m.base_ring(), f.lift(one_col))
            except ValueError:
                raise ValueError('Matrix equation has no solution: column ' + str(j) + ' does not lift.')
            ret = ret.augment(matrix(m.base_ring(), m.ncols(), 1, list(solve_vec)))
        return ret

    def solve_right(self, other):
        # We want to perform column operations on self
        # until we obtain other.  And we want to keep track
        # of what we did.
        # We can do each column individually by solving a local problem at (-,d)
        # where d is the column label.
        cols = []
        for j, col in enumerate(other.columns()):
            d = col.target[0]
            fd = self.cat.cofree_module(self.ring, (d,))
            one_col = fd(col).column(self.cat.morphism_to_number(d, self.cat.identity(d), d))
            # This should be precomputed or saved:
            solve_vec = CatMat.matrix_solve_right(fd(self), one_col).column(0)
            #mat = fd(self)
            #f = Hom(self.ring**mat.ncols(), self.ring**mat.nrows())(mat.transpose())
            ## solve_vec = fd(self).solve_right(one_col)
            #try:
            #    solve_vec = vector(self.ring, f.lift(one_col))
            #except ValueError:
            #    raise ValueError('Matrix equation has no solution: column ' + str(j) + ' does not lift.')
            cols += [CatMat(self.ring, self.cat, self.target, solve_vec, [d])]
        return CatMat.block_row(cols, ring=self.ring, cat=self.cat, source=self.target)

    # Returns either a two-sided inverse or None
    def inverse(self):
        source_id = CatMat.identity_matrix(self.ring, self.cat, self.source)
        target_id = CatMat.identity_matrix(self.ring, self.cat, self.target)
        try:
            inv = self.solve_right(source_id)
            if self * inv == target_id:
                return inv
            else:
                return None
        except ValueError:
            return None

    # Satisfies (A << P) * P == A
    # Raises a ValueError when there is no solution
    def __lshift__(self, other):
        # This nonsense line was here:
        # other.solve_left(self)
        # who wrote this code?
        return (other.transpose() >> self.transpose()).transpose()

    # Satisfies Q * (Q >> B) == B
    # Raises a ValueError when there is no solution
    def __rshift__(self, other):
        return self.solve_right(other)

    # Satisfies (~M) * M == 0
    # and if A * M == 0 for some A
    # then (A << (~M)) exists.
    def __invert__(self):
        return self.step_left()

    # Satisfies M * (+M) == 0
    # and if M * B == 0 for some B
    # then ((+M) >> B) exists.
    def __pos__(self):
        return self.step_right()

    def step_right_dgModule(self):
        def d_law(x, (d,)):
            if d <= -2:
                return CatMat.identity_matrix(self.ring, self.cat, [])
            if d == -1:
                return CatMat.zero_matrix(self.ring, self.cat, [], self.source)
            if d in self.res:
                return self.res[d]
            self.res[d] = +d_law(x, (d - 1,))
            return self.res[d]

        def f_law((d,), x, f, y):
            return CatMat.identity_matrix(self.ring, self.cat, d_law(x, (d - 1,)).target)

        return dgModule(TerminalCategory, self.ring, f_law, [d_law], target_cat=self.cat, cache=False)



# Class for matrix representations
# Nice conversion methods to and from dgModules
# If you give it a dictionary that takes objects
# and returns matrices that can be multiplied
# against the outgoing maps
# then it provides a dictionary with smaller matrices
# that has the same span.



class MatrixRepresentation(object):
    def __init__(self, cat, ring, law, target_cat=None):
        self.cat = cat
        self.ring = ring
        self.law = law
        self.pre = {}
        self.ranks = {}
        self.target_cat = target_cat
        self.cat_mat = not (target_cat is None)
        self.res = {}
        # The information below 0 in res is stored here
        self.gen_info_pre = None

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
        for i, x in enumerate(cm.source):
            block_row = []
            for j, y in enumerate(cm.target):
                if self.cat_mat:
                    block_entry = CatMat.zero_matrix(self.ring, self.target_cat, self.rank(x), self.rank(y))
                else:
                    block_entry = zero_matrix(self.ring, self.rank(x), self.rank(y))
                coefs = cm.entry_vector(i, j)
                for k, f in enumerate(self.cat.hom(x, y)):
                    block_entry += coefs[k] * self(x, f, y)
                block_row += [block_entry]
            block_rows += [block_row]
        if self.cat_mat:
            sources = [self.rank(x) for x in cm.source]
            targets = [self.rank(y) for y in cm.target]
            return CatMat.block_matrix(block_rows, self.ring, self.target_cat, sources, targets)
        else:
            rows = sum([self.rank(x) for x in cm.source])
            cols = sum([self.rank(y) for y in cm.target])
            if rows * cols == 0:
                return zero_matrix(self.ring, rows, cols)
            else:
                return block_matrix(block_rows)

    def rank(self, x):
        if x in self.ranks:
            return self.ranks[x]
        if self.cat_mat:
            ret = self.law(x, self.cat.identity(x), x).source
        else:
            ret = self.law(x, self.cat.identity(x), x).nrows()
        self.ranks[x] = ret
        return ret

    # If we compute the rank by some other means
    # then we can tell the representation about it
    # using this line.
    def learn_rank(self, x, rk):
        if x in self.ranks:
            pass
        else:
            self.ranks[x] = rk

    # subspanners is a dict whose keys are the objects
    # of self.cat and whose values are matrices
    # The function finds a subset of these generators
    # that still spans just as much, and
    # returns a list of the degrees for these gens
    # as well as a dict whose keys are objects, and
    # whose values are matrices.  These matrices
    # give the components of the incoming map from
    # the representable projective.
    #
    # Note that the subrepresentation may not be a matrix
    # representation.  (Over a field or a PID it will be)
    # This assumption was required in earlier implementations
    # But this code allows matrices over a general cat.
    #
    # If cat_mat, then the return value of points is
    # a list of pairs where the first coordinate is an object
    # of self.target_cat and the second is an object of self.cat
    def prune_subspanners(self, subspanners):
        # nrows() works for CatMats and for sagemath matrices
        potential_gens = [(x, i) for x in self.cat.objects for i in range(subspanners[x].nrows())]
        npg = len(potential_gens)
        pointwise_spans = dict()
        for x, i in potential_gens:
            for y in self.cat.objects:
                rows = []
                for f in self.cat.hom(x, y):
                    if self.cat_mat:
                        rows += [(subspanners[x].row(i) * self(x, f, y))]
                    else:
                        rows += [(subspanners[x][i:i + 1] * self(x, f, y))]

                if self.cat_mat:
                    sources = [[subspanners[x].source[i]]] * len(rows)
                    targets = [self.rank(y)]
                    pointwise_spans[x, i, y] = CatMat.block_matrix([[r] for r in rows],
                                                                   self.ring, self.target_cat, sources, targets)
                else:
                    if len(rows) == 0:
                        pointwise_spans[x, i, y] = zero_matrix(self.ring, 0, self.rank(y))
                    else:
                        pointwise_spans[x, i, y] = block_matrix([[r] for r in rows])
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
                my_table = [[pointwise_spans[z, k, y]] for z, k in potential_gens if current_gens[z, k]]
                if self.cat_mat:
                    sources = [pointwise_spans[z, k, y].source for z, k in potential_gens if current_gens[z, k]]
                    targets = [self.rank(y)]
                    my = CatMat.block_matrix(my_table, self.ring, self.target_cat, sources, targets)
                    try:
                        pointwise_spans[x, i, y] << my
                    except ValueError:
                        current_gens[x, i] = True
                        break
                else:
                    if len(my_table) == 0:
                        my = zero_matrix(self.ring, 0, self.rank(y))
                    else:
                        my = block_matrix(my_table)
                    if not pointwise_spans[x, i, y].row_space().is_submodule(my.row_space()):
                        current_gens[x, i] = True
                        break
        chosen_gens = [(x, i) for x, i in potential_gens if current_gens[x, i]]
        if self.cat_mat:
            points = [(x, subspanners[x].source[i]) for x, i in chosen_gens]
        else:
            points = [x for x, i in chosen_gens]
        components = dict()

        if self.cat_mat:
            for y in self.cat.objects:
                table = [[pointwise_spans[x, i, y]] for x, i in chosen_gens]
                sources = [pointwise_spans[x, i, y].source for x, i in chosen_gens]
                targets = [self.rank(y)]
                components[y] = CatMat.block_matrix(table, self.ring, self.target_cat, sources, targets)
        else:
            for y in self.cat.objects:
                table = [[pointwise_spans[x, i, y]] for x, i in chosen_gens]
                total_rows = sum([m[0].nrows() for m in table])
                if total_rows == 0:
                    components[y] = zero_matrix(self.ring, 0, self.rank(y))
                else:
                    components[y] = block_matrix(table)
        # Should return triple
        # degrees, generators, components
        # there is mild redundancy because
        # components holds the generators
        # but it will be much more convenient this way.
        gens = [subspanners[x].row(i) for x, i in chosen_gens]
        return points, gens, components

    def gen_info(self):
        if self.gen_info_pre is None:
            all_gens = dict()
            for x in self.cat.objects:
                if self.cat_mat:
                    all_gens[x] = CatMat.identity_matrix(self.ring, self.target_cat, self.rank(x))
                else:
                    all_gens[x] = identity_matrix(self.rank(x))
            gen_points, gens, surj = self.prune_subspanners(all_gens)
            self.gen_info_pre = gen_points, gens, surj
        return self.gen_info_pre

    # This code builds a presentation matrix over self.cat
    def presentation(self):
        if 0 in self.res:
            return self.res[0]
        # First get spanners
        gen_points, gens, surj = self.gen_info()

        # then take kernels of components
        ker_gens = dict()
        for x in self.cat.objects:
            if self.cat_mat:
                ker_gens[x] = surj[x].step_left()
            else:
                ker_gens[x] = CatMat.matrix_step_left(surj[x])

        # now build the free representation left-Kan-extended from the generators
        if self.cat_mat:
            new_cat = ProductCategory(self.cat, self.target_cat.op())

            def lan_law(x, f, y):
                diag = []
                for s, t in gen_points:
                    sm = self.cat.right_action_matrix(s, x, f, y)
                    tm = CatMat.identity_matrix(self.ring, self.target_cat, [t])
                    diag += [CatMat.kronecker_product(sm, tm)]
                return CatMat.block_diagonal(diag, self.ring, self.target_cat)
        else:
            new_cat = self.cat

            def lan_law(x, f, y):
                diag = []
                for s in gen_points:
                    sm = self.cat.right_action_matrix(s, x, f, y)
                    diag += [sm]
                return block_diagonal_matrix(diag)
        free_on_gens = MatrixRepresentation(self.cat, self.ring, lan_law, target_cat=self.target_cat)

        # then get spanners for those kernels
        rel_points, rels, _ = free_on_gens.prune_subspanners(ker_gens)

        # finally, build the presentation matrix
        if self.cat_mat:
            columns = []
            for p, r in zip(rel_points, rels):
                column = []
                k = 0
                for g in gen_points:
                    dvl = []
                    ey = CatMat.zero_matrix(self.ring, new_cat, [g], [p])
                    for f in self.cat.hom(g[0], p[0]):
                        dvl += list(r.entry_vector(0, k))
                        # Build the 1x1 CatMat with entry f
                        fm = CatMat.from_string(self.ring, self.cat, [g[0]], '[[' + f + ']]', [p[0]])
                        em = CatMat(self.ring, self.target_cat.op(), [g[1]], r.entry_vector(0, k), [p[1]])
                        ey += CatMat.kronecker_product(fm, em)
                        k += 1
                    # Another risky attempt:
                    # column += [[CatMat(self.ring, new_cat, [g], vector(self.ring, dvl), [p])]]
                    column += [[ey]]
                # This was the risky way I did it before:
                # cm = CatMat(self.ring, new_cat, gen_points, r.data_vector, [p])
                # It might be faster, but is it correct?
                cm = CatMat.block_matrix(column, self.ring, new_cat, [[g] for g in gen_points], [[p]])
                columns += [cm]
            self.res[0] = CatMat.block_matrix([columns], self.ring, new_cat, [gen_points], [[p] for p in rel_points])
            return self.res[0]
        else:
            cols = [CatMat(self.ring, self.cat, gen_points, rl, [rp]) for rp, rl in zip(rel_points, rels)]
            sources = [gen_points]
            targets = [[r] for r in rel_points]
            self.res[0] = CatMat.block_matrix([cols], self.ring, new_cat, sources=sources, targets=targets)
            return self.res[0]

    # Returns a dgModule on the terminal category
    # with values in matrices over self.cat
    def resolution(self):
        # This line populates self.res[0]
        self.presentation()

        def d_law(x, (d,)):
            if d <= -2:
                return CatMat.identity_matrix(self.ring, self.res[0].cat, [])
            if d == -1:
                return CatMat.zero_matrix(self.ring, self.res[0].cat, [], self.res[0].source)
            if d in self.res:
                return self.res[d]
            self.res[d] = +d_law(x, (d - 1,))
            return self.res[d]

        def f_law((d,), x, f, y):
            return CatMat.identity_matrix(self.ring, self.res[0].cat, d_law(x, (d - 1,)).target)

        return dgModule(TerminalCategory, self.ring, f_law, [d_law], target_cat=self.res[0].cat, cache=False)

    # This method recomputes differentials
    # so only use it if you want a single degree of homology.
    def homology(self, degree):
        res = self.resolution()
        trivial_rep = self.cat.trivial_representation(self.ring)
        diff_dict = {d: trivial_rep(res.differential('*', (d,))).transpose() for d in range(degree - 1, degree + 2)}
        ch = ChainComplex(diff_dict)
        return ch.homology(degree)












class dgModule(object):

    # laws take the form
    # f_law(degree_tuple, x, f, y)
    # d_laws is a list of laws of the form
    # d_law(x, degree_tuple)
    # where degree_tuple gives the source of the differential
    #
    # Remember to always use a tuple!  If there is only one differential, then degree 2 is actually degree (2,)
    # Make sure that the functions work on every degree_tuple, even ones with negative entries.

    def __init__(self, source, ring, f_law, d_laws, target_cat=None, cache=True):
        self.cat = source
        self.ring = ring
        self.target_cat = target_cat
        self.cat_mat = not (target_cat is None)
        self.f_law = f_law
        self.d_laws = d_laws
        self.n_diff = len(self.d_laws)

        # TODO: implement cache == False
        self.modules = {}
        self.d_pre = {}

        # This variable stores information
        # about generators for the module at multidegree.
        self.gen_info = {}

    def prep_module(self, d):
        if d in self.modules:
            return

        def law(x, f, y):
            return self.f_law(d, x, f, y)
        self.modules[d] = MatrixRepresentation(self.cat, self.ring, law, self.target_cat)

    def rank(self, d, x):
        self.prep_module(d)
        return self.modules[d].rank(x)

    # Here arg can be x, f, y or a single CatMat
    def structure_map(self, d, *arg):
        self.prep_module(d)
        return self.modules[d](*arg)

    def module_in_degree(self, d):
        self.prep_module(d)
        return self.modules[d]

    # x is an object of self.cat
    # d is a degree tuple giving the source of the differential
    # and a is an integer saying which coordinate direction the differential points
    def differential(self, x, d, a=0):
        if (x, d, a) in self.d_pre:
            return self.d_pre[(x, d, a)]
        self.d_pre[(x, d, a)] = self.d_laws[a](x, d)
        return self.d_pre[(x, d, a)]


    @classmethod
    def outer_tensor_product(cls, *args_pre):
        if type(args_pre[0]) is str:
            sep = args_pre[0]
            args = args_pre[1:]
        else:
            sep = ','
            args = args_pre
        q = len(args)
        # Figure out the ring
        if len(args) == 0:
            ring = ZZ
        else:
            ring = args[0].ring

        # Find the new source and target categories
        new_source = ProductCategory(sep, *[otf.cat for otf in args])
        if any([otf.cat_mat for otf in args]):
            new_target = ProductCategory(sep, *[otf.target_cat for otf in args if otf.cat_mat])
        else:
            new_target = None

        # Figure out which differentials belong to which tensor factor
        k = 0
        diff_dict = {}
        for i, otf in enumerate(args):
            for j in range(otf.n_diff):
                diff_dict[k] = (i, j)
                k += 1

        diff_lengths = [otf.n_diff for otf in args]
        ds = [sum(diff_lengths[:i]) for i in range(q + 1)]

        # Define the structure law
        def f_law(degree_tuple, xx, ff, yy):
            kf = []
            for i, f in enumerate(new_source.break_string(ff)):
                x = xx[i]
                y = yy[i]
                kf += [args[i].structure_map(degree_tuple[ds[i]:ds[i + 1]], x, f, y)]
            return CatMat.kronecker_product(sep, *kf)


        # Define the differential laws
        def kth_d_law(k):
            def d_law(x_tuple, degree_tuple):
                kf = []
                for i, x in enumerate(x_tuple):
                    otf = args[i]
                    deg = degree_tuple[ds[i]:ds[i + 1]]
                    otf.prep_module(x)
                    cat = otf.target_cat
                    if otf.cat_mat:
                        kf += [CatMat.identity_matrix(ring, cat, otf.rank(deg, x))]
                    else:
                        kf += [identity_matrix(ring, otf.rank(deg, x))]
                i, j = diff_dict[k]
                kf[k] = args[i].differential(x_tuple[i], degree_tuple[ds[i]:ds[i + 1]], j)
                return CatMat.kronecker_product(sep, *kf)
            return d_law

        return dgModule(new_source, ring, f_law, [kth_d_law(k) for k in range(q)], target_cat=new_target)

    def total_complex(self):
        def f_law((d,), x, f, y):
            b_summands = []
            for v in WeightedIntegerVectors(n=d, weight=[1]*self.n_diff):
                b_summands += [self.structure_map(tuple(v), x, f, y)]
            # The following line will also work if cat_mat is false
            return CatMat.block_diagonal(b_summands, self.ring, self.target_cat)

        def d_law_block_entry(x, (d,), v, w):
            dd = ([j - i for (i, j) in zip(v, w)])
            source = self.rank(tuple(v), x)
            target = self.rank(tuple(w), x)
            if any([z < 0 for z in dd]):
                zz = CatMat.zero_matrix(self.ring, self.target_cat, source, target)
                return zz
            a = dd.index(1)
            sgn = (-1) ** sum(v[0:a])
            dlbe = sgn * self.differential(x, tuple(v), a)
            return dlbe

        def d_law(x, (d,)):
            s = list(IntegerVectors(d, self.n_diff))
            t = list(IntegerVectors(d + 1, self.n_diff))
            sources = [self.rank(tuple(v), x) for v in s]
            targets = [self.rank(tuple(w), x) for w in t]
            # Since s and t always have size at least 1 if n_diff > 0, this line is mostly ok
            b_entries = [[d_law_block_entry(x, (d,), v, w) for w in t] for v in s]
            # TODO: The following line should specify sources and targets.  Current code is sloppy.
            return CatMat.block_matrix(b_entries, ring=self.ring, cat=self.target_cat, sources=sources, targets=targets)

        return dgModule(self.cat, self.ring, f_law, [d_law], target_cat=self.target_cat)

    def hocolim(self):
        def trivial_rep_law(x, f, y):
            return matrix(self.ring, 1, 1, [1])
        trivial_rep = MatrixRepresentation(self.cat, self.ring, trivial_rep_law)

        res = trivial_rep.resolution()

        def ud_law_res(_, dd):
            d_res = (dd[0],)
            d_rep = dd[1:]
            return self.module_in_degree(d_rep)(res.differential('*', d_res))

        def ud_laws_rep(k):
            def ud_law_rep(_, dd):
                d_res = (dd[0],)
                d_rep = dd[1:]
                b_summands = []
                for x in res.differential('*', d_res).source:
                    b_summands += [self.differential(x, d_rep, a=k)]
                return CatMat.block_diagonal(b_summands, ring=self.ring)
            return ud_law_rep

        def ud_f_law(dd, x, f, y):
            d_res = (dd[0],)
            d_rep = dd[1:]
            return identity_matrix(self.ring, self.module_in_degree(d_rep)(res.differential('*', d_res)).nrows())

        return dgModule(TerminalCategory, self.ring, ud_f_law, [ud_law_res] +
                                  [ud_laws_rep(k) for k in range(self.n_diff)])

    def show(self, x, (a, b), title='DG-module'):
        s = '\\bullet_{' + str(a) + '}'
        if self.n_diff != 1:
            raise NotImplementedError('Can only display a dgModule with a single differential.')
        for d in range(a, b + 1):
            s += ' \\xrightarrow{' + self.differential(x, (d,)).to_latex() + '} \\bullet_{' + str(d + 1) + '} '
        view([LatexExpr(title), LatexExpr(s)], title=title, tightpage=True)


    def apply_matrix_rep(self, matrix_rep):
        def f_law(dd, x, f, y):
            return matrix_rep(self.module_in_degree(dd)(x, f, y))

        def kth_d_law(k):
            def d_law(x, dd):
                return matrix_rep(self.differential(x, dd, a=k))
            return d_law

        return dgModule(self.cat, self.ring, f_law, [kth_d_law(k) for k in range(self.n_diff)],
                        target_cat=matrix_rep.target_cat)

    # TODO: implement every entry on every page of all the spectral sequences
    # Note that homology means we will transpose everything
    def homology(self, x, k):
        assert self.n_diff == 1
        assert self.target_cat is None
        ch = ChainComplex({-1: self.differential(x, (k,)), 0: self.differential(x, (k - 1,))})
        return ch.homology(0)

    def cohomology(self, x, k):
        assert self.n_diff == 1
        assert self.target_cat is None
        ch = ChainComplex({-1: self.differential(x, (k - 1,)).transpose(), 0: self.differential(x, (k,)).transpose()})
        return ch.homology(0)

    def cohomology_generators(self, x, k):
        assert self.n_diff == 1
        assert self.target_cat is None
        ch = ChainComplex({-1: self.differential(x, (k - 1,)).transpose(), 0: self.differential(x, (k,)).transpose()})
        return ch.homology(0, generators=True)

    # To build a resolution, you can imagine a resolution for each module in each multidegree.
    # Since we already know how to compute these resolutions, the task
    # is to stitch these resolutions together.
    # The original modules are city blocks, and the resolutions build a skyscraper on each block
    # Our job is to build bridges connecting every level of the city so that you never need
    # to go back down to street level.
    #
    # Once the "first floor" tubes are built, the rest can be filled in by solving matrix equations
    # that rely on already having the tubes built on lower floors and in lower multidegrees.
    # The matrix equations serve to make every square commute and every direction a cochain complex.
    #
    # For this reason, it is important that self is concentrated in nonnegative degrees.
    #
    # The dictionary res contains dgModules with source * so that res[k] = k-th layer of the city
    # considering the "first floor" as k=0.
    # The layers are built to be compatible with the resolutions from each module, so these are enough
    # to find the final answer.

    # TODO: This code is stolen from above and put here for reference
    def presentation(self):
        if 0 in self.res:
            return self.res[0]
        # First get spanners
        all_gens = dict()
        for x in self.cat.objects:
            if self.cat_mat:
                all_gens[x] = CatMat.identity_matrix(self.ring, self.target_cat, self.rank(x))
            else:
                all_gens[x] = identity_matrix(self.rank(x))
        gen_points, gens, surj = self.prune_subspanners(all_gens)

        # then take kernels of components
        ker_gens = dict()
        for x in self.cat.objects:
            if self.cat_mat:
                ker_gens[x] = surj[x].step_left()
            else:
                ker_gens[x] = CatMat.matrix_step_left(surj[x])

        # then get spanners for those kernels

        # first build the free representation Left-Kan-Extended from the generators
        if self.cat_mat:
            new_cat = ProductCategory(self.cat, self.target_cat.op())

            def lan_law(x, f, y):
                diag = []
                for s, t in gen_points:
                    sm = self.cat.right_action_matrix(s, x, f, y)
                    tm = CatMat.identity_matrix(self.ring, self.target_cat, [t])
                    diag += [CatMat.kronecker_product(sm, tm)]
                return CatMat.block_diagonal(diag, self.ring, self.target_cat)
        else:
            new_cat = self.cat

            def lan_law(x, f, y):
                diag = []
                for s in gen_points:
                    sm = self.cat.right_action_matrix(s, x, f, y)
                    diag += [sm]
                return block_diagonal_matrix(diag)
        free_on_gens = MatrixRepresentation(self.cat, self.ring, lan_law, target_cat=self.target_cat)



        rel_points, rels, _ = free_on_gens.prune_subspanners(ker_gens)

        # then build output matrix
        if self.cat_mat:
            columns = []
            for p, r in zip(rel_points, rels):
                column = []
                k = 0
                for g in gen_points:
                    dvl = []
                    ey = CatMat.zero_matrix(self.ring, new_cat, [g], [p])
                    for f in self.cat.hom(g[0], p[0]):
                        dvl += list(r.entry_vector(0, k))
                        # Build the 1x1 CatMat with entry f
                        fm = CatMat.from_string(self.ring, self.cat, [g[0]], '[[' + f + ']]', [p[0]])
                        em = CatMat(self.ring, self.target_cat.op(), [g[1]], r.entry_vector(0, k), [p[1]])
                        ey += CatMat.kronecker_product(fm, em)
                        k += 1
                    # Another risky attempt:
                    # column += [[CatMat(self.ring, new_cat, [g], vector(self.ring, dvl), [p])]]
                    column += [[ey]]
                # This was the risky way I did it before:
                # cm = CatMat(self.ring, new_cat, gen_points, r.data_vector, [p])
                # It might be faster, but is it correct?
                cm = CatMat.block_matrix(column, self.ring, new_cat, [[g] for g in gen_points], [[p]])
                columns += [cm]
            self.res[0] = CatMat.block_matrix([columns], self.ring, new_cat, [gen_points], [[p] for p in rel_points])
            return self.res[0]
        else:
            cols = [CatMat(self.ring, self.cat, gen_points, rl, [rp]) for rp, rl in zip(rel_points, rels)]
            sources = [gen_points]
            targets = [[r] for r in rel_points]
            self.res[0] = CatMat.block_matrix([cols], self.ring, new_cat, sources=sources, targets=targets)
            return self.res[0]



    # TODO: under construction
    # Introduces a new differential
    # changes the source category to *
    # and changes the target category to the old source category (op?)
    #
    # Resolves the module in each multidegree
    # and stitches resolutions together
    #
    # Currently assumes that self is supported in nonnegative multidegree
    # (But of course it may call negative stuff anyhow--make sure to return the appropriate zero matrix!)
    # Would be easy to generalize to bounded-below
    def resolution(self):

        if self.cat_mat:
            new_cat = ProductCategory(self.cat, self.target_cat.op())
        else:
            new_cat = self.cat


        # First build layer_zero, the dgModule that will be placed in res[0]
        def rk_in_degree(d):
            return self.module_in_degree(d).presentation().source

        def layer_zero_f_law(d, x, f, y):
            return CatMat.identity_matrix(self.ring, new_cat, rk_in_degree(d))

        # The matrices for layer_zero_d_law are stored here
        pre = {}
        # Build the correct zero matrices pointing up into the nonnegative orthant
        # These serve as base-case matrices in the iteration
        def seed_pre(d):
            for a in range(self.n_diff):
                # Always use -1 in coordinate a
                for dd in itertools.product(*[range(p) if k!= a else [-1] for k, p in enumerate(d)]):
                    dd0 = tuple(max(0, q) for q in dd)
                    pre[dd] = CatMat.zero_matrix(self.ring, new_cat, [], rk_in_degree(dd0))

        # Start loop to define the various d laws.
        def kth_layer_zero_d_law(k):
            def layer_zero_d_law(x, d):

                for a in range(k + 1):
                    for dd in itertools.product(*[range(p + 1) if q <= k else [p] for q, p in enumerate(d)]):

                        # Build system to solve
                        incomers = []
                        composites = []
                        for b in range(a + 1):
                            dc = tuple(dd[p] - 1 if p == b else dd[p] for p in range(self.n_diff))
                            de = tuple(dc[p] + 1 if p == a else dc[p] for p in range(self.n_diff))
                            # TODO: these two lines are wrong; they need to use surj to see where images go
                            # You can tell it's wrong because x should be * and never matter.
                            incomers += [self.differential(x, dc, a=b)]
                            composites += [self.differential(x, dc, a=a) * self.differential(x, de, a=b)]

                            incomer_cols = []
                            for r, o in enumerate(self.module_in_degree(dc)):
                                incomer_cols += CatMat(self.ring, new_cat, [o], )
                                # TODO: I think I've been thinking about subsequent layers and not the zeroth.
                                # The original columns are the pilots you sink first.
                                # Add in all the wires in direction 0 now
                                # and you will have compat with these columns + self-compat
                                # The compat with these columns is a bit tricky because they are pointwise at first.
                                # TODO: Can you solve pointwise for each object to get a pointwise description of layer_zero, and THEN convert to matrices?
                                # TODO: I don't know.  How will you make sure that the maps you different pointwise solutions are compatible?
                                # TODO: that seems to require compatibility with generating morphisms for the category.
                                # TODO: admittedly, I could compute those using Hochschild trick

                        # solve it to get our new arrow
                        # save and return the arrow.










        pass



    # Given a dgModule dgm with source *
    # builds a smaller representative for dgm in the derived category
    @classmethod
    def prune(cls, dgm):
        pass











































