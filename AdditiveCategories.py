from CatMat import *

# Constructing a PreadditiveCategory using __init__
#
# We assume that all Homs are free modules over the commutative ring of coefficients.
# There are important examples where this is not true, but a better fix would be to
# use dg-categories, and we're not there yet.
#
# object_list
# A list of objects in the category.  These objects must be hashable.
# The list need not be exhaustive--its purpose is to indicate where to check exactness.
# TODO: replace this with a modulus as in arXiv:CODZ.
#
# one_law
# This argument tells the PreadditiveCategory what the identity morphisms are.  It must be a
# function that takes an object and returns a vector that represents the identity at
# that object.
#
# hom_law
# This argument tells the PreadditiveCategory how to compute hom between two objects.  It must be a
# function that takes a pair of objects and returns a list of morphisms from one to the other.
# The morphisms are represented as strings.
#
# composition_law
# This argument tells the PreadditiveCategory how to compose.  It is a function of the following
# form:
#        composition_law(x, f, y, g, z)
# where x, y, and z are objects, and f : x --> y and g : y --> z are morphisms represented
# as strings.  The function should return a vector over the ring giving the coefficients
# of the composite morphism in the same order that they appear in hom_law(x, z)
#
class PreadditiveCategory(object):
    def __init__(self, object_list, one_law, hom_law, composition_law, ring=ZZ,
                 object_latex_law=None, morphism_latex_law=None,
                 cache=True):
        self.objects = object_list
        self.basic_hom = hom_law
        self.basic_one = one_law
        self.basic_composition = composition_law
        self.ring = ring
        self.one_dict = {}
        self.hom_dict = {}
        self.mns = {}
        self.msn = {}

        self.lact = {}
        self.mact = {}
        self.ract = {}
        self.op_cat = OppositeCategory(self)

        self.double_cat = ProductCategory(';', self.op_cat, self)

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

    # Here, f and g are strings, and the result is a vector.
    def basic_compose(self, x, f, y, g, z):
        return self.basic_composition(x, f, y, g, z)

    # Here, f and g are vectors and the result is a vector.
    def compose(self, x, f, y, g, z):
        return vector(self.ring, [f * self.middle_action_matrix(x, fg, z, y) * g for fg in self.hom(x, z)])

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
        #ret = matrix(ZZ, len(rows), len(cols), [1 if self.compose(x, f, y, r, z) == c
        #                                        else 0 for r in rows for c in cols])
        ret = matrix(self.ring, len(rows), len(cols),
                     [e for r in rows for e in self.basic_compose(x, f, y, r, z)])
        self.lact[(x, f, y, z)] = ret
        return ret

    def middle_action_matrix(self, x, f, z, y):
        if self.cache and (x, f, z, y) in self.mact:
            return self.mact[(x, f, z, y)]
        rows = self.hom(x, y)
        cols = self.hom(y, z)
        fn = self.morphism_to_number(x, f, z)
        ret = matrix(self.ring, len(rows), len(cols),
                     [self.basic_compose(x, r, y, c, z)[fn] for r in rows for c in cols])
        self.mact[(x, f, z, y)] = ret
        return ret

    def right_action_matrix(self, x, y, f, z):
        if self.cache and (x, y, f, z) in self.ract:
            return self.ract[(x, y, f, z)]
        rows = self.hom(x, y)
        cols = self.hom(x, z)
        #ret = matrix(ZZ, len(rows), len(cols), [1 if self.compose(x, r, y, f, z) == c
        #                                        else 0 for r in rows for c in cols])
        ret = matrix(ZZ, len(rows), len(cols), [e for r in rows for e in self.basic_compose(x, r, y, f, z)])
        self.ract[(x, y, f, z)] = ret
        return ret

    def free_module(self, degrees):
        try:
            iter(degrees)
        except TypeError:
            print('Warning! You have passed a non-iterable list of degrees to free_module.')
            print('Figure out when it happened, and fix it!')
            return self.free_module(self.ring, (degrees,))

        def law(x, f, y):
            ret = matrix(self.ring, 0, 0, [])
            for d in degrees:
                ret = ret.block_sum(self.right_action_matrix(d, x, f, y))
            return ret

        return MatrixRepresentation(self, self.ring, law, target_cat=None)

    #def free_op_module(self, ring, degrees):
    #    return self.op_cat.free_module(ring, degrees)

    def cofree_module(self, degrees):
        try:
            iter(degrees)
        except TypeError:
            return self.cofree_module(self.ring, (degrees,))

        def law(x, f, y):
            ret = matrix(self.ring, 0, 0, [])
            for d in degrees:
                ret = ret.block_sum(self.left_action_matrix(x, f, y, d).transpose())
            return ret

        return MatrixRepresentation(self, self.ring, law, target_cat=None)


    def op(self):
        return self.op_cat


    def hom_bimodule(self):
        def hom_bimodule_law(bx, fg, ay):
            b, x = bx
            a, y = ay
            f, g = self.double_cat.break_string(fg)
            free = self.free_module([b])
            cofree = self.cofree_module([y])
            return free(x, g, y) * cofree(a, f, b).transpose()
        return MatrixRepresentation(self.double_cat, ZZ, hom_bimodule_law, target_cat=None)


    def show_multiplication_table(self):
        morphisms = [(x, f, y) for x in self.objects for y in self.objects for f in self.hom(x, y)]
        source = [x for x, f, y in morphisms]
        target = [z for y, g, z in morphisms]
        entries = [e for x, f, y in morphisms for yy, g, z in morphisms
                     for e in ([0] * len(self.hom(x, z)) if y != yy else self.basic_compose(x, f, y, g, z))]
        print([f for _, f, _ in morphisms])
        print(CatMat(ZZ, self, source, vector(ZZ, entries), target).to_latex())


    def test(self):
        for x in self.objects:
            if len(self.identity(x)) != len(self.hom(x, x)):
                print('The identity morphism for the object ' + str(x) + \
                      ', which is supposed to have length ' + str(len(self.hom(x, x))) + \
                      ', instead has length ' + str(len(self.identity(x))) + '.')
        for x in self.objects:
            for y in self.objects:
                for f in self.hom(x, y):
                    fv = vector(self.ring, [1 if m == f else 0 for m in self.hom(x, y)])
                    if self.compose(x, self.identity(x), x, fv, y) != fv:
                        print('The identity morphism for the object ' + str(x) + \
                              ' does not fix the morphism ' + str(fv) + \
                              ' to ' + str(y) + '.')
        for x in self.objects:
            for y in self.objects:
                for z in self.objects:
                    for f in self.hom(x, y):
                        for g in self.hom(y, z):
                            if len(self.basic_compose(x, f, y, g, z)) != len(self.hom(x, z)):
                                print('The composition ' + str((x, f, y, g, z)) + ', which is supposed ' + \
                                    'to have length ' + len(self.hom(x, z)) + \
                                    ', instead has length ' + len(self.basic_compose(x, f, y, g, z)) + '. ')
        for w, x, y, z in itertools.product(*([self.objects] * 4)):
            for f in self.hom(w, x):
                for g in self.hom(x, y):
                    for h in self.hom(y, z):
                        fv = vector(self.ring, [1 if m == f else 0 for m in self.hom(w, x)])
                        hv = vector(self.ring, [1 if m == h else 0 for m in self.hom(y, z)])
                        left = self.compose(w, fv, x, self.basic_compose(x, g, y, h, z), z)
                        right = self.compose(w, self.basic_compose(w, f, x, g, y), y, hv, z)
                        if left != right:
                            print('The following triple of morphisms do not associate:')
                            print(w, f, x, g, y, h, z)
















