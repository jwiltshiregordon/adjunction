from RepresentationStabilityCategories import *
D = FI()


# As practice, we implement the right adjunction
# FI(x + 1,y) = FI(x, y * (y-1)).
# The left adjoint is easy
def plus_one_law(x, f, y):
    sf = ''.join(chr(ord(c) + 1) for c in f)
    return x + 1, 'a' + sf, y + 1


# We only specify the right adjoint on objects
def minus_one_on_objects(y):
    return [y - 1] * y


# The counit is given by drawing a card and placing it on top
def plus_one_counit(x):
    id_string = D.identity(x)
    m_string = '['
    for i in range(x):
        m_string += '[' + id_string[i] + id_string[:i] + id_string[i + 1:] + '],'
    m_string = m_string[:-1] + ']'
    return CatMat.from_string(ZZ, D, [x - 1 + 1] * x, m_string, [x])


# Now we use the Adjunction class to solve for the right adjoint
plus_one = Functor(D, plus_one_law, D)
adj = Adjunction(plus_one, minus_one_on_objects, plus_one_counit)
minus_one = adj.right_adjoint()

print
minus_one(2, 'ac', 3).pp()
print
minus_one(3, 'dcb', 4).pp()
print
minus_one(2, 'db', 4).pp()

