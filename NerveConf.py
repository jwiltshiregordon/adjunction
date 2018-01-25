from sage.all import *
from CatMat import *
from sage.all import matrix


def circle_one(x):
    if x == 'v':
        return 'Iv'
    if x == 'e':
        return 'Ie'

def circle_hom(x, y):
    if x == 'v' and y == 'v':
        return ['Iv']
    if x == 'v' and y == 'e':
        return ['f', 'g']
    if x == 'e' and y == 'v':
        return []
    if x == 'e' and y == 'e':
        return ['Ie']

def circle_comp(x, f, y, g, z):
    if x == z:
        if x == 'v':
            return 'Iv'
        if x == 'e':
            return 'Ie'
    if f == 'f' or f == 'g':
        return f
    return g

circle_cat = FiniteCategory(['v', 'e'], circle_one, circle_hom, circle_comp)

torus_cat = ProductCategory(circle_cat, circle_cat)


for x in torus_cat.objects:
    for y in torus_cat.objects:
        print 'Hom(' + str(x) + ', ' + str(y) + ') = ' + str(torus_cat.hom(x, y))



for x in torus_cat.objects:
    for y in torus_cat.objects:
        for z in torus_cat.objects:
            for f in torus_cat.hom(x, y):
                for g in torus_cat.hom(y, z):
                    print 'composition of ' + str(f) + ' and ' + str(g)
                    print torus_cat.compose(x, f, y, g, z)


conf_two_objects = []



def circle_conf_cat_one(x):
    #e_positions = [i for i, c in enumerate(x[0])]
    return torus_cat.identity(x[0])# + ''.join([chr(e_positions.index(i) + 97) if i in e_positions else None
                                   #            for i in range(len(x[0]))])

def same_sorted(list_of_pairs):
    lxy = [(x, y) for x, y in list_of_pairs]
    lyx = [(y, x) for x, y in list_of_pairs]
    lxy.sort()
    lyx.sort()
    return lxy == [(x, y) for y, x in lyx]

print 'SAME SORTED'
print same_sorted([('a', 'b'), ('a', 'c')])
print same_sorted([('a', 'b'), ('c', 'a')])


def circle_conf_cat_hom(x, y):
    e_positions_x = [i for i, c in enumerate(x[0]) if c == 'e']
    e_positions_y = [i for i, c in enumerate(y[0]) if c == 'e']
    if any(ex not in e_positions_y for ex in e_positions_x):
        return []
    position_pairs = [(x[1][ex], y[1][ex]) for ex in e_positions_x]
    if not same_sorted(position_pairs):
        return []

    return torus_cat.hom(x[0], y[0])

def circle_conf_cat_comp(x, f, y, g, z):
    return torus_cat.compose(x[0], f, y[0], g, z[0])

circle_conf_cat_object_list_2 = [(('v', 'e'), (None, 'a')),
                               (('e', 'v'), ('a', None)),
                               (('e', 'e'), ('a', 'b')),
                               (('e', 'e'), ('b', 'a'))
                               ]

circle_conf_cat_object_list_3 = [(('v', 'v', 'e'), (None, None, 'a')),
                                 (('v', 'e', 'v'), (None, 'a', None)),
                                 (('e', 'v', 'v'), ('a', None, None)),
                                 (('v', 'e', 'e'), (None, 'a', 'b')),
                                 (('v', 'e', 'e'), (None, 'b', 'a')),
                                 (('e', 'v', 'e'), ('a', None, 'b')),
                                 (('e', 'v', 'e'), ('b', None, 'a')),
                                 (('e', 'e', 'v'), ('a', 'b', None)),
                                 (('e', 'e', 'v'), ('b', 'a', None)),
                                 (('e', 'e', 'e'), ('a', 'b', 'c')),
                                 (('e', 'e', 'e'), ('a', 'c', 'b')),
                                 (('e', 'e', 'e'), ('b', 'a', 'c')),
                                 (('e', 'e', 'e'), ('b', 'c', 'a')),
                                 (('e', 'e', 'e'), ('c', 'a', 'b')),
                                 (('e', 'e', 'e'), ('c', 'b', 'a'))]



circle_conf_cat = FiniteCategory(circle_conf_cat_object_list_2, circle_conf_cat_one, circle_conf_cat_hom, circle_conf_cat_comp)


for x in circle_conf_cat.objects:
    for y in circle_conf_cat.objects:
        print 'Hom(' + str(x) + ', ' + str(y) + ') = ' + str(circle_conf_cat.hom(x, y))




for x in circle_conf_cat.objects:
    for y in circle_conf_cat.objects:
        for z in circle_conf_cat.objects:
            for f in circle_conf_cat.hom(x, y):
                for g in circle_conf_cat.hom(y, z):
                    print 'composition of ' + str(x) + '  ---' + str(f) + '-->  ' + str(y) + '  ---' + str(g) + '-->  ' + str(z)
                    print circle_conf_cat.compose(x, f, y, g, z)











def circle_conf_triv_law(x, f, y):
    return matrix(ZZ, 1, 1, [1])


circle_conf_triv = MatrixRepresentation(circle_conf_cat, ZZ, circle_conf_triv_law)

dgm = circle_conf_triv.resolution()



Ch = ChainComplex({k:circle_conf_triv(dgm.differential('*', (k,))).transpose() for k in range(9)})
for d in Ch.homology():
    print Ch.homology()[d]



# Here n gives the number of particles
# and graph is a collection of edges given as a list of tuple pairs
def braid_conf_cat(n, graph):
    def one(x):
        pass
    def hom(x, y):
        pass
    def comp(x, f, y, g, z):
        pass
