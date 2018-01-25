from sage.all import *

from CatMat import *
from sage.all import vector, matrix, zero_matrix, identity_matrix, block_diagonal_matrix
from sage.all import Matroid
import sys
sys.path.insert(0, '/Users/jwiltshiregordon/Dropbox/SageUseful')
from ConfigurationSpace import power_complex



# All graphs must be immutable
# and have vertex set {0, ..., n - 1}
#
# A morphism is represented as a set function
#



# The next three functions define the category of finite sets
def GI_one(x):
    return '*' if x == 0 else ''.join([chr(v + 97) for v in range(x)])


def finHom(x, y):
    return ['*'] if x == 0 else [''.join([chr(v + 97) for v in w]) for w in
                                 tuple(itertools.product(*([range(0, y)] * x)))]


def finComp(x, f, y, g, z):
    return '*' if x == 0 else ''.join([tuple(g)[ord(c) - 97] for c in tuple(f)])


def GI_one(x):
    return '*'

def GI_hom(x, y):
    return ['*'] if x.issubset(y) else []

def GI_comp(x, f, y, g, z):
    return '*'

# This poset is called \mathcal{G}(n) in the paper
def G(n):
    return FiniteCategory(Graphs(n), G_one, G_hom, G_comp)




