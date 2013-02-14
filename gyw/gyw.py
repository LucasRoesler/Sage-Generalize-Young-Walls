#******************************************************************************
#  Copyright (C) 2013
#
#  Lucas David-Roesler (roesler at lvc dot edu)
#  Ben Salisbury (bsalisbury at ccny dot cuny dot edu)
#  Travis Scrimshaw (tscrim at ucdavis dot edu)
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************


#########
## e operators are wrong!!!!!!
## Fix documentation
## is it possible to create an error if tiles are not placed correctly?
#########
import re
from copy import deepcopy
from sage.combinat import ranker
from sage.combinat.root_system.cartan_type import CartanType
from sage.structure.element import Element, parent
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.combinat.combinat import CombinatorialObject
from sage.categories.highest_weight_crystals import HighestWeightCrystals

class GeneralizedYoungWall(CombinatorialObject,Element):
    
    def __init__(self,parent,data):
        i = len(data)-1
        while i >= 0 and len(data[i]) == 0:
            data.pop()
            i -= 1
        self.rows = len(data)
        if data == []:
            self.cols = 0
        else:
            self.cols = max([len(r) for r in data])
        self.data = data
        CombinatorialObject.__init__(self, data)
        Element.__init__(self, parent)
                
    def __repr__(self):
        return self.data.__repr__()

    def raw_signature(self,i):
        '''
        Returns the sequence from {+,-} obtained from all i-admissible slots and removable i-boxes 
        without canceling any (+,-)-pairs.
        '''
        sig = []
        rank = self.parent().cartan_type().rank() # n+1
        for row in range(self.rows):
            if self.data[row] == [] and i == ( row % rank ):
                sig.append(['+',row,0])
            elif self.data[row] == []:
                continue
            elif self.data[row][-1] == ( (i+1) % rank ):
                sig.append(['+',row,len(self.data[row])+1])
            elif self.data[row][-1] == i:
                sig.append(['-',row,len(self.data[row])])
        return sorted(sig,key=self.sig_sort)
        
    def sig_sort(self,a):
        '''
        Internal command used to appropriately sort the output from raw_signature.
        '''
        return (-a[2],a[1])
        
    def generate_signature(self, i):
        '''
        The i-signature of self (with whitespace where cancellation occurs) together 
        with the unreduced sequence from {+,-}.
        '''
        sig = []
        rank = self.parent().cartan_type().classical().rank()
        for row in range(self.rows):
            if self.data[row] == [] and i == ( row % (rank+1) ):
                sig.append(['+',row,0])
            elif self.data[row] == []:
                continue
            elif self.data[row][-1] == ( (i+1) % (rank+1) ):
                sig.append(['+',row,len(self.data[row])+1])
            elif self.data[row][-1] == i:
                sig.append(['-',row,len(self.data[row])])
        sig = sorted(sig,key=self.sig_sort)

        # sig is a multilist containing the +/- string and the location for each +/-
        # strsig is simply the string of the +/- in sig
        strsig = ''.join( x[0] for x in sig)
        
        # Below we replace each +- pair, replacing it with an equivalent
        # length of whitespace. Then sub() accepts a function to define the replacement
        # string. We use a lambda function to get the whitespace length correct.
        reducedsig = strsig
        while re.search(r"\+\s*-",reducedsig):
            reducedsig = re.sub(r"\+\s*-", lambda match : str().ljust(len(match.group(int(0)))) , reducedsig)
        return (sig,reducedsig)

    def signature(self, i):
        '''
        Returns the i-signature of self.
        '''
        return self.generate_signature(i)[1].strip()
        
    def pp(self):
        '''
        Returns an ASCII drawing of self.
        '''
        for row in reversed(self.data):
            wall = ''
            for elem in reversed(row):
                wall += str(elem)
                wall += '|'
            if row == []:
                wall += '|'
            print(wall.rjust(2*self.cols+1))
        if self.data==[]:
            print '0'
            
    def content(self):
        '''
        Returns total number of blocks in self.
        '''
        return sum(len(r) for r in self.data)
            
    def e(self,i):
        '''
        Returns the application of the Kashiwara raising operator in the direction i on self.
        '''
        signature = self.generate_signature(i)
        raw_signature = signature[0]
        lastminus  = signature[1].rfind('-')
        newdata = []
        if lastminus > -1:
            deletionrow = raw_signature[lastminus][1]
            for r in reversed(range(self.rows)):
                if r == deletionrow:
                    newdata.append(list(self.data[r][:-1]))
                else:
                    newdata.append(list(self.data[r]))
            return self.__class__(self.parent(),newdata)
        else:
            return None

    def f(self,i):
        '''
        Returns the application of the Kashiwara lowering operator in the direction i on self.
        '''
        signature = self.generate_signature(i)
        raw_signature = signature[0]
        firstplus = signature[1].find('+')     
        newdata = deepcopy(self.data)
        if firstplus > -1:
            additionrow = raw_signature[firstplus][1]
            newdata[additionrow].append(i)
        else:
            while len(newdata) % (self.cartan_type().n+1)  != i:
                newdata.append([])
            newdata.append([i])
        return self.__class__(self.parent(),newdata)

    def latex(self):
        '''
        Generates LaTeX code for self.  Requires TikZ.
        '''
        s = ""
        if self.data == []:
            s += "\\emptyset"
        else:
            s += "\\begin{tikzpicture}[baseline=5,scale=.45] \n \\foreach \\x [count=\\s from 0] in \n"
            s += "{" + ','.join("{" + ','.join( str(i) for i in r ) + "}" for r in self.data ) + "} \n"
            s += "{\\foreach \\y [count=\\t from 0] in \\x {  \\node[font=\\scriptsize] at (-\\t,\\s) {$\\y$}; \n \draw (-\\t+.5,\\s+.5) to (-\\t-.5,\\s+.5); \n \draw (-\\t+.5,\\s-.5) to (-\\t-.5,\\s-.5); \n \draw (-\\t-.5,\\s-.5) to (-\\t-.5,\\s+.5);  } \n \draw[-,thick] (.5,\\s+1) to (.5,-.5) to (-\\t-1,-.5); } \n \\end{tikzpicture} \n"
        return s

    def latex_small(self):
        '''
        This also generates LaTeX code for self, but makes the output much smaller.  Requires TikZ.
        '''
        s = ""
        if self.data == []:
                s += "\\emptyset"
        else:
            s += "\\begin{tikzpicture}[baseline=5,scale=.25] \\foreach \\x [count=\\s from 0] in \n"
            s += "{" + ','.join("{" + ','.join( str(i) for i in r ) + "}" for r in self.data ) + "} \n"
            s += "{\\foreach \\y [count=\\t from 0] in \\x {  \\node[font=\\tiny] at (-\\t,\\s) {$\\y$}; \n \draw (-\\t+.5,\\s+.5) to (-\\t-.5,\\s+.5); \n \draw (-\\t+.5,\\s-.5) to (-\\t-.5,\\s-.5); \n \draw (-\\t-.5,\\s-.5) to (-\\t-.5,\\s+.5);  } \n \draw[-] (.5,\\s+1) to (.5,-.5) to (-\\t-1,-.5); } \n \\end{tikzpicture} \n"
        return s
        
    _latex_ = latex_small
    
    def weight(self):
        '''
        Returns the weight of self as an element of the root lattice.
        '''
        W = []
        L = self.cartan_type().root_system().root_lattice()
        alpha = L.simple_roots()
        for r in self.data:
            for i in r:
                W.append(-1*alpha[i])
        return L(sum(w for w in W))

    def epsilon(self, i):
        """
        Returns the number of i-colored arrows in the i-string above self in the crystal graph.
        """
        assert i in self.index_set()
        eps = 0
        while True:
            self = self.e(i)
            if self is None:
                break
            eps = eps+1
        return eps
    
    def Epsilon(self):
        La = self.cartan_type().root_system().weight_lattice().fundamental_weights()
        return sum(self.epsilon(i)*La[i] for i in self.index_set())

    def phi(self,i):
        h = self.parent().weight_lattice_realization().simple_coroots()
        return self.epsilon(i) + self.weight().scalar(h[i])
    
    def Phi(self):
        La = self.cartan_type().root_system().weight_lattice().fundamental_weights()
        return sum(self.phi(i)*La[i] for i in self.index_set())

    def column(self, k):
        """
        Returns the list of boxes from the kth column of self.
        """
        C = []
        for row in self.data:
            if k-1 < len(row):
                C.append(row[k-1])
            else:
                C.append(None)
        return C

    def a(self,i,k):
        """
        Returns the number a_i(k) of i-colored boxes in the kth column of self.
        """
        A = []
        for c in range(len(self.column(k))):
            if self.column(k)[c] == i:
                A.append(self.column(k)[c])
        return len(A)

    def in_highest_weight_crystal(self,La):
        """
        Returns a boolean indicating if the generalized Young wall element
        is in the highest weight crystal cut out by the given highest weight La.
        """        
        if not La in self.parent().weight_lattice_realization():
            raise TypeError("Must be an element in the weight lattice realization")
        ac = self.parent().weight_lattice_realization().simple_coroots()
        n = self.cartan_type().classical().rank()
        for k in range(1,self.cols+1):
            for j in self.index_set():
                if self.a(j,k) - self.a( (j-1) % (n+1) ,k) <= 0:
                    continue
                else:
                    p_not_found = True
                    for p in self.index_set():
                        if (j+k) % (n+1)  == (p+1) % (n+1) and self.a(j,k) - self.a( (j-1) % (n+1) ,k) <= La.scalar(ac[p]):
                            p_not_found = False
                            continue
                        else:
                            continue
                    if p_not_found:
                        return False
        return True


class CrystalOfGeneralizedYoungWalls(Parent,UniqueRepresentation):
    r"""
    Returns the crystal `Y(\infty)` of generalized Young walls of the given type.  Note that the only valid 
    types for input have the form ['A',`n`,1] for some `n`.  These were defined in the J.-A. Kim and 
    D.-U. Shin's paper *Generalized Young Walls and Crystal Bases for Quantum Affine Algebra of Type `A`*, 
    Proc. Amer. Math. Soc. 138(11), pp. 3877--3889, 2010.
        
    INPUT:
    
    - ``cartan type`` -- Affine type and rank
    
    EXAMPLES::
    
        Yinf = CrystalOfGeneralizedYoungWalls(['A',3,1])
        sage: y = Yinf([[0],[1,0,3,2],[],[3,2,1],[0],[1,0]])
        sage: y.pp()
            0|1|
              0|
          1|2|3|
               |
        2|3|0|1|
              0|
        sage: y.weight()
        -4*alpha[0] - 3*alpha[1] - 2*alpha[2] - 2*alpha[3]
        sage: y.f(0)
        [[0], [1, 0, 3, 2], [], [3, 2, 1], [0], [1, 0], [], [], [0]]
        sage: y.e(0).pp()
              0|
        2|3|0|1|
               |
          1|2|3|
               |
            0|1|
        sage: S = GYW.subcrystal(max_depth=3)
        sage: G = GYW.digraph(subset=G)
        sage: view(G, tightpage=True)
    """

    @staticmethod
    def __classcall_private__(cls, cartan_type):
        ct = CartanType(cartan_type)
        return super(CrystalOfGeneralizedYoungWalls,cls).__classcall__(cls,ct)
    
    def __init__(self, cartan_type):
        self._cartan_type = cartan_type
        Parent.__init__(self, category=HighestWeightCrystals())
        self.module_generators = [self.element_class(self,[])]

    Element = GeneralizedYoungWall

    def _element_constructor_(self,data):
        return self.element_class(self,data)

    def __repr__(self):
        return "Crystal of generalized Young walls of type %s" % self._cartan_type

    def subset(self, max_depth=4):
        return [c for c in self.subcrystal(max_depth=max_depth, direction='lower')]


class HighestWeightCrystalofGYWElement(GeneralizedYoungWall):

    def e(self,i):
        ret = GeneralizedYoungWall.e(self, i)
        if ret.in_highest_weight_crystal(self.parent().hw):
            return ret
        return None

    def f(self,i):
        ret = GeneralizedYoungWall.f(self, i)
        if ret.in_highest_weight_crystal(self.parent().hw):
            return ret
        return None

    def weight(self):
        return self.parent().weight_lattice_realization()(self.parent().hw + GeneralizedYoungWall.weight(self))


class HighestWeightCrystalOfGYW(CrystalOfGeneralizedYoungWalls):
    
    r"""
    Returns the highest weight crystal `Y(\lambda)` of generalized Young walls.  This crystal was 
    described in Theorem 4.1 of Kim and Shin, *Generalized Young Walls and Crystal Bases of Quantum
    Affine Algebra of Type `A`,* Proc. Amer. Math. Soc. 138(11), pp. 3877--3889, 2010.
        
    INPUT:
        
    - ``cartan type`` -- Affine type and rank
        
    - ``weight`` -- Highest weight for the above type and rank
        
    EXAMPLES::
        
        sage: La = RootSystem(['A',3,1]).weight_lattice().fundamental_weights()[1]
        sage: YLa = HighestWeightCrystalOfGYW(['A',3,1],La)
        sage: y = YLa([[0],[1,0,3,2,1],[2,1,0],[3]])
        sage: y.pp()
                3|
            0|1|2|
        1|2|3|0|1|
                0|
        sage: y.weight()
        -Lambda[0] + Lambda[2] + Lambda[3]
        sage: y.in_highest_weight_crystal(La)
        True
        sage: y.f(1)
        [[0], [1, 0, 3, 2, 1], [2, 1, 0], [3], [], [1]]
        sage: y.f(1).f(1)
        sage: yy = CrystalOfGeneralizedYoungWalls(['A',3,1])([[0], [1, 0, 3, 2, 1], [2, 1, 0], [3], [], [1]])
        sage: yy.f(1)
        [[0], [1, 0, 3, 2, 1], [2, 1, 0], [3], [], [1], [], [], [], [1]]
        sage: yyy = yy.f(1)
        sage: yyy.in_highest_weight_crystal(La)
        False
        sage: S = YLa.subset(max_depth=4)
        sage: G = YLa.digraph(subset=S)
        sage: view(G, tightpage=True)
    """
    
    @staticmethod
    def __classcall_private__(cls, cartan_type, La):
        ct = CartanType(cartan_type)
        La = ct.root_system().weight_lattice()(La)
        return super(HighestWeightCrystalOfGYW, cls).__classcall__(cls, ct, La)
    
    def __init__(self, cartan_type, La):
        CrystalOfGeneralizedYoungWalls.__init__(self, cartan_type)
        self.hw = La
    
    Element = HighestWeightCrystalofGYWElement

    def __repr__(self):
        return "Highest weight crystal of generalized Young walls of Cartan type {1!s} and highest weight {0!s}.".format(self.hw, self._cartan_type)
    
    def __iter__(self):
        for c in self.subcrystal(direction='lower'):
            if c.in_highest_weight_crystal(self.hw) :
                yield c

    def subset(self, max_depth=4):
        return [c for c in self.subcrystal(max_depth=max_depth, direction='lower')
                if c.in_highest_weight_crystal(self.hw)]
