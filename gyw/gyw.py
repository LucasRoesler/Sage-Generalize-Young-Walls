#******************************************************************************
#  Copyright (C) 2013
#
#  Lucas David-Roesler (roesler at lvc dot edu)
#  Ben Salisbury (bsalisbury at ccny dot cuny dot edu)
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

# The following is an implementation of the generalized Young wall realization
# of the crystal B(infinity) developed by Kim and Shin (Proc. AMS, 2010).
# Portions of this code were inspired by code sent from Daniel Bump and the
# already implemented code for crystals in Sage.


########## TO DO ################
#
# - input rep. theoretic data
# - weight of a wall
# - highest weight crystals
# - redo latex output so that we start with digraph --> dot_tex, plot and plot3d --> latex, latex_file, view
#
#


import re
from copy import deepcopy
from sage.misc.latex import latex
from sage.graphs.graph import DiGraph
from sage.combinat import ranker
from sage.combinat.root_system.cartan_type import CartanType

class GeneralizedYoungWall:
    '''
        Constructs a generalized Young wall from list input.
        
        INPUT:
        
        - ``data`` -- Multilist containing the boxes of the generalized Young wall read right to left and bottom to top.  An empty list is required for each empty row.
        - ``n`` -- Positive integer value denoting the rank of the generalized Young wall.
        
        EXAMPLES::
        
        sage: y = GeneralizeYoungWall([[0,2,1,0,2],[1,0,2],[],[],[1],[],[],[1]],2)
        sage: y.pp()
        1|
        |
        |
        1|
        |
        |
        2|0|1|
        2|0|1|2|0|
        
        sage: y = GeneralizeYoungWall([[0,5,4,3,2],[],[2,1,0,5,4,3],[3,2],[],[5,4,3,2]],5)
        sage| y.pp()
        2|3|4|5|
        |
        2|3|
        3|4|5|0|1|2|
        |
        2|3|4|5|0|
        
        sage: y = GeneralizeYoungWall([[0,2,1],[1,0,2],[2],[],[],[2]],2)
        sage: y.pp()
        2|
        |
        |
        2|
        2|0|1|
        1|2|0|
        1|2|0|
    '''

    def __init__(self,data,n):
        self.rows = len(data)
        self.cols = 0
        self.rank = n
        self.data = data
        for r in self.data:
            if len(r) > self.cols:
                self.cols = len(r)
        self._cartan_type = CartanType(['A',self.rank,1])
                
    def __repr__(self):
        return self.data.__repr__()
        
    def __eq__(self,other):
        if type(other) is type(self):
            return self.data == other.data
        else:
            return False
            
    def __neq__(self,other):
        if type(other) is type(self):
            return self.data != other.data
        else:
            return True

    def __cmp__(self,other):
        return cmp(self.data,other.data)
     
    def __hash__(self):
        return id(self)

    def raw_signature(self,i):
        '''
        Returns the sequence from {+,-} obtained from all i-admissible slots and removable i-boxes without canceling any (+,-)-pairs.
        '''
        sig = []
        for row in range(self.rows):
            #print row % (self.rank+1)
            if self.data[row] == [] and i == ( row % (self.rank+1) ):
                sig.append(['+',row,0])
            elif self.data[row] == []:
                continue
            elif self.data[row][-1] == ( (i+1) % (self.rank+1) ):
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
        The i-signature of self (with whitespace where cancellation occurs) together with the unreduced sequence from {+,-}.
        '''
        sig = []
        for row in range(self.rows):
            if self.data[row] == [] and i == ( row % (self.rank+1) ):
                sig.append(['+',row,0])
            elif self.data[row] == []:
                continue
            elif self.data[row][-1] == ( (i+1) % (self.rank+1) ):
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
        #print raw_signature
        #print "grabbing from the " + str(lastminus) +'th spot in the raw ' +  str(i) +'-sig'
        deletionrow = raw_signature[lastminus][1]
        newdata = []
        if lastminus > -1:
            #newdata = self.data
            #newdata[deletionrow] = newdata[deletionrow][:-1]
            for r in range(self.rows):
                if r == deletionrow:
                    newdata.append(list(self.data[r][:-1]))
                else:
                    newdata.append(list(self.data[r]))
        return GeneralizedYoungWall(newdata,self.rank)

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
            while len(newdata) % (self.rank+1)  != i:
                newdata.append([])
            newdata.append([i])
            
        #print newdata
        return GeneralizedYoungWall(newdata,self.rank)

    def latex(self):
        '''
        Generates LaTeX code for self.  Requires TikZ.
        '''
        s = ""
        if self.data == []:
            s += "\\varnothing"
        else:
            s += "\\begin{tikzpicture}[baseline=20,scale=.45] \n \\foreach \\x [count=\\s from 0] in \n"
            s += "{" + ','.join("{" + ','.join( str(i) for i in r ) + "}" for r in self.data ) + "} \n"
            s += "{\\foreach \\y [count=\\t from 0] in \\x {  \\node[font=\\scriptsize] at (-\\t,\\s) {$\\y$}; \n \draw (-\\t+.5,\\s+.5) to (-\\t-.5,\\s+.5); \n \draw (-\\t+.5,\\s-.5) to (-\\t-.5,\\s-.5); \n \draw (-\\t-.5,\\s-.5) to (-\\t-.5,\\s+.5);  } \n \draw[-,thick] (.5,\\s+1) to (.5,-.5) to (-\\t-1,-.5); } \n \\end{tikzpicture} \n"
        return s

    def latex_small(self):
        '''
        This also generates LaTeX code for self, but makes the output much smaller.  Still requires TikZ.  This is used by the latex() and latex_file() commands for the crystal.
        '''
        s = ""
        if self.data == []:
                s += "\\varnothing"
        else:
            s += "\\begin{tikzpicture}[baseline=20,scale=.25] \\foreach \\x [count=\\s from 0] in \n"
            s += "{" + ','.join("{" + ','.join( str(i) for i in r ) + "}" for r in self.data ) + "} \n"
            s += "{\\foreach \\y [count=\\t from 0] in \\x {  \\node[font=\\tiny] at (-\\t,\\s) {$\\y$}; \n \draw (-\\t+.5,\\s+.5) to (-\\t-.5,\\s+.5); \n \draw (-\\t+.5,\\s-.5) to (-\\t-.5,\\s-.5); \n \draw (-\\t-.5,\\s-.5) to (-\\t-.5,\\s+.5);  } \n \draw[-] (.5,\\s+1) to (.5,-.5) to (-\\t-1,-.5); } \n \\end{tikzpicture} \n"
        return s
    
    def index_set(self):
        return self.cartan_type().index_set()

    def cartan_type(self):
        return self._cartan_type
            
    def root_system(self):
        return RootSystem(['A',self.rank,1])

    def weight_lattice_realization(self):
        return RootSystem(['A',self.rank,1]).weight_lattice()

    def Lambda(self):
        return self.weight_lattice_realization().fundamental_weights()

    def simple_roots(self):
        return self.weight_lattice_realization().simple_roots()

    def root_lattice_realization(self):
        return RootSystem(['A',self.rank,1]).root_lattice()

    def alpha(self):
        return self.root_lattice_realization().simple_roots()

    def weight(self):
        return sum(self.iweight(i) for i in self.index_set())

    def iweight(self,i):
        W = []
        for r in self.data:
            if i in r:
                W.append(-1*self.alpha()[i])
        return sum(w for w in W)

    def weight_on_hi(self,i):
        W = []
        for r in self.data:
            if i in r:
                W.append(-1*self.alpha()[i])
        return sum(1 for w in W)

    def epsilon(self, i):
        '''
        Returns the number of i-colored arrows in the i-string above self in the crystal graph.
        '''
        #Copied from existing Sage code.  Not functioning properly here.
        assert i in self.index_set()
        eps = 0
        while True:
            self = self.e(i)
            if self == 0:
                break
            eps = eps+1
        return eps

    def phi(self,i):
        return self.epsilon(i) + self.weight_on_hi(self,i)

    def column(self, k):
        L = [len(r) for r in self.data]
        C = []
        for r in range(len(self.data)):
            if k-1 > len(self.data[r]):
                C.append(None)
            else:
                C.append(self.data[r][k-1])
        return C

    def a(self,i,k):
        assert i in self.index_set()
        A = []
        for c in range(len(self.column(k))):
            if self.column(k)[c] == i:
                A.append(self.column(k)[c])
        return len(A)


class CrystalOfGeneralizedYoungWalls:
    '''
        Constructs the top part of the crystal B(infinity) realized as the set of generalized Young walls in type A_n^{(1)} down to a given depth.
        
        INPUT:
        - ``n`` -- integer. The rank of A_n^{(1)}.
        - ``h`` -- integer. Only the generalized Young walls with at most h boxes are generated.
        
        EXAMPLES::
        
        sage: Y = GeneralizedYoungWallCrystal(2,2)
        sage: Y.cardinality()
        13
    '''
    
    def __init__(self, n, h):
        self.rank = n
        self.depth = h
        self.data = [GeneralizedYoungWall([],n)]
        for level in range(h):
            for Y in [X for X in self.data if X.content()==level]:
                for i in range(n+1):
                    W = Y.f(i)
                    if W in self.data:
                        continue
                    else:
                        self.data.append(W)
        self._cartan_type = CartanType(['A',self.rank,1])
    
    def __repr__(self):
        return "Crystal of generalized Young walls of type %s down to depth %d." % (self.cartan_type(), self.depth)

    def list(self):
        return self.data
     
    def report(self):
        print "\n-----\n"
        print ' There are a total of ' + str(len(self.data)) 
        print ' elements in the crystal, going down to depth ' + str(self.depth) +'.'
    
    def index_set(self):
        print range(self.rank+1)
    
    def cardinality(self):
        return len(self.data)
    
    def dot_tex(self):
        """
        Returns a Dot2TeX version of self.
        """
        #rank = ranker.from_list(self.list())[int(0)]
        #rank = lambda x : self.data.index(x)
        #vertex_key = lambda x: "N_"+str(rank(x))
        vertex_key = lambda x : "N_"+str(self.data.index(x))
        
        # To do: check the regular expression
        # Removing %-style comments, newlines, quotes
        # This should probably be moved to sage.misc.latex
        quoted_latex = lambda x: re.sub("\"|\r|(%[^\n]*)?\n","", x.latex_small())
        
        result = "digraph G { \n  node [ shape=plaintext ];\n"
        
        for x in self.data:
            result += "  " + vertex_key(x) + " [ label = \" \", texlbl = \"$"+quoted_latex(x)+"$\" ];\n"
        for x in self.data:
            for i in range(self.rank+1):
                child = x.f(i)
                if child in self.data:
                    try:
                        result += "  " + vertex_key(x) + " -> "
                    except KeyError:
                        print x.pp()
                        print "x caused an error with the ranker function, stopping exectution"
                        return False
                    try:
                        result += vertex_key(child)
                    except KeyError as error:
                        print child.pp()
                        print "child caused an error with the ranker function, stopping exectution"
                        print error
                        return False
                
                    result += " [ label = \" \", texlbl = \"%d\" ];\n"%i
        result+="}"
        return result
    
    def latex(self):
        '''
        Returns a string of LaTeX code of self.  To export directly to a LaTeX file, use self.latex_file('<directory>').
        '''
        try:
            from dot2tex.dot2tex import Dot2TikZConv
        except ImportError:
            print "dot2tex not available.  Install after running \'sage -sh\'"
            return
        
        options = {'format':'tikz', 'crop':True, 'usepdflatex':True, 'figonly':True}
        
        content = (Dot2TikZConv(options)).convert(self.dot_tex())
        
        return content

    def latex_file(self, filename):
        '''
        Outputs a LaTeX file of self to destination filename.
        '''
        header = r"""\documentclass{article}
            \usepackage[x11names, rgb]{xcolor}
            \usepackage[utf8]{inputenc}
            \usepackage{tikz}
            \usetikzlibrary{snakes,arrows,shapes,matrix}
            \usepackage{amsmath,amssymb}
            \usepackage[active,tightpage]{preview}
            \newenvironment{bla}{}{}
            \PreviewEnvironment{bla}
            
            \begin{document}
            \begin{bla}"""
        
        footer = r"""\end{bla}
            \end{document}"""
        f = open(filename, 'w+')
        f.write(header + self.latex() + footer)
        f.close()

    def index_set(self):
        return range(self.rank+1)
    
    def cartan_type(self):
        return self._cartan_type
    
    def root_system(self):
        return RootSystem(['A',self.rank,1])
    
    def weight_lattice_realization(self):
        return RootSystem(['A',self.rank,1]).weight_lattice()
    
    def Lambda(self):
        return self.weight_lattice_realization().fundamental_weights()
    
    def simple_roots(self):
        return self.weight_lattice_realization().simple_roots()
    
    def root_lattice_realization(self):
        return RootSystem(['A',self.rank,1]).root_lattice()
    
    def alpha(self):
        return self.root_lattice_realization().simple_roots()
