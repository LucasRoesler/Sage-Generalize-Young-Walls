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
# - highest weight crystals
# - redo latex output so that we start with digraph --> dot_tex, plot and plot3d --> latex, latex_file, view


r'''
    WARNING: At the moment, there is no check that an implemented array satisfies the board placement rules for tiles as in Kim-Shin.  For example, our code does not check that the southestern-most tile is colored 0.
'''


import re
from copy import deepcopy
from sage.misc.latex import latex
from sage.graphs.graph import DiGraph
from sage.combinat import ranker
from sage.combinat.root_system.cartan_type import CartanType
from sage.structure.element import Element, parent
from sage.misc.latex import latex
from sage.graphs.dot2tex_utils import have_dot2tex
from sage.combinat.combinat import CombinatorialObject

class GeneralizedYoungWall(CombinatorialObject):
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
        if data ==[]:
            self.cols = 0
        else:
            self.cols = max([len(r) for r in data])
        self.rank = n
        self.data = data
        self._cartan_type = CartanType(['A',self.rank,1])
        CombinatorialObject.__init__(self, data)
                
    def __repr__(self):
        return self.data.__repr__()
        


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
       
        newdata = []
        if lastminus > -1:
            deletionrow = raw_signature[lastminus][1]
            #newdata = self.data
            #newdata[deletionrow] = newdata[deletionrow][:-1]
            for r in range(self.rows):
                if r == deletionrow:
                    newdata.append(list(self.data[r][:-1]))
                else:
                    newdata.append(list(self.data[r]))
            return GeneralizedYoungWall(newdata,self.rank)
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
        
    _latex_ = latex_small
    
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
        '''
        Returns the simple roots in the basis of fundamental weights.
        '''
        return self.weight_lattice_realization().simple_roots()

    def root_lattice_realization(self):
        return RootSystem(['A',self.rank,1]).root_lattice()

    def alpha(self):
        return self.root_lattice_realization().simple_roots()

    def weight(self):
        '''
        Returns the weight of self.  Here, it is an element of the root lattice.
        '''
        W = []
        for r in self.data:
            for i in r:
                W.append(-1*self.alpha()[i])
        return sum(w for w in W)

    def epsilon(self, i):
        '''
        Returns the number of i-colored arrows in the i-string above self in the crystal graph.
        '''
        assert i in self.index_set()
        eps = 0
        while True:
            self = self.e(i)
            if self is None:
                break
            eps = eps+1
        return eps
    
    def Epsilon(self):
        return sum(self.epsilon(i)*self.Lambda()[i] for i in self.index_set())

    def phi(self,i):
        h = self.weight_lattice_realization().simple_coroots()
        return self.epsilon(i) + y.weight().scalar(h[i])
    
    def Phi(self):
        return sum(self.phi(i)*self.Lambda()[i] for i in self.index_set())

    def column(self, k):
        '''
        Returns the list of boxes from the kth column of self.
        '''
        C = []
        for row in self.data:
            if k-1 < len(row):
                C.append(row[k-1])
            else:
                C.append(None)
        return C

    def a(self,i,k):
        '''
        Returns the number a_i(k) of i-colored boxes in the kth column of self.
        '''
        A = []
        for c in range(len(self.column(k))):
            if self.column(k)[c] == i:
                A.append(self.column(k)[c])
        return len(A)

    def in_highest_weight_crystal(self,La):
        '''
        Returns a boolean indicating if the generalized young wall element
        is in the highest weight crystal cut out by the given highest weight La.
        '''
        # We impliment Theorem 4.1 in Kim and Shin (Proc. AMS, 2010)
        
        # check that La is in the weight lattice or throw an exception
        assert La in self.weight_lattice_realization()
        
        # grab the coroots and the rank
        ac = self.weight_lattice_realization().simple_coroots()
        n = self.rank
        
        # for each column in the GYW
        for k in range(1,self.cols+1):
            # and each color j
            for j in self.index_set():
                # we check if the number of j boxes is less than or equal
                # to the number of j-1 boxes, if so there is nothing else to
                # check.   Note that if j=0, then j-1 = the rank, hence the 
                # modular arithmetic 
                if self.a(j,k) - self.a( (j-1) % (n+1) ,k) <= 0:
                    continue
                else:
                # if the # of j boxes is greater than the # of j-1 boxes 
                # then we must find an index p such that
                # j+k = p + 1 mod (n+1) and at the same time 
                # we have # j boxes - # j-1 boxes is no bigger than La(h_p)
                # p_not_found is the state of this test.
                    p_not_found = True
                    for p in self.index_set():
                        if (j+k) % (n+1)  == (p+1) % (n+1) and self.a(j,k) - self.a( (j-1) % (n+1) ,k) <= La.scalar(ac[p]):
                            # test succeed, switch the test state
                            p_not_found = False
                            continue
                        else:
                            # p not found yet, we need to make sure that 
                            # we check all of the p values
                            continue
                    if p_not_found:
                        # after we have tested each p value,
                        # if no p is found then we can stop testing any other
                        # j or k values, this GYW is not in the highest weight
                        # crystal cut out by La
                        return False
        # if all of the above tests succeed, then this GYW is in the
        # highest weight crystal cut out by La
        return True



class CrystalOfGeneralizedYoungWalls(Parent):
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
        for height in range(h):
            for Y in [X for X in self.data if X.content()==height]:
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
        
        
    def digraph(self):
        from sage.graphs.all import DiGraph
        d = {}
        for x in self.data:
            d[x] = {}
            for i in self.index_set():
                child = x.f(i)
                if child in self.data:
                    d[x][child]=i
        G = DiGraph(d)
        if have_dot2tex():
            G.set_latex_options(format="dot2tex", edge_labels = True, 
                                color_by_label = self.cartan_type()._index_set_coloring)
        return G
    def plot(self, **options):
        """
        Returns the plot of self as a directed graph.
        """
        return self.digraph().plot(edge_labels=True,vertex_size=0,**options)

    def plot3d(self, **options):
        """
        Returns the 3-dimensional plot of self as a directed graph.
        """
        G = self.digraph(**options)
        return G.plot3d()    
    
    def dot_tex(self):
        """
        Returns a Dot2TeX version of self.
        """
        vertex_key = lambda x : "N_"+str(self.data.index(x))
        quoted_latex = lambda x: re.sub("\"|\r|(%[^\n]*)?\n","", x.latex_small())
        result = "digraph G { \n  node [ shape=plaintext ];\n"
        for x in self.data:
            result += "  " + vertex_key(x) + " [ label = \" \", texlbl = \"$"+quoted_latex(x)+"$\" ];\n"
        for x in self.data:
            for i in self.index_set():
                child = x.f(i)
                if child in self.data:
                    try:
                        result += "  " + vertex_key(x) + " -> "
                    except KeyError:
                        print x.pp()
                        print "x caused an error with the ranker function. Stopping execution."
                        return False
                    try:
                        result += vertex_key(child)
                    except KeyError as error:
                        print child.pp()
                        print "child caused an error with the ranker function. Stopping execution."
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
        
    def altlatex(self, **options):
            r"""
            Returns the crystal graph as a latex string. This can be exported
            to a file with self.latex_file('filename').
            """
            if not have_dot2tex():
                print "dot2tex not available.  Install after running \'sage -sh\'"
                return
            G=self.digraph()
            return G._latex_()
    
    def altlatex_file(self, filename):
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
        f.write(header + self.altlatex() + footer)
        f.close()
            

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
        

class HighestWeightCrystalOfGYW(CrystalOfGeneralizedYoungWalls):
    
    def __init__(self, n, h , La):
        super(HighestWeightCrystalOfGYW,self).__init__(n,h)
        self.hw = La
        
        self.originaldata = self.data
        
        self.data = []
        for c in self.originaldata:
            if c.in_highest_weight_crystal(La) : 
                self.data.append(c)

    def __repr__(self):
        return "Highest weight crystal of generalized Young walls of Cartan type {1!s} and highest weight {0!s} down to depth {2!s}.".format(self.hw, self.cartan_type(), self.depth)

    def list(self):
        return self.data
        
    def HW_test(self,first_factor):
        list = []
        for wall in self.data:
            if wall.Epsilon() <= self.hw:
                list.append([wall,first_factor+self.hw+wall.weight()])
        return list
