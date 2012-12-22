#******************************************************************************
#  Copyright (C) 2013
#
#  Lucas David-Roesler (roesler at lvc dot edu)
#  Ben Salisbury (bsalisbury at sci dot ccny dot cuny dot edu)
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
#
#
#


import re
from sage.misc.latex import latex
from sage.graphs.graph import DiGraph
from sage.combinat import ranker

class GeneralizedYoungWall:
    '''
    construct a generalized young from its list representation
    
    INPUT:
    
    - ``data`` -- multi-list, containing the boxes of the generalized young wall read right to left bottom to top, empty list are required for each empty row.
    - ``n`` -- integer, this is the largest expected value in any box of the generalized young wall.
    
    EXAMPLES::
    
        sage: X = [[0,2,1,0,2],[1,0,2],[],[],[1],[],[],[1]]
        sage: XX = GeneralizeYoungWall(X,2)
        sage: XX.pp()
                1|
                 |
                 |        
                1|
                 |
                 |
            2|0|1|
        2|0|1|2|0|
        
        sage: Y = [[0,5,4,3,2],[],[2,1,0,5,4,3],[3,2],[],[5,4,3,2]]
        sage: YY = GeneralizeYoungWall(Y,5)
        sage| YY.pp()
            2|3|4|5|
                   |
                2|3| 
        3|4|5|0|1|2|
                   |
          2|3|4|5|0|
        
        sage: Z =  [[0,2,1],[1,0,2],[2],[],[],[2]]
        sage: ZZ = GeneralizeYoungWall(Z,2)
        sage: ZZ.pp()
             2|
              |
              |
             2|
         2|0|1|
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
        self._root_system = self._cartan_type.root_system()
        self._space = self._root_system.ambient_space()
#        self._positive_roots = self._space.positive_roots()
#        self._simple_roots = self._space.simple_roots()
#        self._fundamental_weights = self._space.fundamental_weights()
                
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
        return the sequence from {+,-} obtain from all i-admissible
        slots and removable i-boxes without canceling any (+,-)-pairs.
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
        we use sig_sort to sort the +/- signature by the elements in the 
        farthest column and lowest row.  The location of the +/- is stored
        as the standard (row,col).  Because we need farthest col first, we 
        switch the order and negate that value of the col, this forces large
        values to be 'small', hence giving the correct order of farthest column
        and lowest row.
        '''
        return (-a[2],a[1])
        
    def generate_signature(self, i):
        '''
        generante the reduced +/- i-signature. generate_signature will return
        a tuple containing the raw signature and the reduced signature.
        The raw signature is an multilist where each sublist conatins the location
        with respect to the original data defining the generalized young wall.
        The reduced signature is a sting that contains white space where the +-
        pairs were deleted. The whitepsace allows us to keep track of where each
        + or - came from in the raw signature.  To simply print the reduced
        signature use the function signature.
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
        Returns the application of the Kashiwara raising operator in the direction i
        on self.
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
        Returns the application of the Kashiwara lowering operator in the direction i
        on self.
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
        This also generates LaTeX code for self, but makes the output much  
        smaller.  Still requires TikZ.
        '''
        s = ""
        if self.data == []:
                s += "\\varnothing"
        else:
            s += "\\begin{tikzpicture}[baseline=20,scale=.25] \\foreach \\x [count=\\s from 0] in \n"
            s += "{" + ','.join("{" + ','.join( str(i) for i in r ) + "}" for r in self.data ) + "} \n"
            s += "{\\foreach \\y [count=\\t from 0] in \\x {  \\node[font=\\tiny] at (-\\t,\\s) {$\\y$}; \n \draw (-\\t+.5,\\s+.5) to (-\\t-.5,\\s+.5); \n \draw (-\\t+.5,\\s-.5) to (-\\t-.5,\\s-.5); \n \draw (-\\t-.5,\\s-.5) to (-\\t-.5,\\s+.5);  } \n \draw[-] (.5,\\s+1) to (.5,-.5) to (-\\t-1,-.5); } \n \\end{tikzpicture} \n"
        return s

    def type(self):
        return self._cartan_type
            
    def root_system(self):
        return self._root_system

    def space(self):
        return self._space

#    def positive_roots(self):
#        return self._positive_roots
#            
#    def simple_roots(self):
#        return self._simple_roots
#            
#    def fundamental_weights(self):
#        return self._fundamental_weights


class GeneralizedYoungWallCrystal:
    '''
    construct the crystal of generalized young walls in type affine A_n
    
    INPUT:
    - ``n`` -- integer, the rank of the affine Lie algebra, this determines the largest value of a box in the generalized young wall
    - ``h`` -- integer, only the generalized young walls with at most h boxes are generated
    
    EXAMPLES::
    
        sage: Y = GeneralizeYoungWallCrysal(2,2)
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

    
    def list(self):
        return self.data
     
    def report(self):
        for x in self.data:
            x.pp()
            print "\n-----\n"
        print ' There are a total of ' + str(len(self.data)) 
        print ' elements in the crystal, going down to depth ' + str(self.depth) +'.'
        
        
    def cartan_type(self):
        return self._cartan_type
    
    def index_set(self):
        print range(self.rank+1)
    
    def cardinality(self):
        return len(self.data)
    
    def dot_tex(self):
        """
        Returns a Dot2TeX version of self.
        """
        rank = ranker.from_list(self.list())[int(0)]
        vertex_key = lambda x: "N_"+str(rank(x))
        
        # To do: check the regular expression
        # Removing %-style comments, newlines, quotes
        # This should probably be moved to sage.misc.latex
        quoted_latex = lambda x: re.sub("\"|\r|(%[^\n]*)?\n","", x.latex_small())
        
        result = "digraph G { \n  node [ shape=plaintext ];\n"
        
        for x in self.data:
            result += "  " + vertex_key(x) + " [ label = \" \", texlbl = \"$"+quoted_latex(x)+"$\" ];\n"
        for x in self.data:
            for i in range(1, self.rank+1):
                child = x.f(i)
                if child in self.data:
                    result += "  " + vertex_key(x) + " -> " + vertex_key(child)
                    result += " [ label = \" \", texlbl = \"%d\" ];\n"%i
        result+="}"
        return result
    
    def latex(self):
        try:
            from dot2tex.dot2tex import Dot2TikZConv
        except ImportError:
            print "dot2tex not available.  Install after running \'sage -sh\'"
            return
        
        options = {'format':'tikz', 'crop':True, 'usepdflatex':True, 'figonly':True}
        
        content = (Dot2TikZConv(options)).convert(self.dot_tex())
        
        return content

    def latex_file(self, filename):
        header = r"""\documentclass{article}
            \usepackage[x11names, rgb]{xcolor}
            \usepackage[utf8]{inputenc}
            \usepackage{tikz}
            \usetikzlibrary{snakes,arrows,shapes,matrix}
            \usepackage{amsmath}
            \usepackage[active,tightpage]{preview}
            \newenvironment{bla}{}{}
            \PreviewEnvironment{bla}
            
            \begin{document}
            \begin{bla}"""
        
        footer = r"""\end{bla}
            \end{document}"""
        f = open(filename, 'w')
        f.write(header + self.latex() + footer)
        f.close()
        


