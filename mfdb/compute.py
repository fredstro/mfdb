##############
# The code REQUIRES: 12779
#          benefits from: 12772, 11358, 12640, 10281
# 
import sage.all

import os

import sqlite3
import nosqlite
# Use SFTP via paramiko to work with files remotely
# (since some of the HPC systems has ridiculously low quotas)
try: 
    import paramiko
except ImportError:
    print "Note that remote files are not supported without paramiko installed!"

#nsql = nosqlite.Client('nsql')
verbose = 0
import sage
from sage.modular.modsym.space import is_ModularSymbolsSpace
from sage.all import (ModularSymbols, DirichletGroup, trivial_character,
                      dimension_new_cusp_forms,
                      save, load,
                      cputime,
                      fork, parallel,
                      Integer,
                      prime_range, prime_divisors,
                      version,
                      Sequence,
                      cached_function,
                      Integer)

def dim_new(chi, k):
    if not isinstance(chi, (int, long, Integer)) and chi.is_trivial():
        return dimension_new_cusp_forms(chi.modulus(), k)
    else:
        return dimension_new_cusp_forms(chi, k)

def rangify(v):
        return [v] if isinstance(v, (int, long, Integer, str)) else v
    
@cached_function
def characters(N):
    """
    Return representatives for the Galois orbits of Dirichlet characters of level N.
    """
    return [X[0] for X in DirichletGroup(N).galois_orbits()]

def character_to_int(eps):
    """
    Return integer corresponding to given character.
    """
    if eps.is_trivial():
        return 0
    N = eps.modulus()
    X = characters(N)
    try:
        return X.index(eps)
    except IndexError:
        # very unlikely -- would have to be some weird character
        # not got from character(N,i)
        for i, Y in enumerate(DirichletGroup(N).galois_orbits()):
            if X in Y:
                return i
        raise RuntimeError

def character(N, i):
    if i==0:
        return trivial_character(N)
    #print "character(%s, %s)"%(N,i)
    return characters(N)[i]

def parse_Nki(s):
    return tuple(int(x) for x in s.split('-'))

def rexists(sftp, path):
    """os.path.exists for paramiko's SCP object
    """
    try:
        sftp.stat(path)
    except IOError, e:
        if e[0] == 2:
            return False
        raise
    else:
        return True

from stat import S_ISDIR

    
class Filenames(object):
    def __init__(self, data,host='',db_file='',username=''):
        r"""
        If host is left empty we work with local files, otherwise via SFTP 
        """
        self._host = host
        self._sftp = None
        self._ssh = None
        if self._host <> '':
            try:
                self._ssh = paramiko.SSHClient()
            except ImportError:
                raise ValueError,"If paramiko is not installed you must use local files! You set host:{0}".format(self._host)
            self._ssh.load_host_keys(os.path.expanduser(os.path.join("~", ".ssh", "known_hosts")))
            self._ssh.connect(self._host, username=username, password='')
            self._sftp = self._ssh.open_sftp()
        if not self.path_exists(data):
            raise RuntimeError, "please create the data directory '%s'"%data
        self._data = data
        if db_file <> '':
            self._known_db_file = db_file
        elif self._host=='':
            self._known_db_file = os.path.join(self._data, 'known.sqlite3')
        else:
            self._known_db_file = "{0}:{1}/known.sqlite3".format(host,data)

    ## file interface functions
            
    def path_exists(self,f):
        r"""
        Check if the path f exists as a local file or on the remote host.
        """
        if self._sftp == None:
            return os.path.exists(f)
        else:
            return rexists(self._sftp,f)

    def make_path_name(self,f,*args):
        if self._sftp==None:
            s = os.path.join(self._data,f) # , self.space_name(N,k,i))
        else:
            s = "{0}/{1}".format(self._data,f)
        for fs in args:
            s+= "/{0}".format(fs)
        return s
    
    def makedirs(self,f):
        if self._sftp==None:
            os.makedirs(f)
        else:
            self._sftp.mkdir(f)
    def listdir(self,f):
        if self._sftp == None:
            return os.listdir(f)
        else:
            return self._sftp.listdir(f)

    def isdir(self,path):
        if self._sftp==None:
            return os.path.isdir(path)
        else:
            try:
                return S_ISDIR(self._sftp.stat(path).st_mode)
            except IOError:
                # Path does not exist, so by definition not a directory
                return False


    def delete_file(self,path):
        if self._sftp == None:
            os.unlink(path)
        else:
            self._sftp.remove(path)


        
    def space_name(self, N, k, i):
        return '%05d-%03d-%03d'%(N,k,i)
    
    def space(self, N, k, i, makedir=False):
        f = self.make_path_name(self.space_name(N,k,i))
        if makedir and not self.path_exists(f):
            self.makedirs(f)
        return f

    def M(self, N, k, i, makedir=False):
        return self.make_path_name(self.space(N,k,i,makedir=makedir), 'M.sobj')

    def ambient(self, N, k, i, makedir=False):
        return self.make_path_name(self.space(N,k,i,makedir=makedir), 'ambient.sobj')

    def decomp_meta(self, N, k, i):
        return self.make_path_name(self.space(N,k,i), 'decomp-meta.sobj')
    
    def factor(self, N, k, i, d, makedir=False):
        f = self.make_path_name(self.space(N,k,i,makedir), '%03d'%d)
        if makedir and not self.path_exists(f):
            self.makedirs(f)
        return f

    def number_of_known_factors(self, N, k, i):
        fn = self.space(N,k,i)
        return len([d for d in self.listdir(fn) if
                    d.isdigit() and self.isdir(self.make_path_name(fn, d))])
        
    def factor_basis_matrix(self, N, k, i, d):
        return self.make_path_name(self.factor(N,k,i,d), 'B.sobj')
    
    def factor_dual_basis_matrix(self, N, k, i, d):
        return self.make_path_name(self.factor(N,k,i,d), 'Bd.sobj')
    
    def factor_dual_eigenvector(self, N, k, i, d, makedir=True):
        return self.make_path_name(self.factor(N,k,i,d,makedir=makedir), 'v.sobj')

    def factor_eigen_nonzero(self, N, k, i, d):
        return self.make_path_name(self.factor(N,k,i,d), 'nz.sobj')

    def factor_aplist(self, N, k, i, d, makedir, *args):
        a = '-'.join('%05d'%x for x in args)
        return self.make_path_name(self.factor(N,k,i,d,makedir), 'aplist-%s.sobj'%a)

    def factor_atkin_lehner(self, N, k, i, d, makedir):
        return self.make_path_name(self.factor(N,k,i,d,makedir), 'atkin_lehner.txt')

    def known_levels(self):
        res = []
        for Nki in self.listdir(self._data):
            z = Nki.split('-')
            if len(z) == 3:
                N, k, i = parse_Nki(Nki)
                if N not in res:
                    res.append(N)
        return res
    
    def meta(self, filename):
        base, ext = os.path.splitext(filename)
        return base + '-meta.sobj'

    def find_known(self):
        """
        Return iterator of 5-tuples of Python ints, defined as follows:

            (N, k, i, newforms, maxp)
            (37, 2, 0, 2, 10000)

        Here N = level, k = weight, i = character, newforms = number of newforms,
        maxp = integer such that a_p is known for p<=maxp.

        If no newforms are known but there are newforms (they just
        haven't been computed), then newforms is set to -1.
        """
        for Nki in self.listdir(self._data):
            z = Nki.split('-')
            if len(z) == 3:
                N, k, i = parse_Nki(Nki)
                if k==1: # weight 1 not implemented
                    continue
                newforms = [x for x in self.listdir(self.make_path_name(self._data, Nki)) if x.isdigit()]
                if len(newforms) == 0:
                    # maybe nothing computed?
                    if i == 0:
                        # program around a bug in dimension_new_cusp_forms: Trac 12640
                        d = dimension_new_cusp_forms(N,k)
                    else:
                        chi = character(N, i)
                        d = dimension_new_cusp_forms(chi, k)
                    if d == 0:
                        # definitely no newforms
                        yield (N,k,i,0,0)
                    else:
                        # we just don't know the newforms yet
                        yield (N,k,i,-1,0)
                else:
                    maxp = None
                    for n in newforms:
                        v = set([])
                        this_maxp = 0
                        for X in self.listdir(self.make_path_name(self._data, Nki, n)):
                            if X.startswith('aplist') and 'meta' not in X:
                                args = [int(a) for a in X.rstrip('.sobj').split('-')[1:]]
                                v.update(prime_range(*args))
                                this_maxp = max(this_maxp, max(args))
                        if len(v) != len(prime_range(this_maxp)):
                            # something missing!
                            if verbose>0:
                                print "data ranges are missing in the aplist data for %s"%Nki
                            maxp = 100
                        else:
                            maxp = this_maxp if maxp is None else min(this_maxp, maxp)

                    yield (N,k,i,len(newforms),maxp)

    def update_known_db(self):
        # 1. create the sqlite3 database
        # Unlink is only necessary with loal files
        if os.path.exists(self._known_db_file):
            os.unlink(self._known_db_file)
        db = sqlite3.connect(self._known_db_file)
        cursor = db.cursor()
        schema = 'CREATE TABLE "known" (N, k, i, newforms, maxp)'
        cursor.execute(schema)
        db.commit()

        # 2. iterate over known 5-tuples inserting them in db
        for t in self.find_known():
            #print t
            cursor.execute("INSERT INTO known VALUES(?,?,?,?,?)", t)

        db.commit()


    def known(self, query):
        # TODO -- fix db
        query = query.replace('prec','maxp')
        
        # 1. open database
        db = sqlite3.connect(self._known_db_file)
        cursor = db.cursor()

        # 2. return result of query
        # really stupid and dangerous?
        if ';' in query:
            query = query.split(';')[0]

        cmd = 'SELECT * FROM known '
        if query.strip():
            cmd += 'WHERE %s'%query
        cmd += ' ORDER BY N, k, i'
        return cursor.execute(cmd)
        
    def find_missing(self, Nrange, krange, irange, fields=None):
        """
        Return generator of
        
             {'N':N, 'k':k, 'i':i, 'missing':missing, ...},

        where missing is in the intersection of fields and the
        following strings (or all strings if fields is None):

                'M', 'decomp',
                'aplist-00100',  'aplist-00100-01000',  'aplist-01000-10000',
                'charpoly-00100','charpoly-00100-01000','charpoly-01000-10000',
                'zeros', 
                'leading', 
                'atkin_lehner'

        If the string is not 'M' or 'decomp' then the meaning is that
        the indicated data is not complete for *all* newforms in this
        space, i.e., at least one is missing.  If 'decomp' is given,
        it means the decomp isn't complete (it could be partial).
        
        Spaces with dimension 0 are totally ignored. 

        Note that not every missing is listed, just the *next* one that
        needs to be computed, e.g., if (11,2,0,'M') is output, then
        nothing else for (11,2,0,*) will be output.
        """
        if fields is None:
            fields = set(['M', 'decomp',
                'aplist-00100',  'aplist-00100-01000',  'aplist-01000-10000',
                'charpoly-00100','charpoly-00100-01000','charpoly-01000-10000',
                'zeros', 
                'leading', 
                'atkin_lehner'])
        else:
            assert isinstance(fields, (list, tuple, str))
            fields = set(fields)

        space_params = set(self.listdir(self._data))
        for k in rangify(krange):
            for N in rangify(Nrange):
                for ch in rangify(irange):
                    
                    if isinstance(ch, str):
                        CHI = list(enumerate(characters(N)))
                        if ch == 'quadratic':
                            CHI = [(i,chi) for i,chi in CHI if chi.order()==2]
                        elif ch == 'all':
                            pass
                        else:
                            raise ValueError
                    else:
                        try:
                            CHI = [(ch, character(N, ch))]
                        except IndexError:
                            CHI = []
                            
                    for i, chi in CHI:
                        N,k,i = int(N), int(k), int(i)
                        obj = {'space':(N,k,i)}
                        dim = dim_new(chi, k)
                        if dim > 0:
                            fields0 = list(fields)
                            if 'M' in fields0:
                                fields0.remove('M')
                            if 'decomp' in fields0:
                                fields0.remove('decomp')
                            Nki = self.space_name(N,k,i)
                            d3 = self.make_path_name(self._data, Nki)
                            if Nki not in space_params or not self.path_exists(self.make_path_name(d3, 'M-meta.sobj')):
                                if 'M' in fields:
                                    obj2 = dict(obj)
                                    obj2['missing'] = 'M'
                                    yield obj2
                                break
                            newforms = []
                            for fname in self.listdir(d3):
                                if fname.isdigit():
                                    # directory containing data about a newforms
                                    d2 = self.make_path_name(d3, fname)
                                    deg = self.make_path_name(d2, 'degree.txt')
                                    if self.path_exists(deg):
                                        degree = eval(open(deg).read())
                                    else:
                                        B_file = self.make_path_name(d2, 'B.sobj')
                                        if not self.path_exists(B_file):
                                            degree = None
                                        else:
                                            degree = load(B_file).nrows()
                                            open(self.make_path_name(d2, 'degree.txt'),'w').write(str(degree))
                                    f = {'fname':fname, 'degree':degree,
                                         'other':set([x.split('.')[0] for x in self.listdir(d2)])}
                                    newforms.append(f)
                            degs = [f['degree'] for f in newforms]
                            if None in degs:
                                sum_deg = None
                            else:
                                sum_deg = sum(degs)
                            if 'decomp' in fields and (sum_deg is None or sum_deg != dim):
                                obj2 = dict(obj)
                                obj2['missing'] = 'decomp'
                                obj2['newforms'] = newforms
                                if sum_deg > dim:
                                    obj2['bug'] = 'sum of degrees (=%s) is too big (should be %s) -- internal consistency error!'%(sum_deg, dim)
                                yield obj2
                                break
                            missing = []
                            for other in fields0:
                                for j in range(len(newforms)):
                                    if other not in newforms[j]['other']:
                                        missing.append(other)
                                        break
                            if missing:
                                missing.sort()
                                obj2 = dict(obj)
                                obj2['missing'] = 'other'
                                obj2['other'] = missing
                                yield obj2
                        
                            
################################################    

#filenames = Filenames('data')

# ambient spaces

# use @fork to avoid any memory leaks
### A more specialized class


class FilenamesMFDB(Filenames):
    r"""

    """
    def __init__(self,data):
        super(FilenamesMFDB,self).__init__(data)        


    @fork    
    def compute_ambient_space(self,N, k, i,**kwds):
        if i == 'all':
            G = DirichletGroup(N).galois_orbits()
            sgn = (-1)**k
            for j, g in enumerate(G):
                if g[0](-1) == sgn:
                    self.compute_ambient_space(N,k,j,**kwds)
            return

        if i == 'quadratic':
            G = DirichletGroup(N).galois_orbits()
            sgn = (-1)**k
            for j, g in enumerate(G):
                if g[0](-1) == sgn and g[0].order()==2:
                    self.compute_ambient_space(N,k,j,**kwds)
            return
        filename = self.ambient(N, k, i)
        if self.path_exists(filename):
            return
        eps = character(N, i)
        t = cputime()
        M = kwds.get('M',None)
        if M ==  None or M.sign()<>N or M.weight()<>k or M.level()<>N or M.character()<> eps or not is_ModularSymbolsSpace(M):
            t = cputime()
            M = ModularSymbols(eps, weight=k, sign=1)
            tm = cputime(t)
        else:
            tm = kwds.get('tm')
        self.save_ambient_space(M,i)
        #save(M, filename)
        meta = {'cputime':tm, 'dim':M.dimension(), 'M':str(M), 'version':sage.version.version}
        save(meta, self.meta(filename))
        if verbose>0:
            print "save {0} to {1}".format(meta,filename)

    def compute_ambient_spaces(self,Nrange, krange, irange, ncpu,**kwds):
        @parallel(ncpu)
        def f(N,k,i):
            self.compute_ambient_space(N,k,i,**kwds)

        v = [(N,k,i) for N in rangify(Nrange) for k in rangify(krange) for i in rangify(irange)]
        for X in f(v):
            print X

    def ambient_to_dict(self,M, i=None):
        """
        Data structure of dictionary that is created:

            - 'space': (N, k, i), the level, weight, and and integer
              that specifies character in terms of table; all Python ints
            - 'eps': (character) list of images of gens in QQ or cyclo
              field; this redundantly specifies the character
            - 'manin': (manin_gens) list of 2-tuples or 3-tuples of
              integers (all the Manin symbols)
            - 'basis': list of integers -- index into above list of Manin symbols
            - 'rels': relation matrix (manin_gens_to_basis) -- a sparse
              matrix over a field (QQ or cyclotomic)
            - 'mod2term': list of pairs (n, c), such that the ith element
              of the list is equivalent via 2-term relations only
              to c times the n-th basis Manin symbol; these
        """
        if i is None:
            i = self.character_to_int(M.character())
        return {'space':(int(M.level()), int(M.weight()), int(i)),
                'eps':list(M.character().values_on_gens()),
                'manin':[(t.i,t.u,t.v) for t in M._manin_generators],
                'basis':M._manin_basis,
                'rels':M._manin_gens_to_basis,
                'mod2term':M._mod2term}

    def dict_to_ambient(self,modsym):
        #print "WWEWEW=",modsym
        N,k,i = modsym['space']
        eps   = modsym['eps']
        manin = modsym['manin']
        basis = modsym['basis']
        rels  = modsym['rels']
        mod2term  = modsym['mod2term']
        F = rels.base_ring()
        if i == 0:
            eps = trivial_character(N)
        else:
            eps = DirichletGroup(N, F)(eps)

        from sage.modular.modsym.manin_symbols import ManinSymbolList, ManinSymbol
        manin_symbol_list = ManinSymbolList(k, manin)

        def custom_init(M):
            # reinitialize the list of Manin symbols with ours, which may be
            # ordered differently someday:
            syms = M.manin_symbols()
            ManinSymbolList.__init__(syms, k, manin_symbol_list)

            M._manin_generators = [ManinSymbol(syms, x) for x in manin]
            M._manin_basis = basis
            M._manin_gens_to_basis = rels
            M._mod2term = mod2term
            return M

        return ModularSymbols(eps, k, sign=1, custom_init=custom_init, use_cache=False)

    def save_ambient_space(self,M, i):
        N = M.level()
        k = M.weight()
        fname = self.ambient(N, k, i, makedir=True)
        if self.path_exists(fname):
            print "%s already exists; not recreating"%fname
            return
#        fnameM = self.M(N, k, i, makedir=True)
#        if self.path_exists(fname):
#            print "%s already exists; not recreating"%fnameM
#            M = load(fnameM)
#            save(M,fname)
#            return
        if verbose>0:
            print "Creating ", fname
        save(self.ambient_to_dict(M, i), fname)

    def load_M(self,N, k, i):
        return load(self.M(N, k, i, makedir=False))

    def convert_M_to_ambient(self,N, k, i):
        self.save_ambient_space(self.load_M(N,k,i), i)

    def convert_all_M_to_ambient(self):
        d = self._data
        for X in self.listdir(d):
            p = self.make_path_name(d, X)
            if self.isdir(p):
                f = set(self.listdir(p))
                if 'M.sobj' in f and 'ambient.sobj' not in f:
                    print X
                    #try:
                    self.convert_M_to_ambient(*parse_Nki(X))
                    #except:
                    #    print "ERROR!"

    def delete_all_M_after_conversion(self):
        d = self._data
        for X in self.listdir(d):
            p = self.make_path_name(d, X)
            if self._db.isdir(p):
                f = set(self.listdir(p))
                if 'M.sobj' in f and 'ambient.sobj' in f:
                    print "Remove: \n ",X                    
                    self.delete_file(self.make_path_name(p, 'M.sobj'))

     # old version -- doesn't require trac 12779.
    #def load_ambient_space(N, k, i):
    #    return load(filenames.M(N, k, i, makedir=False))

    def load_ambient_space(self,N, k, i):
        fname = self.ambient(N, k, i, makedir=False)
        #print "fname=",fname
        if self.path_exists(fname):
            return self.dict_to_ambient(load(fname))
        fname = self.ambient(N, k, i, makedir=False)
        if self.path_exists(fname):
            return load(fname)
        raise ValueError, "ambient space (%s,%s,%s) not yet computed"%(N,k,i)

    def load_factor(self,N, k, i, d, M=None):
        import sage.modular.modsym.subspace
        if M is None:
            M = self.load_ambient_space(N, k, i)
        f = self.factor(N, k, i, d, makedir=False)
        if not self.path_exists(f):
            raise RuntimeError, "no such factor (%s,%s,%s,%s)"%(N,k,i,d)
        try:
            B = load(self.factor_basis_matrix(N, k, i, d))
            Bd = load(self.factor_dual_basis_matrix(N, k, i, d))
            v = load(self.factor_dual_eigenvector(N, k, i, d))
            nz = load(self.factor_eigen_nonzero(N, k, i, d))
        except IOError:
            raise RuntimeError,"Data is incomplete for factor ({0}) at {1}".format((N,k,i,d),f)
        B._cache['in_echelon_form'] = True
        Bd._cache['in_echelon_form'] = True
        # These two lines are scary, obviously, since they depend on
        # private attributes of modular symbols.
        A = sage.modular.modsym.subspace.ModularSymbolsSubspace(M, B.row_module(), Bd.row_module(), check=False)
        A._HeckeModule_free_module__dual_eigenvector = {('a',nz):(v,False)}
        A._is_simple = True
        A._HeckeModule_free_module__decomposition = {(None,True):Sequence([A], check=False)}
        return A

    def load_aps(self,N, k, i, d, ambient=None,numc=-1):
        r"""
        Load aps for a given factor. If numc > 0 we return all sets.
        """
        import sage.modular.modsym.subspace
        F = self.load_factor(N, k, i, d, ambient)
        factor_dir = self.factor(N, k, i, d, makedir=False)
        try:
            tmp = self.listdir(factor_dir)
        except OSError:
            return 
        aplist_files = []; aplist_meta_files = []
        for fname in tmp:
            if "aplist" in fname:
                if "meta" in fname:
                    numap = int(fname.split("-")[1])
                    aplist_meta_files.append((numap,fname))
                else:
                    numap = int(fname.split("-")[1].split(".")[0])
                    aplist_files.append((numap,fname))
        if aplist_files == []:
            return 
        if numc == 'max' or numc == -1: # Find max no. of coeffs.
            numap,fname = max(aplist_files)
        elif numc == 'min' or numc == 0: # Find min. no. of coeffs.
            numap,fname = min(aplist_files)
        else:
            numap,fname = aplist_files[0]
            for n,c in aplist_files[1:]:
                if c == numc:
                    numap,fname = n,c
                    break
        metaname = fname.split(".")[0]+"-meta.sobj"
        try:
            E = load("{0}/{1}".format(factor_dir,fname))
            v = load("{0}/v.sobj".format(factor_dir))
            meta = load("{0}/{1}".format(factor_dir,metaname))
        except Exception as e:
            raise ValueError,"Could not load factor: {0}. Error:{1}".format(factor_dir,e.message)
        
        return E,v,meta

    
 

class ComputeMFData(object):
    r"""
    Use Williams methods to compute tables of modular forms data
    """
    def __init__(self,db,compute_ambient=False):
        r"""
        compute_ambient = True if you want to compute ambient spaces when missing
        """
        if isinstance(db,str):
            db = FilenamesMFDB(db)
        self._compute_ambient = compute_ambient
        self._db = db  ## Should be instance of, e.g. FilenamesMFDB
        self._collection = self._db
    # decompositions
    def compute_ambient_space(self,N,k,i,**kwds):
        self._db.compute_ambient_space(N,k,i,**kwds)

    def compute_ambient_spaces(self,Nrange, krange, irange, ncpu=1,**kwds):
        @parallel(ncpu)
        def f(N,k,i):
            self.compute_ambient_space(N,k,i,**kwds)

        v = [(N,k,i) for N in rangify(Nrange) for k in rangify(krange) for i in rangify(irange)]
        for X in f(v):
            print X
   
       
    @fork    
    def compute_decompositions(self,N, k, i,verbose=0,**kwds):
        if i == 'all':
            G = DirichletGroup(N).galois_orbits()
            sgn = (-1)**k
            numo = 0
            for j, g in enumerate(G):
                if g[0](-1) == sgn:
                    numo+=self.compute_decompositions(N,k,j,**kwds)
            return numo

        if i == 'quadratic':
            G = DirichletGroup(N).galois_orbits()
            sgn = (-1)**k
            numo = 0
            for j, g in enumerate(G):
                if g[0](-1) == sgn and g[0].order()==2:
                    num0+=self.compute_decompositions(N,k,j,**kwds)
            return numo

        filename = self._db.ambient(N, k, i)        
        if verbose>0:
            print "filename=",filename
        if not self._db.path_exists(filename):
            print "Ambient space ({0},{1},{2}) not computed. filename={3}".format(N,k,i,filename)
            #return
            self.compute_ambient_space(N, k, i,**kwds)
        if not self._db.path_exists(filename):
            return 0
        eps = DirichletGroup(N).galois_orbits()[i][0]
        # check if the factor already exists by checking for 
        if verbose>0:
            print "check if path exists {0}".format(self._db.factor_eigen_nonzero(N, k, i, 0))
        if self._db.path_exists(self._db.factor_eigen_nonzero(N, k, i, 0)):
            return self._db.number_of_known_factors(N,k,i) 
        t = cputime()
        M = self._db.load_ambient_space(N, k, i)
        if verbose>0:
            print "M=",M
        if kwds.get('D') is None:
            D = M.cuspidal_subspace().new_subspace().decomposition()
        else:
            D = kwds['D']
        if verbose>0:
            print "D=",D
        for d in range(len(D)):
            self._db.factor(N,k,i,d,makedir=True)
            f = self._db.factor_basis_matrix(N, k, i, d)
            if self._db.path_exists(f):
                continue
            A = D[d]
            B  = A.free_module().basis_matrix()
            Bd = A.dual_free_module().basis_matrix()
            v  = A.dual_eigenvector(names='a', lift=False)    # vector over number field
            nz = A._eigen_nonzero()
            name = self._db.factor_basis_matrix(N, k, i, d)
            save(B, name)
            save(Bd, self._db.factor_dual_basis_matrix(N, k, i, d))
            save(v, self._db.factor_dual_eigenvector(N, k, i, d))
            save(nz, self._db.factor_eigen_nonzero(N, k, i, d))

        tm = cputime(t)
        meta = {'cputime':tm, 'number':len(D), 'version':sage.version.version}
        save(meta, self._db.decomp_meta(N, k, i))
        return len(D)
    
    def compute_decomposition_ranges(self,Nrange, krange, irange, ncpu,verbose=0):
        @parallel(ncpu)
        def f(N,k,i):
            self.compute_decompositions(N,k,i,verbose=verbose)

        v = [(N,k,i) for N in rangify(Nrange) for k in rangify(krange) for i in rangify(irange)]
        for X in f(v):
            print X

    def compute_ambient_space_ranges(self,Nrange, krange, irange, ncpu):
        @parallel(ncpu)
        def f(N,k,i):
            self._db.compute_ambient_space(N,k,i)
        v = [(N,k,i) for N in rangify(Nrange) for k in rangify(krange) for i in rangify(irange)]
        for X in f(v):
            print X
    # atkin_lehner
    @fork    
    def compute_atkin_lehner(self,N, k, i,M=None,m=None,**kwds):
        verbose = kwds.get('verbose',0)
        filename = self._db.ambient(N, k, i)
        if not self._db.path_exists(filename):
            print "Ambient (%s,%s,%s) space not computed. Filename=%s "%(N,k,i,filename)
            return -1
            #compute_ambient_space(N, k, i)
        if verbose>0:
            print "computing atkin-lehner for (%s,%s,%s)"%(N,k,i)
        if m is None:
            m = self._db.number_of_known_factors(N, k, i)
        if M is None:
            M = self._db.load_ambient_space(N, k, i)
        for d in range(m):
            atkin_lehner_file = self._db.factor_atkin_lehner(N, k, i, d, False)
            if self._db.path_exists(atkin_lehner_file):
                if verbose>0:
                    print "skipping computing atkin_lehner for (%s,%s,%s,%s) since it already exists"%(N,k,i,d)
                # already done
                continue
            # compute atkin_lehner
            if verbose>0:
                print "computing atkin_lehner for (%s,%s,%s,%s)"%(N,k,i,d)
            t = cputime()
            A = self._db.load_factor(N, k, i, d, M)
            #print "A=",A
            #print "character=",A.character()
            #print "character order=",A.character().order()
            al = ' '.join(['+' if a > 0 else '-' for a in atkin_lehner_signs(A)])
            #print al
            open(atkin_lehner_file, 'w').write(al)
            tm = cputime(t)
            meta = {'cputime':tm, 'version':sage.version.version}
            save(meta, self._db.meta(atkin_lehner_file))

    # aplists
    @fork    
    def compute_aplists(self,N, k, i, *args):
        if i == 'all':
            G = DirichletGroup(N).galois_orbits()
            sgn = (-1)**k
            for j, g in enumerate(G):
                if g[0](-1) == sgn:
                    self.compute_aplists(N,k,j,*args)
            return

        if i == 'quadratic':
            G = DirichletGroup(N).galois_orbits()
            sgn = (-1)**k
            for j, g in enumerate(G):
                if g[0](-1) == sgn and g[0].order()==2:
                    self.compute_aplists(N,k,j,*args)
            return

        if len(args) == 0:
            args = (100, )

        filename = self._db.ambient(N, k, i)
        if not self._db.path_exists(filename):
            print "Ambient ({0},{1},{2}) space not computed. Filename:{3}".format(N,k,i,filename)
            return -1
            #compute_ambient_space(N, k, i)
        if verbose>0:
            print "computing aplists for (%s,%s,%s)"%(N,k,i)

        m = self._db.number_of_known_factors(N, k, i)
        if verbose>0:
            print "m=",m
        if m == 0:
            # nothing to do
            return

        M = self._db.load_ambient_space(N, k, i)
        if verbose>0:
            print "M,m=",M,m
        for d in range(m):
            aplist_file = self._db.factor_aplist(N, k, i, d, False, *args)
            if self._db.path_exists(aplist_file):
                if verbose>0:
                    print "skipping computing aplist(%s) for (%s,%s,%s,%s) since it already exists"%(args, N,k,i,d)
                # already done
                continue

            # compute aplist
            if verbose>0:
                print "computing aplist(%s) for (%s,%s,%s,%s)"%(args, N,k,i,d)
            t = cputime()
            A = self._db.load_factor(N, k, i, d, M)
            aplist, _ = A.compact_system_of_eigenvalues(prime_range(*args), 'a')
            #print aplist, aplist_file
            save(aplist, aplist_file)
            tm = cputime(t)
            meta = {'cputime':tm, 'version':sage.version.version}
            if verbose>0:
                print "meta=",meta
            save(meta, self._db.meta(aplist_file))

    def compute_aplists_ranges(self,Nrange, krange, irange, ncpu, *args):
        @parallel(ncpu)
        def f(N,k,i):
            self.compute_aplists(N,k,i,*args)

        v = [(N,k,i) for N in rangify(Nrange) for k in rangify(krange) for i in rangify(irange)]
        for X in f(v):
            print X

    def phase1_goals(self,stages, fields=None):
        """
          Trivial character S_k(G0(N)):
             0. k=2   and N<=4096= 2^12
             1. k<=16 and N<=512 = 2^9
             2. k<=32 and N<=32  = 2^5
          Nontrivial character S_k(N, chi):
             3. k<=16, N<=128 = 2^7, all chi quadratic
             4. k=2,   N<=128 = 2^7, all chi!=1, up to Galois orbit
        """
        if 0 in stages:
            for X in self._db.find_missing(range(1,4096+1), [2], 0, fields=fields):
                yield X

        if 1 in stages:
            for X in self._db.find_missing(range(1,513),
                                            range(2,17,2), 0, fields=fields):
                yield X

        if 2 in stages:
            for X in self._db.find_missing(range(1,33),
                                            range(2,33,2), 0, fields=fields):
                yield X

        if 3 in stages:
            for X in self._db.find_missing(range(1,129),
                                     range(2,17), 'quadratic', fields=fields):
                yield X

        if 4 in stages:
            for X in self._db.find_missing(range(1,129), 2, 'all', fields=fields):
                yield X


    def phase1_goals0(self,stages, fields=None):
        v = []
        for X in phase1_goals(stages, fields):
            print X
            v.append(X)
        return v

    # suggestion for collection is: mfself.compute.nsql.missing.phase0
    def phase1_goals_self(self, stages, fields=None):
        for X in self.phase1_goals(stages, fields):
            print X
            self._collection.insert(X)

    def generate_computations_missing_M(self):
        v = []
        for X in self._collection.find_missing(fields="M"):
            N,k,i = X['space']
            v.append('compute_ambient_space(%s,%s,%s)'%(N,k,i))
        return list(sorted(set(v)))

    def generate_computations_missing_decomp(self):
        v = []
        for X in self._collection.find_missing(field="decomp"):
            N,k,i = X['space']
            v.append('compute_decompositions(%s,%s,%s)'%(N,k,i))
        return list(sorted(set(v)))        

    def generate_computations_missing_aplists(self):
        v = []
        for X in self._collection.find_missing(fields="other"):
            N,k,i = X['space']
            if 'aplist-00100' in X['other']:
                v.append('compute_aplists(%s, %s, %s, 100)'%(N,k,i))
            if 'aplist-00100-01000' in X['other']:
                v.append('compute_aplists(%s, %s, %s, 100, 1000)'%(N,k,i))
            if 'aplist-01000-10000' in X['other']:
                v.append('compute_aplists(%s, %s, %s, 1000, 10000)'%(N,k,i))
    ##         if 'charpoly-00100' in X['other']:
    ##             v.append('compute_charpolys(%s, %s, %s, 100)'%(N,k,i))
    ##         if 'charpoly-00100-01000' in X['other']:
    ##             v.append('compute_charpolys(%s, %s, %s, 100, 1000)'%(N,k,i))
    ##         if 'charpoly-01000-10000' in X['other']:
    ##             v.append('compute_charpolys(%s, %s, %s, 1000, 10000)'%(N,k,i))
        return list(sorted(set(v)))        



import sage.all
def parallel_eval(v, ncpu, do_fork=True):
    """
    INPUT:
    - v -- list of strings that can be eval'd in this scope.
    """
    @parallel(ncpu)
    def f(X):
        if do_fork:
            @fork
            def g():
                return eval(X)
            return g()
        else:
            return eval(X)
    for Z in f(v):
        print Z
        
    

def atkin_lehner_signs(A):
    N = A.level()
    return [A.atkin_lehner_operator(p).matrix()[0,0] for p in prime_divisors(N)]




    
