r"""
Programs aimed to read Williams data and convert to/from other files or databases
"""
import sage.all
import os
import glob
import sqlite3
#import nosqlite
#nsql = nosqlite.Client('nsql')
import pymongo
Con1 = pymongo.Connection('localhost:27017')
Con = pymongo.Connection('localhost:37010')
     


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
import mfdb.compute
db = mfdb.compute.filenames

def make_query(N='all',k='all',i='all'):
    r"""
    Make a query string from N,k and i
    
    """
    qN="1";qk="1";qi="1"
    if N<>'all':
        qN = "N={N}".format(N=N)
    if k<>'all':
        qk = "k={k}".format(k=k)
    if i<>'all':
        qi = "i={i}".format(i=i)
    q = "{qN} and {qk} and {qi}".format(qN=qN,qk=qk,qi=qi)
    #print "q=",q
    return q

def get_spaces(N,k,i,n=None,init_spaces=False):
    r"""
    Fetch all spaces matching the search parameters
    If init_spaces = False we only return a list of file names.
    """
    q = make_query(N,k,i)
    l = db.known(q)
    res = []
    for N,k,i,numorbits,aps in l:
        ### We have a modular form with this data.
        print db.space_name(N,k,i)
        res.append(db.ambient(N,k,i))  ## ambient space
    if init_spaces:
        res0 = map(lambda f: load(f),res)
        return res0
    return res



def get_aps(N0,k0,i0,n0=None,init_coeffs=False,all_coeffs=True):
    r"""
    Fetch aps for all spaces matching the search parameters
    If init_coeffs = False we only return a list of file names.
    """
    q = make_query(N0,k0,i0)
    l = db.known(q)
    res = {}
    rb = "[0-9][0-9][0-9][0-9][0-9]"
    for N,k,i,numorbits,aps in l:
        print N,k,i,numorbits,aps 
        for j in range(numorbits):
            if n0 <>None and j<>n0:
                continue
            print "aps=",aps
            v = mfdb.compute.load(db.factor_dual_eigenvector(N,k,i,j,makedir=False))
            ## initial list of ap's
            fname = db.factor_aplist(N,k,i,j,False,100)
            meta = load(mfdb.compute.filenames.meta(fname))
            aplist = mfdb.compute.load(fname)
            s = format_aps(aplist,v)
            res[(N,k,i,j)]={(0,100):(s,meta)}
            #print "a=",aplist
            #print "v=",v
            print "s=",s
            ## Do we want more coefficients
            if all_coeffs:
                cdir = mfdb.compute.filenames.factor(N,k,i,j)
                list_of_files = glob.glob('{dir}/aplist-{rb}-{rb}.sobj'.format(dir=cdir,rb=rb))
                print "list=",list_of_files
                for name in list_of_files:
                    print "name=",name
                    apn = re.findall("aplist.*",name)[0]                
                    ns = re.findall("[0-9]+",apn)
                    m,n =ns
                    fname = '{dir}/aplist-{m:05d}-{n:05d}.sobj'.format(dir=cdir,m=m,n=n)
                    aplist = mfdb.compute.load(fname) 
                    s = format_aps(aplist,v)
                    meta = load(mfdb.compute.filenames.meta(fname))
                    res[(N,k,i,j)]={(m,n):(s,meta)}
        return res

def format_aps(aplist,v):
    r"""
    String representation of the ap's
    """
    K = v.parent().base_ring()
    if hasattr(K, 'defining_polynomial'):
        s = "{0}".format(K.defining_polynomial().list())
    else:
        s = "1"  ## Defining polynomial for Q
    ap = str(list(aplist*v)).replace(' ','')
    if K.absolute_degree() >= 4:
        ap = ap.replace(',',',\n')
    s += '; {ap}'.format(ap=ap)
    return s


### Testing alternative storage of number field elements as plain text

ITMAX = 10000  ## Avoid infinite recursion
def random_polynomial(degb=5,cb=100,irreducible=True,it=0):
    r"""
    Return a random (irreducible) polynomial of degree <= degb and
    with coefficients bounded by cb in absolute value.
    """

    if it>ITMAX:
        raise Arithmeticerror,"Could not find irreducible polynomial within {0} iterations!".format(ITMAX)
    d = ZZ.random_element(2,degb)
    x = ZZ['x'].gens()[0]
    p = x**d
    
    for i in range(d-1):
        c = ZZ.random_element(-cb,cb)
        if c==0:
            c=1
        p = p + c*x**i

    if irreducible:
        if not p.is_irreducible():
            return random_polynomial(degb,cb,irreducible=True,it=it+1)
    return p

def random_number_field(degb=5,discb=5000,cb =100,it=0):
    r"""
    Return random number field with discriminant bounded by discb.
    """
    if it>ITMAX:
        raise Arithmeticerror,"Could not find number field with disciminant bounded by {0} in {1} iterations!".format(discbd,ITMAX)
    p = random_polynomial(degb,cb,True)
    if p.discriminant()>discb:
        return random_number_field(degb,discb,cb,it=it+1)
    return NumberField(p,names='x')
    
def random_list_of_number_field_elts(N,degb=5,discb=5000,cb=100):
    res = []
    F = random_number_field(degb,discb,cb)
    for i in range(N):
        res.append(F.random_element())
    return res
        

def convert_list(l):
    res = []
    for x in l:
        res.append(NF_to_str(x))
    return str(res)

def convert_dict(d):
    res = dict()
    for x in d.keys():
        res[d]=append(NF_to_str())
    return str(res)



def NF_to_str(x):
    K = x.parent()
    v = x.vector()
    #p = K.polynomial().list()
    s = "{0}:{1}".format(K.polynomial().list(),x.vector())
    return s
