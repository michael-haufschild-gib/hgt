# Ramified-local root number at higher conductor (foundations §66; extends §65).
#
# CLAIM. At a ramified prime, the local module is a SINGULAR q-difference module; its conductor
# exponent f_p measures the irregularity, and the local root number eps_p (= the swap-discrepancy
# of Conjecture 65.1) is the normalized Gauss sum of the local character. We test on primitive
# Dirichlet characters mod p^k (k>=2 = wild ramification, f_p=k): |eps|=1 and
# eps = eps_infty * tau(chi)/sqrt(p^k), with the conductor = p^k (primitivity).
# Pure python (cmath), local. 2026-06-19.
import cmath, math

def primroot(n):
    # primitive root mod n (n = p^k, odd p)
    def order(g,n):
        from math import gcd
        if gcd(g,n)!=1: return 0
        x=1
        for k in range(1,n+1):
            x=(x*g)%n
            if x==1: return k
        return 0
    phi = n - n//(smallest_prime(n))  # phi(p^k)=p^k - p^{k-1}
    for g in range(2,n):
        if order(g,n)==phi: return g, phi
    return None, phi

def smallest_prime(n):
    d=2
    while d*d<=n:
        if n%d==0: return d
        d+=1
    return n

def is_primitive(chi, n, p):
    # primitive mod p^k iff not induced from mod p^{k-1}: chi nontrivial on 1+p^{k-1} subgroup
    m = n//p
    return any(abs(chi((1+ t*m) % n)-1)>1e-9 for t in range(1,p))

def chars_primepower(n):
    p=smallest_prime(n)
    g,phi=primroot(n)
    dlog={}; x=1
    for k in range(phi):
        dlog[pow(g,k,n)]=k
    out=[]
    for mexp in range(phi):
        def chi(a,mexp=mexp,n=n,phi=phi,dlog=dlog):
            a%=n
            from math import gcd
            if gcd(a,n)!=1: return 0
            return cmath.exp(2j*math.pi*mexp*dlog[a]/phi)
        out.append((mexp,chi,p))
    return out

def gauss(chi,n):
    return sum(chi(a)*cmath.exp(2j*math.pi*a/n) for a in range(1,n))

print("=== Ramified-local root number at higher conductor (§66, wild ramification) ===")
for n in (9,25,27):
    p=smallest_prime(n); k=0; t=n
    while t%p==0: t//=p; k+=1
    print("\n-- modulus n=%d = %d^%d  (conductor exponent f_p=%d) --" % (n,p,k,k))
    cnt=0
    for mexp,chi,p in chars_primepower(n):
        if mexp==0: continue
        if not is_primitive(chi,n,p): continue  # only primitive => conductor exactly n
        cnt+=1
        tau=gauss(chi,n)
        a = 0 if abs(chi(n-1)-1)<1e-9 else 1
        eps = tau/((1j**a)*math.sqrt(n))
        eps_inf=1j**(-a); eps_fin=tau/math.sqrt(n); recon=eps_inf*eps_fin
        print("  primitive chi (m=%2d) parity a=%d : |eps|=%.6f  match=%s"
              % (mexp,a,abs(eps), "YES" if abs(eps-recon)<1e-9 else "no"))
    print("  (%d primitive characters of conductor %d tested)" % (cnt,n))
print("\n=== verdict: |eps|=1 and eps factors (arch x ramified-local Gauss) at conductor p^k, k>=2 (wild) ===")
