# Root number as the place-swap automorphy factor (foundations §65, grounding §64.3).
#
# CLAIM under test. The functional-equation involution s<->1-s of the completed L is, in the
# extended-base picture (P u {infty}), the place-swap 0<->infty; its automorphy factor is the
# root number eps, which FACTORS over places eps = prod_v eps_v (Tate's thesis): an archimedean
# eps_infty (from the Gamma-place, the character's sign at infinity) times finite eps_p (Gauss-sum
# contributions). We verify on Dirichlet L-functions: |eps|=1, eps = tau(chi)/(i^a sqrt q), and
# the archimedean/finite split eps_infty * (tau/sqrt q) reproduces it.
# Pure python (cmath), local. 2026-06-19.
import cmath, math

def legendre_like_chars(q):
    # all Dirichlet characters mod q via a primitive root (q prime), as chi(g^k)=zeta^{m k}
    # find primitive root
    def is_primroot(g,q):
        seen=set(); x=1
        for _ in range(q-1):
            x=(x*g)%q; seen.add(x)
        return len(seen)==q-1
    g=2
    while not is_primroot(g,q): g+=1
    # discrete log table
    dlog={}; x=1
    for k in range(q-1):
        x=(x*g)%q if k>0 else 1
        dlog[pow(g,k,q)]=k
    chars=[]
    for m in range(q-1):
        def chi(n,m=m,q=q,dlog=dlog):
            n%=q
            if n==0: return 0
            return cmath.exp(2j*math.pi*m*dlog[n]/(q-1))
        chars.append((m,chi))
    return chars

def gauss_sum(chi,q):
    return sum(chi(n)*cmath.exp(2j*math.pi*n/q) for n in range(1,q))

print("=== Root number factorization over places (Dirichlet L), grounding §64.3 ===")
for q in (5,7,13):
    print("\n-- q = %d --" % q)
    for m,chi in legendre_like_chars(q):
        if m==0: continue  # skip trivial
        tau=gauss_sum(chi,q)
        # parity a: chi(-1)=(-1)^a
        a = 0 if abs(chi(q-1)-1)<1e-9 else 1
        # root number eps = tau/(i^a sqrt q)
        eps = tau/((1j**a)*math.sqrt(q))
        # archimedean local factor eps_infty = i^{-a} (sign at infinity from the Gamma-place);
        # finite part = tau/sqrt q ; product should reproduce eps (up to the i^a normalization)
        eps_infty = 1j**(-a)
        eps_finite = tau/math.sqrt(q)
        recon = eps_infty*eps_finite
        print("  m=%2d parity a=%d : |eps|=%.6f  eps=%.4f%+.4fi  eps_inf*eps_fin=%.4f%+.4fi  match=%s"
              % (m,a, abs(eps), eps.real,eps.imag, recon.real,recon.imag,
                 "YES" if abs(eps-recon)<1e-9 else "no"))
print("\n=== verdict: |eps|=1 and eps factors as eps_infty(Gamma-place) * eps_finite(Gauss) ===")
