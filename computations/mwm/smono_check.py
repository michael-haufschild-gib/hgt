#!/usr/bin/env python3
"""Attack on #138 (S-mono / outer single crossing), two decisive tests:
 (I) lattice (S-mono): constant-delta semi-infinite lattice, check S_i=d+W(t*_i)
     increasing in the outer range (doc 29 claim).
 (II) genuine SPUR-R target: Z_c(J^d_{Pg})=2 on a one-sided-far LP x pair carrier
     across a wide d-sweep + (a,b) grid; a single Z_c>2 refutes (S-mono)/SPUR-R."""
import numpy as np
from mpmath import mp, mpf, coth, csch, findroot
mp.dps = 30

# ---------- (I) lattice (S-mono) ----------
def lattice_S(d, delta):
    tk = [mpf(k)*delta for k in range(1, d+1)]
    def sigchi(t):
        return sum(coth((t-tj)/2) for tj in tk)
    def W(t):
        return mpf('0.25')*sum(csch((t-tj)/2)**2 for tj in tk)
    S=[]
    for i in range(1, d):  # gap between t_i and t_{i+1}
        lo, hi = tk[i-1], tk[i]
        # solve sigchi(t) = -d in (lo,hi)
        mid=(lo+hi)/2
        try:
            ts=findroot(lambda t: sigchi(t)+d, mid)
            if lo< ts <hi:
                S.append((i, float(ts), float(d+W(ts))))
        except Exception:
            pass
    return S

print("=== (I) lattice (S-mono): is S_i increasing in the outer range? ===")
for d,delta in [(20,mpf('0.3')),(30,mpf('0.2')),(40,mpf('0.15'))]:
    S=lattice_S(d,delta)
    # outer range i>=d/2
    outer=[s for s in S if s[0]>=d//2]
    diffs=[outer[k+1][2]-outer[k][2] for k in range(len(outer)-1)]
    viol=sum(1 for dd in diffs if dd<=0)
    print(f"d={d} delta={float(delta)}: {len(outer)} outer gaps, "
          f"S-increasing violations={viol}/{len(diffs)}  "
          f"min dS={min(diffs) if diffs else float('nan'):.3e}")

# ---------- (II) genuine Z_c on section carriers ----------
def apply_D_minus(p, c):
    dp=np.polyder(p); L=max(len(dp),len(p))
    dp=np.concatenate([np.zeros(L-len(dp)),dp]); pp=np.concatenate([np.zeros(L-len(p)),p])
    return dp-c*pp
def jensen_section(cj, d):
    # J^d_g(x) = sum_j d!/(d-j)! c_j x^j ; cj = maclaurin coeffs list (low->high)
    from math import factorial
    coeffs=[factorial(d)//factorial(d-j)*cj[j] if j<=d and j<len(cj) else 0 for j in range(min(d,len(cj)-1)+1)]
    # numpy wants high->low
    return np.array(coeffs[::-1], dtype=float)
def zc(p):
    r=np.roots(p); return int(np.sum(np.abs(r.imag)>1e-6))

# one-sided-far LP carrier g with zeros at negative reals (g(x)=prod(1+x/n)) truncated
# Maclaurin coeffs of prod_{n=1}^{K}(1+x/n): elementary symmetric of {1/n}
def one_sided_g_coeffs(K):
    roots=[-1.0*n for n in range(1,K+1)]  # zeros at -1..-K (one-sided: all negative)
    p=np.poly(roots)  # high->low, of the polynomial with those roots (this is g truncated)
    # maclaurin coeffs low->high = reverse, normalized so g(0)=1
    c=p[::-1]; c=c/c[0]
    return list(c)
print("\n=== (II) genuine Z_c(J^d_{Pg}) on one-sided-far carrier; want ==2 ===")
cj=one_sided_g_coeffs(12)
worst=0
for a,b in [(0.0,1.0),(0.5,1.0),(2.0,0.8),(-1.5,1.3),(0.0,0.3),(3.0,0.5)]:
    tau=complex(a,b)
    line=[]
    for d in [6,10,15,20,30,40,60]:
        Ad=jensen_section(cj,d)
        # P*g section via three-term: J^d_{Pg}=|tau|^2 A_d -2 a d x A_{d-1}+d(d-1)x^2 A_{d-2}
        Ad1=jensen_section(cj,d-1); Ad2=jensen_section(cj,d-2)
        # build polynomials aligned; multiply by x, x^2
        def padmul(p,shift,scale):
            q=np.concatenate([p*scale, np.zeros(shift)])  # multiply by x^shift (high->low append zeros)
            return q
        t1=(a*a+b*b)*Ad
        t2=-2*a*d*padmul(Ad1,1,1.0)
        t3=d*(d-1)*padmul(Ad2,2,1.0)
        L=max(len(t1),len(t2),len(t3))
        def padL(p): return np.concatenate([np.zeros(L-len(p)),p])
        J=padL(t1)+padL(t2)+padL(t3)
        z=zc(J); line.append(z); worst=max(worst,z)
    print(f"(a,b)=({a},{b}): Z_c over d={[6,10,15,20,30,40,60]} -> {line}")
print(f"\nWORST Z_c over all tested = {worst}  ({'REFUTES (spurious pair!)' if worst>2 else 'consistent with SPUR-R target Z_c<=2'})")
