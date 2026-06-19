# Archimedean potential symbol of H_W = -Delta_prime + V_arch (D6 8.4).
# V_arch is Toeplitz convolution with Bohr-side symbol
#   Omega(r) = Re psi(1/4 + i r/2) - log(pi)  =  log(r/2pi) + o(1)   (digamma asymptotic).
# Certifies: Omega ~ log(r/2pi) to high precision; well (Omega<0) for r<2pi, +log growth for r>2pi.
# Compares to the (also unbounded) separable prime kinetic Sum_p f_p(theta).
# Draft: geometric-rosetta-function-field-continent.md, section 8.4.
# Run: runpod 157.157.221.29:39437, python3.13 + mpmath 1.4.1. 2026-06-19.
import mpmath as mp
mp.mp.dps = 30

def omega(r):
    return mp.re(mp.digamma(mp.mpf(1)/4 + 1j*mp.mpf(r)/2)) - mp.log(mp.pi)

print("=== archimedean potential symbol Omega(r) = Re psi(1/4+ir/2) - log pi (D6 8.4) ===")
print("   r        Omega(r)        log(r/2pi)      Omega-log(r/2pi)")
for r in [0.5,1,2,5,10,20,50,100,300,1000]:
    o = omega(r); a = mp.log(mp.mpf(r)/(2*mp.pi))
    print("  %7.1f   %+12.6f   %+12.6f   %+12.6f" % (r, float(o), float(a), float(o-a)))

print()
print("  Omega(1)=%+.5f  Omega(2pi)=%+.5f  Omega(20)=%+.5f" % (float(omega(1)), float(omega(2*mp.pi)), float(omega(20))))

import math
def f_closed(p, th):
    a=math.sqrt(p); return -2.0*math.log(p)*(a*math.cos(th)-1.0)/(p-2.0*a*math.cos(th)+1.0)
def primes(N):
    s=[True]*(N+1); s[0]=s[1]=False
    for i in range(2,int(N**0.5)+1):
        if s[i]:
            for j in range(i*i,N+1,i): s[j]=False
    return [i for i in range(2,N+1) if s[i]]
ps=primes(2000)
tot0=sum(f_closed(p,0.0) for p in ps); totpi=sum(f_closed(p,math.pi) for p in ps)
print()
print("kinetic wing Sum_p f_p(theta) over primes<2000:  theta=0: %.4f   theta=pi: %.4f  (both unbounded in p)" % (tot0, totpi))
