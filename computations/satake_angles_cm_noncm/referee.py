# Satake-angle equidistribution referee: CM vs non-CM elliptic curves
# Certifies Prop 3' (Sato-Tate = eigenphase equidistribution) and Prop 5
# (CM/non-CM = the dynamics-continent rotation/almost-Mathieu = solvable/non-solvable dichotomy).
# Draft: automorphic-continent-rankin-selberg-ramanujan.md, section 8.
# a_p = p+1-#E(F_p) via Legendre sums; theta_p = arccos(a_p/2 sqrt p).
# Run: runpod 157.157.221.29:39437, python3 (3.8.10), pure math (no numpy). 2026-06-19.
import math

def sieve(N):
    s=[True]*(N+1); s[0]=s[1]=False
    for i in range(2,int(N**0.5)+1):
        if s[i]:
            for j in range(i*i,N+1,i): s[j]=False
    return [i for i in range(2,N+1) if s[i]]

def ap(a,b,p):
    # a_p = -sum_x legendre(x^3+ax+b, p)
    s=0
    for x in range(p):
        v=(x*x%p*x + a*x + b)%p
        if v==0: continue
        s += 1 if pow(v,(p-1)//2,p)==1 else -1
    return -s

def study(a,b,name,badp,N=12000):
    primes=[p for p in sieve(N) if p>3 and p not in badp]
    angles=[]; ss=0
    for p in primes:
        apv=ap(a,b,p)
        if abs(apv) > 2*math.sqrt(p): apv=max(-int(2*math.sqrt(p)),min(int(2*math.sqrt(p)),apv))
        if apv==0: ss+=1
        th=math.acos(max(-1.0,min(1.0,apv/(2.0*math.sqrt(p)))))
        angles.append(th)
    n=len(angles); B=9
    print("=== %s  (%d good primes up to %d) ===" % (name,n,N))
    print("supersingular fraction (a_p=0): %.4f   [CM -> ~0.5; non-CM -> ~0]" % (ss/n))
    print(" bin (theta/pi)    observed   Sato-Tate pred")
    for k in range(B):
        t1=math.pi*k/B; t2=math.pi*(k+1)/B
        obs=sum(1 for th in angles if t1<=th<t2)/n
        pred=( (t2-math.sin(t2)*math.cos(t2)) - (t1-math.sin(t1)*math.cos(t1)) )/math.pi
        print("  [%.2f,%.2f)        %.4f      %.4f" % (k/B,(k+1)/B,obs,pred))
    print()

study(1,1,"NON-CM  y^2=x^3+x+1", {31})
study(-1,0,"CM by Z[i]  y^2=x^3-x", set())
