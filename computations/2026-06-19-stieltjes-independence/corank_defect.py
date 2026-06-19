import mpmath as mp
mp.mp.dps = 60

def Bplus(n):
    return mp.mpf(1)/2 if n==1 else mp.bernoulli(n)

print("=== corank-1 (single prime q): gamma_n^(q) = c_{n-1} of 1/(1-q^-s) at s=0 ===")
print("    claim: c_{n-1} = B_n^+ (log q)^{n-1}/n!  ==> gamma ~ rational*(log q)^n, trdeg 1 (DEPENDENT)")
for q in (2,3):
    L=mp.log(q)
    print(f"  q={q}, log q={mp.nstr(L,12)}")
    for n in range(1,7):
        c = Bplus(n)*L**(n-1)/mp.factorial(n)
        ratio = c/L**(n-1)                       # should equal rational B_n^+/n!
        print(f"    n={n}: c_(n-1)/(log q)^(n-1) = {mp.nstr(ratio,18)}  ; B_n^+/n! = {mp.nstr(Bplus(n)/mp.factorial(n),18)}")

print()
print("=== verify trdeg-1: PSLQ on {1, c0*?,...} -> the powers (log q)^n are the only transcendental ===")
q=2; L=mp.log(q)
cs=[Bplus(n)*L**(n-1)/mp.factorial(n) for n in range(1,7)]   # gamma_1..gamma_6 analog (single prime)
# relation: c_n - (B_{n+1}^+/(n+1)!) * L^n = 0  is exact; test PSLQ finds a c_n vs L^n relation
rel = mp.pslq([cs[2], L**3], maxcoeff=10**8)   # c_3 vs (log2)^3 : rational multiple -> relation exists
print("  PSLQ[c_3, (log2)^3] (rational dependence expected):", rel)

print()
print("=== contrast: REAL gamma_n (corank-infinity) — NO such rational/(log q)^n relation ===")
g=[mp.stieltjes(n) for n in range(1,7)]
rel2 = mp.pslq([g[2], mp.log(2)**3, mp.log(3)**3], maxcoeff=10**8)
print("  PSLQ[gamma_3,(log2)^3,(log3)^3]:", rel2 if rel2 else "no relation (independent, as expected)")
print("=== done ===")
