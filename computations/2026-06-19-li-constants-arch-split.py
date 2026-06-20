import mpmath as mp
mp.mp.dps = 40
lp = mp.log(mp.pi)
# Clean split of log xi at s=1 (pole/zero grouped):
#   log xi_inf(s) = log(1/2) + log s - (s/2) log pi + loggamma(s/2)        [archimedean, regular at 1]
#   log xi_ari(s) = log( (s-1) zeta(s) )                                    [arithmetic, regular at 1, ->log1=0]
def Ginf(s): return mp.log(mp.mpf(1)/2) + mp.log(s) - (s/2)*lp + mp.loggamma(s/2)
def Gari(s): return mp.log((s-1)*mp.zeta(s))
# lambda_n = n * [ (s-1)^n ] ( s^{n-1} G(s) )   (Coffey/Bombieri-Lagarias representation)
def li_part(G, n):
    c = mp.taylor(lambda s: s**(n-1)*G(s), 1, n, method='quad', radius=mp.mpf('0.25'))
    return n*c[n]
print(" n   lambda_n^inf      lambda_n^ari      lambda_n(sum)   known lambda_n")
known={1:'0.0230957',2:'0.0923457',3:'0.2076389',4:'0.3689760',5:'0.5751304',6:'0.8237436'}
for n in range(1,7):
    li = li_part(Ginf,n); la = li_part(Gari,n); tot=li+la
    print(f"{n:2d}   {mp.nstr(li,9):>13}   {mp.nstr(la,9):>13}   {mp.nstr(tot,9):>12}   {known.get(n,'?')}")
# Asymptotic check: lambda_n^inf ~ (n/2)(log n + gamma - 1 - log(2pi)) ?
print("\n asymptotic lambda_n^inf vs (n/2)(log n + gamma - 1 - log(2pi)):")
for n in [4,6,8,10,20]:
    li = li_part(Ginf,n)
    asy = (mp.mpf(n)/2)*(mp.log(n)+mp.euler-1-mp.log(2*mp.pi))
    print(f"  n={n:3d}: lambda_n^inf={mp.nstr(li,8):>11}  (n/2)(log n+gamma-1-log2pi)={mp.nstr(asy,8):>11}  ratio={mp.nstr(li/asy,6)}")
