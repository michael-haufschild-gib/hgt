import mpmath as mp
mp.mp.dps = 35

# P_1 special (regularized); P_j (j>=2) = 1 - (-1)^j zeta(j)/2^j - a_{j-1}
gammaE = mp.euler
P1 = 1 + gammaE/2 - mp.log(4*mp.pi)/2
f = lambda s: mp.zeta(s,1,1)/mp.zeta(s)
a = mp.taylor(f, 0, 12)   # a[0..12], a[j]=[s^j](zeta'/zeta)

def P(j):
    if j == 1: return P1
    return 1 - ((-1)**j)*mp.zeta(j)/mp.mpf(2)**j - a[j-1]

def lam_moments(n):
    return sum(mp.binomial(n,j)*((-1)**(j+1))*P(j) for j in range(1,n+1))

def lam_closed(n):
    # n*P1 + (1-n) + sum_{j=2}^n C(n,j) zeta(j)/2^j  -  sum_{j=2}^n C(n,j)(-1)^{j+1} a_{j-1}
    Z = sum(mp.binomial(n,j)*mp.zeta(j)/mp.mpf(2)**j for j in range(2,n+1))
    A = sum(mp.binomial(n,j)*((-1)**(j+1))*a[j-1] for j in range(2,n+1))
    return n*P1 + (1-n) + Z - A, Z, A

# known Li lambda_n (OEIS A074760): 0.0230957, 0.0923457, 0.2076389, 0.3687904, ...
known = {1:"0.02309570896612103", 2:"0.09234573522804667", 3:"0.20763892055432092",
         4:"0.36879040656451206", 5:"0.57448779424324413", 6:"0.82309327350768119"}
print(f"{'n':>2} | {'lam_moments':>20} | {'lam_closed':>20} | {'known lam_n':>20} | {'Z_n(arch+)':>12} {'A_n(prime)':>12}")
for n in range(1,9):
    lm = lam_moments(n)
    lc, Z, A = lam_closed(n)
    kn = known.get(n,"—")
    print(f"{n:>2} | {mp.nstr(lm,16):>20} | {mp.nstr(lc,16):>20} | {kn:>20} | {mp.nstr(Z,8):>12} {mp.nstr(A,8):>12}")
print()
print("Z_n (archimedean ζ-sum, all coeffs C(n,j)/2^j>0) vs A_n (prime-period a_j sum):")
print("RH face λ_n≥0  ⟺  the positive archimedean ζ-part + n*P1 + (1-n) dominates the prime-period A_n.")
