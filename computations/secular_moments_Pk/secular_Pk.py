import mpmath as mp
mp.mp.dps = 40

# Critic's formula (foundations §19):  P_k = 1 - (-1)^k zeta(k)/2^k - a_{k-1},
#   a_j = [s^j] (zeta'/zeta)(s)  (Taylor at s=0),   P_k = sum over nontrivial zeros rho of rho^{-k}.
# Validate numerically for k=2..6 against the direct zero-sum.

N = 2000
print("computing %d zeta zeros (dps=40)..." % N)
gam = [mp.zetazero(n).imag for n in range(1, N+1)]   # ordinates, zeros at 1/2 + i*gam (and conjugate)

def Pk_zerosum(k):
    # sum over rho and rho-bar: (1/2+i g)^{-k} + (1/2-i g)^{-k} = 2 Re((1/2+i g)^{-k})
    s = mp.mpf(0)
    for g in gam:
        rho = mp.mpf(1)/2 + 1j*g
        s += 2*(rho**(-k)).real
    return s

# Taylor coeffs of zeta'/zeta at 0
f = lambda s: mp.zeta(s, 1, 1)/mp.zeta(s)
a = mp.taylor(f, 0, 7)   # a[0..7]

print("a_0 (=zeta'/zeta(0)) =", mp.nstr(a[0], 15), " (should be log(2pi)=%s)" % mp.nstr(mp.log(2*mp.pi),15))
print()
print(f"{'k':>2} | {'P_k zero-sum (N=2000)':>26} | {'P_k formula':>26} | {'|diff|':>10}")
for k in range(2, 7):
    pk_num = Pk_zerosum(k)
    pk_for = 1 - ((-1)**k)*mp.zeta(k)/mp.mpf(2)**k - a[k-1]
    print(f"{k:>2} | {mp.nstr(pk_num,18):>26} | {mp.nstr(pk_for,18):>26} | {mp.nstr(abs(pk_num-pk_for),3):>10}")
print()
# the odd-zeta content explicitly
print("odd-k moments carry zeta(odd):")
for k in [3,5]:
    print("  P_%d = 1 - zeta(%d)/2^%d... -a_%d ; zeta(%d)=%s" % (k,k,k,k-1,k,mp.nstr(mp.zeta(k),12)))
