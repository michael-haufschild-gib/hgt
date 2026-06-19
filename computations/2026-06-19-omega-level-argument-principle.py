# Argument principle: (1/2pi i) oint d log det_zeta(N+a) = #zeros enclosed = #ground-state rungs.
# det_zeta(N+a) = sqrt(2pi)/Gamma(a); d log det = -psi(a) da. Residue of -psi at a=-n is +1 (simple).
# Verify by direct numerical contour integration around enclosing circles.
import mpmath as mp
mp.mp.dps = 30
def dlogdet(a):   # d/da log(sqrt(2pi)/Gamma(a)) = -psi(a)
    return -mp.digamma(a)
def winding(center, radius, enclosed_desc):
    f = lambda th: dlogdet(center + radius*mp.e**(1j*th)) * (1j*radius*mp.e**(1j*th))
    val = mp.quad(f, [0, mp.pi/2, mp.pi, 3*mp.pi/2, 2*mp.pi]) / (2j*mp.pi)
    print(f"  contour center={center} r={radius}: winding = {mp.nstr(val,8)}   (expect {enclosed_desc})")
print("Argument-principle zero-count of det_zeta(N+a)=sqrt(2pi)/Gamma(a):")
winding(mp.mpf('0'),   mp.mpf('0.4'), "1  [ground state a=0 only]")
winding(mp.mpf('-1'),  mp.mpf('0.4'), "1  [rung a=-1 only]")
winding(mp.mpf('-1'),  mp.mpf('1.6'), "3  [rungs a=0,-1,-2]")
winding(mp.mpf('0.5'), mp.mpf('0.3'), "0  [no rung enclosed]")
print("\nResidue check: psi(a) ~ -1/a near 0  => Res(-psi,0)=+1")
for n in [0,1,2]:
    a0 = mp.mpf(-n)
    res = mp.limit(lambda e: (a0+e+1e-12)*0+ (mp.mpf(1))*( ( -mp.digamma(a0+e) )*e ), 0) if False else None
print("psi near 0: a*psi(a) ->", mp.nstr((mp.mpf('1e-8'))*mp.digamma(mp.mpf('1e-8')),6), "(-> -1, simple pole res -1)")
