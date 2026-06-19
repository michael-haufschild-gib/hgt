# Weil positivity as a prime-lattice Schrodinger operator: kinetic-symbol certificate.
# Certifies D6 section 8: Q_W = -Delta_prime + V_arch, with kinetic term factoring over primes
# as sum_p J_p, each J_p multiplication by symbol f_p(theta) on the Bohr torus.
# Checks: (1) series == closed form; (2) f_p indefinite, sign change at cos(theta)=1/sqrt(p);
#         (3) mean-zero (traceless kinetic, since Lambda(1)=0).
# Draft: geometric-rosetta-function-field-continent.md, section 8.
# Run: runpod 157.157.221.29:39437, python3 (3.8.10), pure math. 2026-06-19.
import math

def f_series(p, theta, K=4000):
    s = 0.0
    for k in range(1, K):
        s += p**(-k/2.0) * math.cos(k*theta)
    return -2.0*math.log(p)*s

def f_closed(p, theta):
    a = math.sqrt(p)
    return -2.0*math.log(p)*(a*math.cos(theta)-1.0)/(p - 2.0*a*math.cos(theta) + 1.0)

def avg(p, N=200000):
    s=0.0
    for j in range(N):
        th = 2*math.pi*j/N
        s += f_closed(p, th)
    return s/N

print("=== kinetic symbol f_p(theta): series vs closed form (D6 8.2) ===")
print(" p   theta     f_series        f_closed        |diff|")
for p in (2,3,5,7):
    for th in (0.3, 1.0, 2.0, 3.0):
        fs=f_series(p,th); fc=f_closed(p,th)
        print(" %d  %.2f   %12.8f   %12.8f   %.2e" % (p,th,fs,fc,abs(fs-fc)))
print()
print("=== sign change at cos(theta)=1/sqrt(p)  (f_p>0 for cos<1/sqrt p, <0 above) ===")
for p in (2,3,5,7):
    thc = math.acos(1.0/math.sqrt(p))
    print(" p=%d: theta_c=%.4f  f(theta_c-0.1)=%+.4f  f(theta_c+0.1)=%+.4f  avg(f_p)=%+.6f"
          % (p, thc, f_closed(p,thc-0.1), f_closed(p,thc+0.1), avg(p)))
