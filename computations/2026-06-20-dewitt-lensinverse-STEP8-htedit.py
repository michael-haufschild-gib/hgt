#!/usr/bin/env python3
# MACHINE STEP8: minimal not-HT-blind edit of the lens-inverse NODE test.
# NODE test computed Sum 1/f'(x_i) over preimages of w (residue value-relation; =0 for a polynomial map).
# Minimal edit: swap the polynomial map -> the HT function ZETA, with w=0 so preimages = nontrivial zeros rho.
# NOT HT-blind: Sum 1/zeta'(rho) depends on zeta's actual zero structure. Test the value relation.
# Control: a degree-D polynomial (Sum 1/p' over roots = 0 exactly) confirms the test logic.
import numpy as np
import mpmath as mp
mp.mp.dps = 30

# --- control: polynomial residue sum (should be ~0 for deg>=2) ---
rng = np.random.default_rng(3)
c = rng.normal(size=7); c[0]=1.0
roots = np.roots(c)
dp = np.polyval(np.polyder(c), roots)
print("control polynomial deg6: Sum 1/p'(root) =", f"{np.sum(1.0/dp):.3e}", "(expect ~0)")

# --- HT edit: f = zeta, w=0, preimages = nontrivial zeros rho = 1/2 + i*gamma_k ---
K = 40
print(f"\n=== Sum 1/zeta'(rho) over first {K} zero-PAIRS (rho, conj rho) ; partial sums ===")
print("  k | gamma_k        | 2*Re(1/zeta'(rho_k))      | running partial sum")
partial = mp.mpf(0)
vals=[]
for k in range(1, K+1):
    rho = mp.mpc(0.5, mp.im(mp.zetazero(k)))
    zp = mp.zeta(rho, derivative=1)
    term = 2*mp.re(1/zp)                 # rho and conj(rho) together -> real
    partial += term
    vals.append(float(term))
    if k<=10 or k%5==0:
        print(f"  {k:2d} | {float(mp.im(rho)):13.6f} | {float(term):+.6e}      | {float(partial):+.6e}")
print(f"\n  partial sum after {K} pairs: {float(partial):+.6e}")
print(f"  term magnitude trend (|term_k|): first={abs(vals[0]):.2e}  last={abs(vals[-1]):.2e}")
# does it converge? look at tail-average drift
tail = vals[-10:]
print(f"  last-10 terms mean={np.mean(tail):+.3e} std={np.std(tail):.3e}  (converging if terms ->0)")
print("\nREAD: compare to control (=0). Does Sum 1/zeta'(rho) -> a clean value, 0, or diverge?")
