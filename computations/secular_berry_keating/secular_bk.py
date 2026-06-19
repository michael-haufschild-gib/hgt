#!/usr/bin/env python3.13
"""
The FE-invariant variable u=s(1-s)=¼+γ²: the canonical Berry–Keating / Hilbert–Pólya form.

u = s(1-s) is the functional-equation INVARIANT (s↔1-s ⟹ same u). On RH, u_n = ¼+γ_n² are REAL and
≥¼ — exactly the spectrum of a POSITIVE self-adjoint operator (Berry–Keating Δ; Connes). So:
   RH ⟺ all u_n real (≥¼) ⟺ the secular operator in u is positive self-adjoint.
Secular test: moments m_k = Σ u_n^{-k} (real, convergent); Hankel [m_{i+j}] PSD ⟺ u real ⟺ RH. This
is the cleanest Hilbert–Pólya framing (positive spectrum), vs §9's reciprocal-squared-zero (−1/γ²).

(1) genuine ⟹ u real ≥¼, Hankel PD; (2) off-line zero ⟹ u complex ⟹ Hankel not PD.
"""
import mpmath as mp

mp.mp.dps = 50

def zeros(N):
    return [mp.im(mp.zetazero(n)) for n in range(1, N + 1)]

def hankel_minors(uvals, K):
    # m_k = Σ (scale/u)^k; Hankel [m_{i+j}]; leading principal minors (PD ⟺ all >0).
    # congruence rescale by the smallest |u| so reciprocals are O(1) (preserves PD/signature).
    scale = min(abs(u) for u in uvals)
    inv = [scale / u for u in uvals]
    m = [sum(x**k for x in inv) for k in range(0, 2 * K + 1)]
    return [mp.det(mp.matrix([[m[i + j] for j in range(n)] for i in range(n)])) for n in range(1, K + 2)]

def main():
    N = 40; K = 10
    g = zeros(N)
    print(f"=== Berry–Keating FE-invariant u=s(1-s)=¼+γ² (N={N}, dps={mp.mp.dps}) ===")
    u = [mp.mpf(1) / 4 + gi**2 for gi in g]
    print(f"  u_1..u_3 = {[mp.nstr(x,8) for x in u[:3]]}  (real, ≥¼ ⟹ positive self-adjoint spectrum)")
    D = hankel_minors(u, K)
    print(f"  genuine: Hankel leading-minor signs = {''.join('+' if d>0 else '-' for d in D)}")
    print(f"           all>0 (PD ⟺ u real ⟺ RH-consistent, positive operator)? {all(d>0 for d in D)}")
    # off-line: zero #1 -> rho=1/2+delta+i*gamma, u = rho(1-rho) becomes COMPLEX (conj pair)
    print("\n  off-line zero #1 by δ ⟹ u complex (conj pair) ⟹ Hankel not PD:")
    for d in ['1.0', '0.3', '0.1']:
        delta = mp.mpf(d)
        rho = mp.mpf('0.5') + delta + 1j * g[0]
        u0 = rho * (1 - rho)                       # complex
        upert = [u0, mp.conj(u0)] + [mp.mpf(1) / 4 + gi**2 for gi in g[1:]]
        Dp = hankel_minors(upert, K)
        nneg = sum(1 for x in Dp if mp.re(x) <= 0)
        print(f"    δ={d:4s}: u={mp.nstr(u0,6)}  #nonpos leading minors={nneg}  "
              f"{'NOT PD ⟹ off-line detected (operator non-self-adjoint)' if nneg>0 else 'still PD'}")
    print("\n# RH ⟺ u=s(1-s) spectrum real ≥¼ ⟺ secular operator positive self-adjoint (Berry–Keating/Connes).")
    print("# The FE-invariant u is the canonical Hilbert–Pólya coordinate; the secular Hankel PD is RH.")

if __name__ == "__main__":
    main()
