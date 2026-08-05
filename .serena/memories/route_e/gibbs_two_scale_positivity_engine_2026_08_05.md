# Cycle 8: the two-scale positivity engine + volume audit (2026-08-05)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-8 section).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsTwoScalePositivity.lean`, wired, built,
no sorry, axioms clean.

## U1 — the reduction (THE new engine)
`TwoScalePositive S x y := ∀ z, 0 ≤ z.re → 0 < (P_S(z,x) * conj P_S(z,y)).re`.
If P_{S∪p}(z,x) = 0 with Re z ≥ 0 then A = −zB so A·conj B = −z·normSq B, real part
−z.re·normSq B ≤ 0. Hence **TSP_S(x, px) ⟹ P_{S∪p} has no zero with Re z ≥ 0**.
=> ALL-k sector stability reduces to positivity of an explicit real quadratic form
   Σ_{j,l} B_{j,l} r^{j+l} cos((j−l)θ),  B_{j,l} = Σ_{|T|=j,|U|=l} e^{−x(e(T)+p·e(U))}.
Terms |j−l| ≤ 1 are automatically ≥ 0; the content is that they dominate. At x=0 the form
IS |1+z|^{2k}; as x→∞ it → 1. Proven in Lean at levels 0 and 1 (all scales) and at every
level in the weak-coupling regime xσ+yσ+xσyσ < 1.

**ORDERING INSIGHT**: the k=2 boundary case needs p ≤ q, so the induction must adjoin
primes in DECREASING order (new prime smaller than all present). Structural constraint on
the ladder, invisible before U1.

## U2 — honest volume audit (LIMITATION)
All stability thresholds are x ≲ 1/m. The infinite-volume gas at coupling x involves all
primes p ≲ 1/x, so its m = e^{θ(1/x)} and x·σ(m) ≫ 1 ALWAYS. **The finite-volume
stability theorems do NOT reach the infinite-volume regime** (V3 covers only
S = {p ≤ log(1/x)}). Do not overstate their reach.

## U3 — dictionary (labelled re-encoding, guidance only)
Selberg–Delange: D_z(s) = ∏(1+zp^{−s}) = ζ(s)^z G(z,s) ⟹
p_x(z) ~ x^{−1}(log 1/x)^{z−1}G(z,1)/Γ(z). Zeros of the infinite gas approach
{−1,−2,…} ∪ {−p} as x→0 (all real negative). Near −1: G(−1,1) = 1, 1/Γ(z) ≈ −(z+1), so
  dist(nearest gas zero, −1) ≈ |Φ(x)|·x·(log 1/x)².
RH ⟺ that distance ≪ x^{1/2−ε}(log)²: the distinguished gas zero traces the zeta zeros
(almost-periodic in log(1/x), frequencies γ, amplitude x^{1/2} iff RH).
Also: Erdős–Kac profile (c_j Poisson, mean loglog(1/x)) gives only (log 1/x)^{−2}
cancellation vs x^{1/2} needed — quantifies how much of (G2) is beyond the smooth profile.

## Lean traps
- `|>.re` doesn't parse in a theorem statement — parenthesise the product.
- `simp [Complex.mul_re]` turns `↑(rexp t)` into `Complex.exp ↑t`; use
  `simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]` then `ring`.
- `-‖w‖ ≤ w.re` : `Complex.re_le_norm (-w)` + `Complex.neg_re` + `norm_neg`.
- Big products: never nlinarith the whole thing; build e1/e2/e3 bounds by calc then
  a single `linarith`.
