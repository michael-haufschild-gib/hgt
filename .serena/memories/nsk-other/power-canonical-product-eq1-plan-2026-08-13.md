# power-canonical-product-exact-moment-borel-lattice-law — the single remaining item, eq. (1)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/power-canonical-product-exact-moment-borel-lattice-law.md`.
Sections 1–3 (equations (2)–(11)) are formalized end to end and axiom-clean; Section 4 is a
negative literature audit, not a theorem.  **The only unformalized statement is equation (1)**:

```
g(s) = ⌊1/s⌋,  E_g(w) = (1-w) exp(∑_{r=1}^g w^r/r),  W_s(z) = ∏_{n≥1} E_g(-z/n^s),
H_s(x) = x W_s'(x)/W_s(x)
H_s(x) = (π/s) csc(π/s) x^{1/s} + ∑_{j=1}^g (-1)^j ζ(sj) x^j - 1/2 + R_s(x),
R_s(x) ~ ∑_{k≥1} b_k x^{-k},   b_k = (-1)^k ζ(-sk)
```

## Corpus entry points (already proved — do not rebuild)
- `HTGeometry/WeierstrassFactorGenus.lean`: `weierstrassE g z = (1-z) exp(∑_{r<g+1} z^r/r)`,
  `hasDerivAt_weierstrassPoly`, `hasDerivAt_weierstrassE`,
  **`logDeriv_weierstrassE (g) (hz : z ≠ 1) : E_g'(z)/E_g(z) = -z^g/(1-z)`**,
  **`tsum_inverse_power_expansion (g) (ht : 1 < ‖t‖) : t^{g+1}/(1+t) = ∑_{j≥0} (-1)^j t^{g-j}`**.
- `HTGeometry/RationalPowerCyclicNorm.lean`: `powerCanonicalProduct a = canonicalProduct (powerGenus a) (powerZero a)`,
  `norm_powerZero`.
- The whole transform theory of (2)–(11) is in
  `RHTower/{AlternatingSineGeometricSum, ZetaRealBound, LambertQuadraticFactor,
  LambertSeriesConvergence, PowerLatticeLambertForm, PowerLatticeResidue,
  PowerLatticeRamification, LambertSumHolomorphic, LambertTailHolomorphic}.lean`.

## Mechanism to formalize
`logDeriv_weierstrassE` gives, with `t_n = x/n^s`,
`H_s(x) = ∑_{n≥1} (-1)^g t_n^{g+1}/(1 + t_n)`.
The Mellin transform of `φ(t) = (-1)^g t^{g+1}/(1+t)` is `(-1)^g π / sin(π(w+g+1))` on
`-(g+1) < Re w < -g`, so `M[H_s](w) = ζ(-sw)·M[φ](w)` on `-(g+1) < Re w < -1/s`
(nonempty because `1/s < g+1`).  Shifting the contour right past `w = -1/s` (pole of `ζ(-sw)`),
`w = -g,…,0` and then `w = 1,2,…` (poles of `π/sin`) produces the displayed expansion; the residue
at `w = k` is `(-1)^k ζ(-sk) x^{-k}`, which is `b_k`.
Alternative elementary route if Mellin contour shifting proves too costly: split the sum at
`n^s ≈ x`, use `tsum_inverse_power_expansion` on the finitely many `n` with `t_n > 1` and the
ascending geometric expansion on the rest, and control the two partial sums by Euler–Maclaurin —
this is where `ζ(-sk)` appears as the regularized value of `∑_n n^{sk}`.  MATHLIB CAPABILITY CHECKED 2026-08-13 (part 2): Euler's reflection formula IS available —
`Complex.Gamma_mul_Gamma_one_sub (z) : Gamma z * Gamma (1 - z) = π / sin (π * z)` in
`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`.  What is NOT there is the half-line Beta
integral `∫_0^∞ t^{w-1}/(1+t) dt = π / sin (π w)` for `0 < Re w < 1` (mathlib's `betaIntegral` is
on `[0,1]`), which is exactly the Mellin transform of the model function
`φ(t) = t^{g+1}/(1+t)` after shifting.  HALF OF THE REDUCTION IS NOW BUILT (2026-08-13):
`HTGeometry/BetaReflectionIntegral.lean` (wired, compiling, axiom-clean) proves
**`betaIntegral_self_one_sub (h0 : 0 < w.re) (h1 : w.re < 1) :
Complex.betaIntegral w (1 - w) = π / Complex.sin (π * w)`**.
So the ONLY step still missing for the half-line Beta integral is the change of variables
`t = x/(1-x)` turning `∫_0^∞ t^{w-1}/(1+t) dt` into `betaIntegral w (1-w)`.

EXACT REDUCTION (2026-08-13): under `t = x/(1-x)` (a diffeo `(0,1) → (0,∞)`, `dt = dx/(1-x)²`)
```
∫_0^∞ t^{w-1}/(1+t) dt = ∫_0^1 x^{w-1} (1-x)^{-w} dx = Complex.betaIntegral w (1-w)
```
and mathlib's `Complex.betaIntegral_eq_Gamma_mul_div (hu : 0 < u.re) (hv : 0 < v.re) :
betaIntegral u v = Γ u * Γ v / Γ (u + v)` with `u = w`, `v = 1 - w`, `Γ 1 = 1`, then
`Complex.Gamma_mul_Gamma_one_sub` finishes: `= π / sin (π w)`.
So the ONLY genuinely missing Lean step is the change of variables on `(0,∞)`; use
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` (injective-on-a-measurable-set form) with
`g x = x/(1-x)` on `Ioo 0 1`, `g' x = (1-x)⁻²`.  Everything after that is a rewrite chain.
Older note (substitution
`t = u/(1-u)` from the `[0,1]` Beta integral, plus `Gamma_mul_Gamma_one_sub`) is the first
concrete, self-contained Lean target for this card and is reusable.
MATHLIB CAPABILITY CHECKED 2026-08-13: `Mathlib/Analysis/MellinTransform.lean` has only ~30
results — the algebraic transformation rules (`mellin_cpow_smul`, `mellin_comp_rpow`,
`mellin_comp_mul_left/right`, `mellin_comp_inv`, `mellin_div_const`, `hasMellin_*`).  There is
**no contour-shift / residue machinery and no Mellin inversion with a moved abscissa**, so the
Mellin route would first require building strip-shift technology.  The elementary split route is
therefore the one to cost out first.  Euler–Maclaurin is NOT in mathlib either, so the regularized
`∑_n n^{sk} → ζ(-sk)` step must be built (mathlib does have `Mathlib/NumberTheory/AbelSummation.lean`
and the Hurwitz-zeta files, which are the natural substitutes).
Check first whether
mathlib's `Mathlib/Analysis/MellinTransform.lean` plus `Mathlib/NumberTheory/LSeries/*` already
supply enough; Euler–Maclaurin is NOT in mathlib.
