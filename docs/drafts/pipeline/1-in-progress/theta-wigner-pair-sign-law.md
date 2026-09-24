# Theta Wigner pair sign law and the Helmholtz form of the pair kernel

- **ID:** theta-wigner-pair-sign-law
- **Stage:** 3-formalized (the stated theorems; the RH-blindness corollary is paper-level)
- **Type:** THEOREM (Lean)
- **Statement:** The exponentially weighted center integral of an ordered theta-cusp source pair
  has a closed form `n^{-σ} m^{-σ} · G_σ(2t + log n − log m)`, the kernel `G_σ` is
  `((σ−1)^2 − d^2/dy^2)` applied to `(cosh y)^{−(σ+2)}` up to a positive constant, and `G_σ(y) > 0`
  exactly for `cosh y < √((σ+2)(σ+3)/(6σ+3))`.

## Goal

The Hedenmalm center-mixed current is positive-definite for all admissible weights iff RH.  The
corpus already had the product/ratio separation of a source pair
(`thetaCuspSourceTerm_mul_reflect_eq_wignerRadialProfile`) but no evaluation of the center
integral, and one negativity witness at radial scale `c = 3`
(`thetaCuspWignerRadialTransform_three_zero_re_neg`).  This card evaluates the center integral
exactly and reads off where the pair current is positive and where it is negative.

## What is proved (Lean, axioms `propext`, `Classical.choice`, `Quot.sound` only)

Module `GaloisForLFunctions/RHTower/ThetaCuspWignerPairSignLaw.lean`:

1. `integral_rpow_mul_thetaCuspWignerRadialProfile` — for `σ > 0`,
   `∫_{(0,∞)} s^{σ−1} R(s,v) ds = Γ(σ+2)(1/cosh 2v)^{σ+2} Q(σ, cosh 2v)`,
   `Q(σ,C) = (σ+2)(σ+3)/C² − 6(σ+2) + 9`.
2. `thetaCuspWignerCriticalCosh σ = √((σ+2)(σ+3)/(6σ+3))`, with
   `one_lt_thetaCuspWignerCriticalCosh : 0 ≤ σ → 1 < thetaCuspWignerCriticalCosh σ`
   (equivalently `σ² − σ + 3 > 0`, which has negative discriminant).
3. `thetaCuspWignerRadialQ_pos_iff` / `_neg_iff` — exact sign threshold in `C`.
4. `integral_Ioi_rpow_mul_eq_exp_chart` — the exponential chart
   `∫_{(0,∞)} z^{σ−1} F z dz = 2 P^σ ∫_ℝ e^{2σu} F(P e^{2u}) du` for `P > 0`.
5. `integral_exp_mul_thetaCuspSourceTerm_pair` — for `σ > 0`, `n, m ≥ 1`,
   `∫_ℝ e^{(2σ−1)u} Φ_n(u+t) Φ_m(u−t) du
      = Γ(σ+2)/(2 (2πnm)^σ) · (1/cosh w)^{σ+2} Q(σ, cosh w)`, `w = 2t + log n − log m`.
6. `integral_exp_mul_thetaCuspSourceTerm_pair_factor` — the same quantity equals
   `n^{−σ} m^{−σ} · thetaCuspWignerPairKernel σ w`: the indices enter only through the Dirichlet
   weight and the hyperbolic separation.
7. `integral_exp_mul_thetaCuspSourceTerm_pair_pos_iff` / `_neg_iff` / `_center_pos` — the pair
   current is strictly positive iff `cosh w < thetaCuspWignerCriticalCosh σ`, strictly negative
   iff above, and always strictly positive at the pair's own center `2t = log m − log n`.

Module `GaloisForLFunctions/RHTower/ThetaCuspWignerPairHelmholtzForm.lean`:

8. `thetaCuspWignerPairKernel_eq_shifted_second_deriv` —
   `G_σ(y) = (2π)^{−σ}Γ(σ+2)/2 · ((σ−1)² f(y) − f''(y))` with `f(y) = (cosh y)^{−(σ+2)}`,
   supported by `hasDerivAt_thetaCuspWignerCoshPower` and
   `hasDerivAt_deriv_thetaCuspWignerCoshPower` (`f'' = (σ+2)² f − (σ+2)(σ+3)(cosh)^{−(σ+4)}`).
   The shift constant is `(σ+2)² − (6σ+3) = (σ−1)²`, a perfect square.

Module `GaloisForLFunctions/RHTower/ThetaCuspWignerPairSpectrum.lean`:

9. `integral_thetaCuspWignerPairKernel_mul_fourier` — for `σ > 0` and every real `ξ`,
   `∫_ℝ G_σ(y) e^{−iξy} dy = π^{−σ} |(s−1) Γ((s+2)/2)|²` at `s = σ+iξ`, an explicit *real*
   quantity (`thetaCuspWignerPairSpectrum`).  Proved from
   `HTGeometry.integral_cosh_rpow_neg_mul_exp_eq_ofReal` applied at exponents `σ+4` and `σ+2`,
   together with `Γ((σ+4+iξ)/2) = ((σ+2+iξ)/2) Γ((σ+2+iξ)/2)`, which makes the two Beta values
   share `|Γ((σ+2+iξ)/2)|²` and leaves the scalar `(σ+2)² + ξ² − (6σ+3) = ξ² + (σ−1)²`.
10. `thetaCuspWignerPairSpectrum_nonneg`, `_pos` (strict off `s = 1`), `_eq_normSq`.

So the universal pair kernel is a **positive-definite function of the hyperbolic separation for
every positive Mellin exponent**, with no arithmetic input, degenerating only at `s = 1`.

Module `GaloisForLFunctions/RHTower/LogWeightedEulerIntegral.lean`:

11. `integrableOn_rpow_mul_log_mul_exp_neg_Ioi`, `integral_rpow_mul_log_mul_exp_neg_Ioi` —
    `∫₀^∞ s^{σ−1}(log s)e^{−s} ds = Γ'(σ)` for every `σ > 0`, generalising the corpus's `σ = 1`
    case `HTGeometry.integral_log_mul_exp_neg_Ioi = −γ`.  Transferred from
    `Complex.hasDerivAt_GammaIntegral` and `Complex.integrableOn_gammaIntegral_log_kernel`.
12. `integral_rpow_mul_log_mul_exp_neg_mul_Ioi` — the rate law
    `∫₀^∞ s^{σ−1}(log s)e^{−Cs} ds = C^{−σ}(Γ'(σ) − Γ(σ) log C)`, by the dilation
    `integral_comp_mul_left_Ioi`; no differentiation under the integral.

Module `GaloisForLFunctions/RHTower/ThetaCuspWignerPairLogScaleWeight.lean`:

13. `thetaCuspWignerRadialLogWeight σ C = (Γ'(σ+4) − Γ(σ+4)log C)/C² − 6(Γ'(σ+3) − Γ(σ+3)log C)
    + 9(Γ'(σ+2) − Γ(σ+2)log C)`, with
    `integral_rpow_mul_log_mul_thetaCuspWignerRadialProfile` the corresponding exact transform and
    `integrableOn_rpow_mul_log_mul_exp_neg_mul_Ioi` the general-rate integrability.
14. `integral_log_scale_mul_exp_mul_thetaCuspSourceTerm_pair` — weighting by
    `log (thetaCuspWignerAtomScale n m u) = log(2πnm e^{2u})` gives
    `(2(2πnm)^σ)^{-1}(1/cosh w)^{σ+2} · thetaCuspWignerRadialLogWeight σ (cosh w)`.

Module `GaloisForLFunctions/RHTower/ThetaCuspWignerPairCenterWeight.lean`:

15. `integrableOn_rpow_mul_iff_integrable_exp_chart` — the exponential chart is an integrability
    *equivalence*, not only an identity.
16. `integrableOn_rpow_mul_thetaCuspWignerRadialProfile`,
    `integrableOn_rpow_mul_log_mul_thetaCuspWignerRadialProfile`,
    `integrable_exp_mul_thetaCuspSourceTerm_pair`,
    `integrable_log_scale_mul_exp_mul_thetaCuspSourceTerm_pair` — both pair currents converge.
17. `log_thetaCuspWignerAtomScale : log (2πnm e^{2u}) = log(2πnm) + 2u`.
18. `integral_center_mul_exp_mul_thetaCuspSourceTerm_pair` — **the centre-weighted current**
    `∫ u e^{(2σ−1)u} Φ_n(u+t)Φ_m(u−t) du
      = (4(2πnm)^σ)^{-1}(1/cosh w)^{σ+2}
          (LogWeight σ (cosh w) − log(2πnm) Γ(σ+2) Q σ (cosh w))`.

Item 18 is the separation: the first two factors are a Dirichlet weight times a function of the
separation `w` alone, exactly as in item 6, but the coefficient `log (2π n m)` sits **outside** the
Dirichlet factor.  Since `Σ_n (log n) n^{−σ+iξ} = −ζ'(σ−iξ)`, its sum over `n, m` produces
`ζ'(σ−iξ)ζ(σ+iξ) + ζ(σ−iξ)ζ'(σ+iξ) = |ζ(σ+iξ)|² · 2 Re(ζ'/ζ)(σ+iξ)` in place of a modulus square.

Module `GaloisForLFunctions/RHTower/CoshPowerSpectrumOrderDerivative.lean`:

19. `coshPowerSpectrum b ξ = 2^{b−1}|Γ((b+iξ)/2)|²/Γ(b)`, with
    `integral_cosh_rpow_neg_mul_cos : ∫_ℝ (cosh y)^{−b} cos(ξy) dy = coshPowerSpectrum b ξ`
    (real form of the corpus's complex transform).
20. `hasDerivAt_coshPowerSpectrum` and
    `integral_log_cosh_mul_cosh_rpow_neg_mul_cos : ∫_ℝ log(cosh y)(cosh y)^{−a}cos(ξy) dy
       = −deriv (fun b => coshPowerSpectrum b ξ) a`,
    by differentiation under the integral in the **order** parameter.  The domination is
    `log(cosh y)(cosh y)^{−b} ≤ (1/δ)(cosh y)^{−c}` for `c + δ ≤ b` (from `Real.log_le_rpow_div`),
    applied with `δ = c = a/4` on `b ∈ (a/2, 3a/2)`.

Module `GaloisForLFunctions/RHTower/ThetaCuspWignerPairLogSpectrum.lean`:

21. `thetaCuspWignerPairLogKernel`, `thetaCuspWignerPairLogSpectrum` and
    `integral_thetaCuspWignerPairLogKernel_mul_cos` — the log-scale kernel's spectrum in closed
    form: two `coshPowerSpectrum` values and two of its order derivatives, with coefficients
    `Γ'(σ+4)`, `9Γ'(σ+2) − 6Γ'(σ+3)`, `Γ(σ+4)`, `9Γ(σ+2) − 6Γ(σ+3)`.
22. `integral_log_scale_..._pair_factor` and
    `integral_center_mul_exp_mul_thetaCuspSourceTerm_pair_factor` —
    `∫ u e^{(2σ−1)u}Φ_nΦ_m du = ½ n^{−σ}m^{−σ}(LogKernel σ w − log(2πnm)·Kernel σ w)`.

## What the criterion actually is

`RHTower.thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis`
(`HedenmalmCenterMixedOrientationBoundary.lean`) is the corpus's endpoint, and
`fourier_thetaCuspHorizontalAutocorrelationTangent_scaled`
(`HedenmalmLocalFrameObstruction.lean`) evaluates the transform as

`ξ'(½+a+bi) ξ(½+a−bi) + ξ(½+a+bi) ξ'(½+a−bi)`,

i.e. `∂_a |ξ(½+a+bi)|²`.  So the criterion is `Re(ξ'/ξ)(½+a+ib) ≥ 0` for `0 < a < ½`, which by
Hadamard is `Σ_ρ (σ−β)/|s−ρ|² ≥ 0`: a zero-location statement.  Everything above is therefore an
**exact σ-derivative dictionary** for that criterion, with the archimedean kernels fully explicit
and sign-resolved — a bridge, not a producer.

Two structural facts follow and are worth keeping:

- Since `∂_σ e^{2σu} = 2u e^{2σu}`, the centre-weighted current is exactly `½ ∂_σ` of the
  exponential current, so item 22 *is* the σ-derivative, computed without differentiating under
  the integral.
- The Hedenmalm weight `r sinh(a r)` on `(0,∞)` equals, after `r = 2u` and evenness,
  `∫_ℝ u (e^{2au} − e^{−2au}) (…) du`.  With `σ = a + ½` the two halves are the centre-weighted
  current at `σ` and at `1 − σ`: the `sinh` is antisymmetrisation under `σ ↔ 1−σ`.
  **Correction (2026-09-24):** an earlier version of this card concluded from this that *"no
  single-`σ` positivity can suffice"*.  That is wrong for the complete source.  The linear centre
  weight is odd, so for even `f`, `∫ u e^{cu} f = −∫ u e^{−cu} f`; since the completed theta
  source is even, `C_σ(t) = −C_{1−σ}(t)` and the antisymmetrised current is simply `2 C_σ(t)`.
  The gate **is** a single-exponent positivity statement.  The genuine difference appears only at
  the atom level, where `Φ_n` is not even — there the `σ ↔ 1−σ` antisymmetry of the pair currents
  is precisely the theta functional equation.

## Paper-level consequence: the pure exponential center weight is RH-blind

Items 6 and 8 give, in the half-plane `σ > 1` where the double series converges absolutely,

`D̂_σ(ξ) = ½ Ĝ_σ(ξ) ζ(σ−iξ) ζ(σ+iξ) = ½ π^{−σ} |(s−1) Γ((s+2)/2) ζ(s)|²`,   `s = σ+iξ`,

by item 9.  This is manifestly nonnegative with no RH input, and vanishes exactly at `σ = 1,
ξ = 0`, where the factor `ξ² + (σ−1)² = |s−1|²` cancels the double pole of `|ζ|²`.  The bracket is
`|π^{−s/2} (s−1) Γ((s+2)/2) ζ(s)|²` up to the elementary factor `|s/2|²` relating `Γ((s+2)/2)` to
`Γ(s/2)`, i.e. the completed zeta modulus squared.

**Consequence.** The purely exponential center weight carries no RH content.  The corpus's
center-mixed weight is `r sinh(a r)`; the `sinh(ar)` part is a combination of exponential weights
and is therefore unconditionally positive-definite.  All RH content sits in the *linear* factor
`r`, whose contribution is `−∂_σ` of the modulus square above and therefore carries `ζ'/ζ`.

This refines the corpus's existing negativity witness: item 7 says exactly which pairs at which
separations are negative, and item 8 plus the classical `ĥ_a > 0` says their Fourier-side sum is
nevertheless a modulus square.

Module `GaloisForLFunctions/RHTower/ThetaCuspWignerPairOrientationAntisymmetry.lean`:

23. `integrable_center_mul_exp_mul_thetaCuspSourceTerm_pair`.
24. `thetaCuspPairOrientationCurrent a n m t :=
    ∫_ℝ u (e^{2au} − e^{−2au}) Φ_n(u+t)Φ_m(u−t) du`, with
    `thetaCuspPairOrientationCurrent_eq_sub`: on `0 < a < 1/2` it is the centre-weighted current at
    `σ = a + 1/2` minus the one at `1 − σ = 1/2 − a`.  **The `sinh` is antisymmetrisation under
    `σ ↔ 1−σ`, as a theorem.**
25. `thetaCuspPairOrientationCurrent_eq_kernels` — the same in closed form, an antisymmetric
    combination of `thetaCuspWignerPairLogKernel` and `thetaCuspWignerPairKernel` at `σ` and `1−σ`.
26. `integral_Ioi_radial_sinh_eq` — `∫_{(0,∞)} r sinh(ar) f(r/2) dr = 4∫_{(0,∞)} u sinh(2au) f(u) du`,
    hypothesis-free, making the `r = 2u` identification exact.

Module `GaloisForLFunctions/RHTower/ThetaCuspWignerRadialGammaProductRule.lean`:

27. `deriv_Gamma_add_one : 0 < x → Γ'(x+1) = x Γ'(x) + Γ(x)` (mathlib has `Γ(x+1) = xΓ(x)` but
    not its derivative).
28. `thetaCuspWignerRadialLogWeight_eq_product_rule` —
    `LogWeight σ C = (Γ'(σ+2) − Γ(σ+2)log C)·Q σ C + Γ(σ+2)·∂_σQ σ C`, where
    `∂_σQ σ C = (2σ+5)/C² − 6`.  Every Gamma value and derivative at `σ+3`, `σ+4` collapses onto
    `Q` and `∂_σQ`.
29. `thetaCuspWignerRadialLogWeight_one : LogWeight σ 1 = Γ'(σ+2)(σ²−σ+3) + Γ(σ+2)(2σ−1)`.
    **The factor `2σ−1` changes sign exactly at the critical abscissa**, so at zero hyperbolic
    separation `Γ(σ+2)(2σ−1)` is the antisymmetric part of the centre weight under `σ ↔ 1−σ`.

Module `GaloisForLFunctions/RHTower/ThetaCuspWignerPairKernelOrderDerivative.lean`:

30. `hasDerivAt_const_rpow : HasDerivAt (fun τ => b^τ) (b^σ log b) σ` for `b > 0`.
31. `hasDerivAt_thetaCuspWignerPairKernel` / `deriv_thetaCuspWignerPairKernel` —
    `d/dσ [Kernel σ y] = LogKernel σ y − log(2π)·Kernel σ y`.  The log-scale kernel **is** the
    order derivative, certified rather than asserted.
32. `thetaCuspPairOrientationCurrent_one_one` — for the `(1,1)` pair the Dirichlet weight is
    trivial, so the gate reduces to
    `½ ∂_τKernel τ (2t)|_{τ=a+½} − ½ ∂_τKernel τ (2t)|_{τ=½−a}`:
    a convexity question for `τ ↦ Kernel τ y` across the critical abscissa.

## The archimedean (1,1) current is eventually negative

Write `Kernel_τ(y) = A(τ)·Q(τ,C)`, `C = cosh y`, `A(τ) = (2π)^{−τ}Γ(τ+2)C^{−(τ+2)}/2 > 0`.  Then
`∂_τ Kernel_τ(y) = A(τ)·B(τ,C)` with `B(τ,C) = (ψ(τ+2) − log(2πC))·Q(τ,C) + ∂_τQ(τ,C)`.

As `C → ∞`: `Q → −(6τ+3)`, `∂_τQ → −6`, so `B(τ,C) ∼ (6τ+3) log C > 0` for both `τ = σ` and
`τ = 1−σ`.  But `A(τ) ∝ C^{−(τ+2)}`, and `σ + 2 > 3 − σ` exactly when `σ > ½`, so `A(σ)` decays
strictly faster than `A(1−σ)`.  Hence

`∂_τKernel|_σ − ∂_τKernel|_{1−σ} ∼ −A(1−σ)·(9−6σ)·log C < 0` .

**The `(1,1)` orientation current is negative for all large `|t|`.**  It does not falsify the
route — the Hedenmalm gate asks for Fourier nonnegativity, not pointwise sign — but it rules out
every strategy that would deduce the gate from pointwise positivity of the current, already at the
archimedean base term where there is no arithmetic input at all.  The decay exponent inequality
`σ + 2 > 3 − σ ⟺ σ > ½` is exactly the `σ ↔ 1−σ` asymmetry.

Module `GaloisForLFunctions/RHTower/ThetaCuspCenterCurrentReflection.lean`:

33. `integral_center_exp_eq_neg_of_even` — for even `f`, `∫ u e^{cu} f u du = −∫ u e^{−cu} f u du`.
34. `integral_center_mul_exp_mul_thetaCuspFullSource_reflect` — hence `C_σ(t) = −C_{1−σ}(t)` for
    the complete theta source, unconditionally.
35. `integral_center_sinh_mul_thetaCuspFullSource_eq_two_mul` — the antisymmetrised current is
    `2 C_σ(t)` (with the two integrability premises).

## Route Q band analysis (2026-09-24)

The cap `Re z ≤ 279/20` in `PrimeArchCentralPairedFourthTraceBand` is **not** a loose constant.
With `λ = w^{−2}`, `w = γ − i d`, `d = Re ρ − ½`:
`λ.re = (γ²−d²)/(γ²+d²)²`, `λ.im = 2γd/(γ²+d²)²`, so `λ.re ≤ 1/γ²` with slack `3γ²d² + d⁴`,
**sharp at `d = 0`**.  The band is exactly `(Re z)² < (1 − √(2/215))·(431/2)`, i.e. tight against
the order-23 height floor.

The pair barrier is `normSq λ·[(1−uλ.re)² + (uλ.im)² + v²normSq λ] − 2λ.im²` with
`u = (z²).re`, `v = (z²).im`, and the current proof drops the last two terms.  Restoring them does
**not** extend the band: at `u λ.re = 1` (i.e. `Re z ≈ |γ|`) one gets `(uλ.im)² = ε` and
`v²normSq λ ≈ 4(Im z)²/γ²` with `ε = λ.im²/λ.re² ≈ 4d²/γ²`, and the barrier equals
`λ.re²[ε² − ε + (1+ε)v²normSqλ]`, which is negative unless `|Im z| ≳ |d|`.  Since `Im z < 1/2` is
free and `|d|` is only bounded by `1/2`, no finite band extension follows.  **The limit is the
barrier method, not the constant**, consistent with route Q's recorded exact negative disk.

## Cross-check against route G

Route G (`rh-current-frontier-map.md`) already records: *"The two-width local positive radius and
gapped-cluster survivor are exact, but finite-width design cannot yield global diagonal
domination."*  `thetaCuspWignerCriticalCosh σ` is exactly such a local positive radius, so the sign
law of item 2 lands inside a recorded obstruction.  **Do not produce further local positivity radii
on this route**; the recorded open problem is global control of the negative cross channel.

## Open core

- The secant-power Fourier transform was **already in the corpus**
  (`HTGeometry.integral_cosh_rpow_neg_mul_exp_eq_ofReal`, via the logistic substitution and the
  complex Beta integral), so item 9 is unconditional.
- `[OPEN CORE]` Summing items 6 and 9 over `n, m` to reach `D̂_σ` itself needs the Dirichlet
  interchange, valid for `σ > 1`.
- The linear-weight centre integral is **closed** (item 18).
- The archimedean profile is **closed** (items 19–21).
- `[OPEN CORE]` A producer.  The dictionary converts the criterion into
  `Σ_{n,m} (nm)^{−σ}(LogKernel σ w_{nm} − log(2πnm) Kernel σ w_{nm}) ≥ 0`, `w_{nm} = 2t + log(n/m)`,
  absolutely convergent only for `σ > 1`, while the criterion lives at `σ ∈ (½,1)`.  No positivity
  mechanism has been produced; the identity is exact but does not exclude zeros.
- `[OPEN CORE]` The spectral gate `G(σ,ξ) ≥ G(1−σ,ξ)` for `σ ∈ (½,1)`, where
  `G(τ,ξ) = thetaCuspWignerPairLogSpectrum τ ξ − log(2π)·thetaCuspWignerPairSpectrum τ ξ`.  Both
  sides are closed forms in `Γ`, `Γ'`, `coshPowerSpectrum` and its order derivative, so this is a
  pure archimedean inequality with no arithmetic input.  At `ξ = 0` the duplication formula gives
  `coshPowerSpectrum b 0 = √π Γ(b/2)/Γ((b+1)/2)`.
- (done) Formalise the `σ ↔ 1−σ` antisymmetrisation: the Hedenmalm weight is
  `C_σ − C_{1−σ}` with `C` the centre-weighted current.  This is a clean Lean target and it
  states precisely why a single-`σ` positivity argument cannot close the route.
- The double series converges absolutely only for `σ > 1`; the term-wise identity below `σ = 1`
  needs the theta functional equation, not term-wise absolute convergence (`Σ_n |Φ_n(x)|` grows
  like `e^{−x/2}` as `x → −∞` while `Φ` is even).  The Hedenmalm weight `r sinh(a r)` has
  `0 ≤ a < 1/2`, i.e. `σ = a + 1/2 ∈ [1/2, 1)`, so the RH-relevant range is **outside** the region
  of absolute convergence.  Every per-pair theorem above holds for all `σ > 0`; only the
  summation step is restricted.

## Log
- 2026-09-23 — created at stage 3; thirteen Lean theorems across three modules checked, wired into
  `RHTower`, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`), `formal_tools.py lint`
  passes.
- 2026-09-24 — items 19–22 added (`CoshPowerSpectrumOrderDerivative`,
  `ThetaCuspWignerPairLogSpectrum`); archimedean profile closed; criterion identified as
  `Re(ξ'/ξ) ≥ 0` on the right half-strip.  Verdict on the chain: `[BRIDGE]`.  All axiom-clean;
  lint passes.
- 2026-09-24 — items 11–18 added across three further modules (`LogWeightedEulerIntegral`,
  `ThetaCuspWignerPairLogScaleWeight`, `ThetaCuspWignerPairCenterWeight`); the centre-weighted
  current is closed in exact form.  All axiom-clean; lint passes.
