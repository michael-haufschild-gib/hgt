# Universal holomorphic multiplier CP domination of the depleted polar resolvent kernel

Status: `[PROVED HERE] [PROVED IN LEAN] [CORPUS-NOVEL NO-GO] [POSITIVE SURVIVOR FORMALIZED]`

## Route tested

To pay the polar source term below `W = ⨅_{A ≥ 0} windowThreshold A` on `M₈(-∞, 0)` without losing
half-line support `(-∞, 0]`, apply the iterated causal half-line resolvents `G = T_{15/2} F` and
`H₈ = T₈ G` (`(T_b F)(x) = e^{bx} ∫_x^0 F(y) e^{-by} dy` for `x < 0`), whose Laplace multipliers
`(b - s)⁻¹` are analytic on `{s : ℂ | Re s < 4}`, and dominate the resulting depleted spectral
kernel

`m(z) := 4 / (1/4 - z²) - 12 / (64 - z²) = (253 + 8z²) / ((1/4 - z²)(64 - z²))`

across the verified off-line strip `Ω_off := {z : ℂ | 0 < |Re z| < 1/2 ∧ 431/2 ≤ (Im z)²}` by a
universal countable square-bounded (or finite) sum of causal half-line multiplier squares
`∑_n ψ_n(z) ψ_n(-z)` (`ψ_n` analytic on `{s : ℂ | Re s < 4}`) in the completely positive sense

`∀ z ∈ Ω_off, ∀ u v ∈ ℂ, Re((m(z) + ∑_n ψ_n(z) ψ_n(-z)) u v) ≤ 0`.

## Obstruction and Lean no-go theorems

Any complex number `w` satisfying `∀ u v ∈ ℂ, Re(w u v) ≤ 0` vanishes (`u = conj w, v = 1`). Hence
universal completely positive domination on `Ω_off` forces `r(z) := m(z) + ∑_n ψ_n(z) ψ_n(-z) = 0`
on the open neighborhood `{0 < Re z < 1/2, Im z > 14.7}` of `1/4 + 15i` inside the convex strip
`U := {z : ℂ | |Re z| < 1/2}`. Under `∑_n B_n < ∞` with `‖ψ_n(z)‖² ≤ B_n` on `|Re z| ≤ 1` (or for any
finite family with no growth condition), Weierstrass uniform convergence makes
`Ψ(z) := ∑_n ψ_n(z) ψ_n(-z)` complex-analytic on `{z : ℂ | |Re z| < 1}`, hence continuous at
`z = 1/2`. Analytic continuation on `U` forces `r(x_k) = 0` along `x_k := 1/2 - 1/(k + 3) → 1/2`,
contradicting `lim_{z → 1/2} (1/4 - z²) m(z) = 4 ≠ 0`.

Formalized in `GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HalfLineResolventIdentitiesAndMultiplierNoGo`:

- `no_universal_holomorphic_multiplier_domination`: kills every countable square-bounded family
  `ψ : ℕ → ℂ → ℂ` analytic on `{s : ℂ | s.re < 4}`;
- `no_finite_universal_holomorphic_multiplier_domination`: kills every finite family
  `ψ : Fin m → ℂ → ℂ` analytic on `{s : ℂ | s.re < 4}` with no growth hypothesis;
- `xiZeroCopy_centered_mem_verified_offLine_strip`: certifies that every off-line `q : RHTower.XiZeroCopy`
  lies inside `Ω_off`.

## Positive survivors formalized in Lean

1. **Exact physical-space `(15/2, 8)` resolvent depletion identity on `M₈(-∞, 0)`**
   (`HalfLineResolventIdentitiesAndMultiplierNoGo.lean`):
   - `integral_halfLineResolvent_sq_mul_exp_neg_eight_le`: Hardy norm bound
     `‖T_b F‖_{M₈}² ≤ (b - 4)⁻² ‖F‖_{M₈}²` (`b > 4`);
   - `mul_integral_halfLineResolvent_mul_eq_add_pairings`,
     `integral_mul_halfLineResolvent_exp_neg_eight`, `halfLineResolvent_comp_sub`,
     `laplace_halfLineResolvent`: exact symmetric pairing, diagonal pairing, resolvent equation,
     and Laplace transform on `{Re s < 4}`;
   - `integral_mul_iteratedResolvent_fifteen_halves_eight` and `iteratedResolvent_depletion_identity`:
     for `G = T_{15/2} F` and `H₈ = T₈ G`,
     `(8/15) ‖G‖_{M₈}² + (24/465) ⟨F, H₈⟩_{M₈} = (224/465) ‖G‖_{M₈}² + (48/31) ‖H₈‖_{M₈}²`.

2. **Pointwise negativity, `1 / 25` single-orbit ratio gap, and piecewise holomorphic square root**
   (`HalfLineResolventIdentitiesAndMultiplierNoGo.lean`):
   - `re_depletedResolventKernel_neg_of_strip`,
     `twenty_five_mul_norm_sq_depletedResolventKernel_lt_neg_re`,
     `re_depletedResolventKernel_xiZeroCopy_neg`,
     `twenty_five_mul_norm_sq_depletedResolventKernel_xiZeroCopy_lt`: on
     `{|Re z| < 1/2, 331/4 < (Im z)²}` (and unconditionally at every `q : XiZeroCopy`),
     `Re m(z) < 0` and `25 ‖m(z)‖² < -Re m(z)` (`1/25 < 224/465`);
   - `analyticOnNhd_depletedSquareRootFactor_upper`,
     `analyticOnNhd_depletedSquareRootFactor_lower`, `depletedSquareRootFactor_conj`,
     `depletedSquareRootFactor_mul_neg`, `depletedSquareRootFactor_mul_neg_xiZeroCopy`:
     `Φ̃(z) := ±i exp(log(-m(z)) / 2)` is analytic on each open half-strip, conjugate-symmetric,
     and satisfies `Φ̃(z) Φ̃(-z) = -m(z)` identically. The obstruction to universal causal domination
     is therefore purely the branch jump across `Im z = 0` together with the simple poles at
     `z = ±1/2`, not any failure of pointwise positivity on `Ω_off`.

3. **Continuum half-line polar threshold law and critical ground-state orthogonality**
   (`HalfLinePolarThresholdAndGroundStateOrthogonality.lean`):
   - `polarPaymentCriticalThreshold_eq_halfLinePolarThreshold`,
     `polarPaymentCriticalThreshold_eq_iInf_windowThreshold_iff_halfLinePolarPositive`;
   - `riemannHypothesis_or_exists_criticalHalfLineGroundState`,
     `polarPaymentCriticalThreshold_le_of_criticalHalfLineGroundState`,
     `polarPaymentCriticalThreshold_lt_of_charged_criticalHalfLineGroundState`,
     `polarPaymentCriticalThreshold_windowThreshold_classification`: quantitative reciprocal shift
     bound for any critical half-line ground state and unconditional three-way pole-orthogonality
     classification.

## Route decision

Retire state-independent universal holomorphic multiplier domination of `m(z)` across the strip. Any
mechanism deciding `polarPaymentCriticalThreshold = W` must either exploit the zero-set / arithmetic
structure of Weil's form (`∫ F · P_polar = 0` on critical half-line ground states) or use
profile-adapted / non-entire frequency splitting across `Im z = 0` rather than a universal causal
multiplier identity on `{Re s < 4}`.

## Lean audit

- `lake --old env lean GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/HalfLinePolarThresholdAndGroundStateOrthogonality.lean`: passed (`exit 0`);
- `lake --old env lean GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/HalfLineResolventIdentitiesAndMultiplierNoGo.lean`: passed (`exit 0`);
- printed axioms on all theorems: `[propext, Classical.choice, Quot.sound]` only;
- wired into `formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations.lean` and documented in
  `formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/README.md`.
