# Half-line polar threshold law, resolvent depletion, and universal multiplier no-go

- **ID:** ahd-half-line-polar-threshold-and-resolvent-depletion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [AHD](../1-in-progress/ahd-arithmetic-hodge-theory-of-degenerations-programme.md)

## Exact arithmetic statements

1. **Half-line continuum polar threshold identity.**
   Call `R > 0` half-line polar-positive (`HalfLinePolarPositive R`) if for every measurable
   `F : ℝ → ℝ` and `β : ℝ` with `F ∈ L¹(ℝ) ∩ L²(ℝ)`, `∫ F(u)² e^{-8u} du < ∞`, `F = 0` on `[0, ∞)`,
   `∫ F² ≤ 1`, and `(∫ F²) + β² > 0`, there exists `T ≥ e^{G₀}` such that
   `Q_T(F) + α(R) ∫_{u<0} F(u)² e^{-8u} du + (∫ φ²) D(R) β² + 2(∫ φ) β ∫ F · P_polar > 0`.
   Let `halfLinePolarThreshold := sSup { (R : EReal) | 0 < R ∧ HalfLinePolarPositive R }`. Then
   `polarPaymentCriticalThreshold = halfLinePolarThreshold = criticalPositivityThreshold`,
   and for `W := ⨅_{A ≥ 0} windowThreshold A`,
   `polarPaymentCriticalThreshold = W ↔ ∀ R > 0, (R : EReal) < W → HalfLinePolarPositive R`.

2. **Critical half-line ground states, quantitative reciprocal shift, and pole-orthogonality classification.**
   Either `RiemannHypothesis` holds, or `W = (W₀ : EReal)` with `0 < W₀` and there exists a
   measurable half-line ground state `F_*` (`∫ F_*² = 1`, `F_* = 0` on `[0, ∞)`,
   `∫ F_*² e^{-8u} du < ∞`, and `Q_T(F_*) + α(W₀) ∫_{u<0} F_*² e^{-8u} du ≤ 0` for all `T ≥ e^{G₀}`).
   For every critical half-line ground state `F` at `W₀ > 0`, writing
   `S := splineAtom · ∫ F · P_polar`, `D₀ := D(W₀)`, and `I₈ := ∫_{u<0} F(u)² e^{-8u} du`,
   `polarPaymentCriticalThreshold ≤ ((1 / W₀ + D₀ S² / (7 J̃(1) D₀² I₈ + J(1) S²))⁻¹ : ℝ)`.
   In particular, any ground state with `∫ F · P_polar ≠ 0` forces `polarPaymentCriticalThreshold < W₀`,
   and unconditionally one of three cases holds:
   - `RiemannHypothesis` (`polarPaymentCriticalThreshold = W = ⊤`),
   - `¬ RiemannHypothesis` and `polarPaymentCriticalThreshold < W`,
   - `¬ RiemannHypothesis`, `polarPaymentCriticalThreshold = W = (W₀ : EReal)` (`W₀ > 0`), a
     critical half-line ground state at `W₀` exists, and every critical half-line ground state `F`
     at `W₀` satisfies `∫ F(u) P_polar(u) du = 0`.

3. **Physical-space half-line resolvent identities on `M₈(-∞, 0)`.**
   For `b > 4` and measurable `F` vanishing on `[0, ∞)` with `∫ F(u)² e^{-8u} du < ∞`, set
   `(T_b F)(x) := e^{bx} ∫_x^0 F(y) e^{-by} dy` (`x < 0`), `0` (`x ≥ 0`). Then:
   - `∫_{u<0} (T_b F)(u)² e^{-8u} du ≤ (b - 4)⁻² ∫_{u<0} F(u)² e^{-8u} du`,
   - for `a, b > 4`,
     `(a + b - 8) ⟨T_a F, T_b F⟩_{M₈} = ⟨F, T_b F⟩_{M₈} + ⟨F, T_a F⟩_{M₈} = (b - 4) ‖T_b F‖_{M₈}² + (a - 4) ‖T_a F‖_{M₈}²`
     and `(b - a) T_b(T_a F) = T_a F - T_b F`,
   - `⟨F, T_b F⟩_{M₈} = (b - 4) ‖T_b F‖_{M₈}²`,
   - for `G = T_{15/2} F` and `H₈ = T₈ G`, `⟨F, H₈⟩_{M₈} = -‖G‖_{M₈}² + 30 ‖H₈‖_{M₈}²` and
     `(8 / 15) ‖G‖_{M₈}² + (24 / 465) ⟨F, H₈⟩_{M₈} = (224 / 465) ‖G‖_{M₈}² + (48 / 31) ‖H₈‖_{M₈}² ≥ (224 / 465) ‖G‖_{M₈}²`,
   - for `Re s < 4 < b`, `∫_{x<0} (T_b F)(x) e^{-sx} dx = (b - s)⁻¹ ∫_{x<0} F(x) e^{-sx} dx`.

4. **Depleted resolvent kernel negativity, single-orbit ratio gap, and piecewise square root.**
   Let `m(z) := 4 / (1/4 - z²) - 12 / (64 - z²) = (253 + 8z²) / ((1/4 - z²)(64 - z²))`.
   On `{z : ℂ | |Re z| < 1/2 ∧ 331/4 < (Im z)²}` (hence at `z_q = ρ_q - 1/2` for every `q : XiZeroCopy`):
   - `Re m(z) < 0` and `25 ‖m(z)‖² < -Re m(z)` (so `‖m(z)‖² / (-Re m(z)) < 1/25 < 224/465`),
   - the piecewise holomorphic factor `Φ̃(z) := ±i exp(log(-m(z)) / 2)` (`+` on `Im z ≥ 0`, `-` on
     `Im z < 0`) is complex-analytic on both open half-strips `{|Re z| < 1/2, Im z > √(331/4)}`
     and `{|Re z| < 1/2, Im z < -√(331/4)}`, satisfies `Φ̃(z̄) = conj(Φ̃(z))`, and obeys
     `Φ̃(z) Φ̃(-z) = -m(z)` identically.

5. **Universal holomorphic multiplier CP domination no-go.**
   No countable square-bounded family `ψ : ℕ → ℂ → ℂ` analytic on `{s : ℂ | Re s < 4}`
   (`∑_n B_n < ∞`, `‖ψ_n(z)‖² ≤ B_n` on `|Re z| ≤ 1`), nor any finite family `ψ : Fin m → ℂ → ℂ`
   analytic on `{s : ℂ | Re s < 4}` (with no growth condition), satisfies
   `Re((m(z) + ∑_n ψ_n(z) ψ_n(-z)) u v) ≤ 0` for all `u, v ∈ ℂ` across the verified off-line strip
   `{z : ℂ | 0 < |Re z| < 1/2 ∧ 431/2 ≤ (Im z)²}`.

## Paper proof

1. **Half-line polar threshold.**
   If `0 < R < S` and `PolarPaymentAt S A` holds for all `A ≥ 0`, `no_charged_limit_profile_below_polarPayment`
   gives `HalfLinePolarPositive R`. Conversely, assume `HalfLinePolarPositive R` (`R > 0`) and let
   `h ∈ C²(ℝ)` vanish outside `[-A, 0]` (`A ≥ 0`). Continuity at `0` gives `h(0) = 0`, so
   `F₀ := halfWeight h` vanishes on `[0, ∞)`. Put `β₀ := -generalTerminalPolarSource A h / ((∫ φ) D(R))`.
   If `(∫ F₀²) + β₀² = 0`, both `F₀` and `generalTerminalPolarSource A h` vanish; otherwise normalize
   `(F₁, β₁) := σ⁻¹ (F₀, β₀)` (`σ = √((∫ F₀²) + β₀²)`). Evaluating `HalfLinePolarPositive R` on `(F₁, β₁)`
   and using `truncatedWeilForm F₁ T ≤ weilQuad F₁` (`T ≥ e^{G₀}`) together with
   `generalTerminalPolarSource_eq_integral_polarSourceProfile` yields `PolarPaymentAt R A`.

2. **Ground states and quantitative reciprocal shift.**
   If `¬ RiemannHypothesis`, `highConductorCriticalThreshold_eq_iInf_windowThreshold` and
   `highConductorCriticalThreshold_eq_top_iff_riemannHypothesis` give `W = (W₀ : EReal)` with `0 < W₀`.
   Applying `eventually_complement_collar_weilQuad_bridge` along `R_k = W₀ + 1/(k+1)` and extracting a
   convergent subsequence via `exists_strong_negative_limit_of_bounded_weilQuad` and
   `eventually_lt_weilQuad_of_subsequence_L1_limit` produces a unit-norm half-line ground state `F_*`
   at `W₀`. For any ground state `F` at `W₀`, `I₈ ≥ ∫ F² = 1 > 0`; setting
   `shift := D₀ S² / (7 J̃(1) D₀² I₈ + J(1) S²)`, `Rb := (1 / W₀ + shift)⁻¹`, and
   `β := -(∫ φ) P / ((∫ φ²) D₀)` makes the increment
   `(α(Rb) - α(W₀)) I₈ + (∫ φ²) D(Rb) β² + 2(∫ φ) β P` vanish identically via
   `D(Rb) - D(W₀) = J(1) (1/Rb - 1/W₀)`, so `(F, β)` has nonpositive charged truncated energy at `Rb`
   for all `T ≥ e^{G₀}`, forcing `polarPaymentCriticalThreshold ≤ Rb` by
   `no_charged_limit_profile_below_polarPayment`.

3. **Resolvent identities on `M₈(-∞, 0)`.**
   In the isometric gauge `w(y) := F(y) e^{-4y}`, `(T_b F)(x) e^{-4x} = ∫_x^0 w(y) e^{(b-4)(x-y)} dy`
   (`x < 0`). Weighted Cauchy–Schwarz against `e^{(b-4)(x-y)}` and Fubini yield
   `‖T_b F‖_{M₈}² ≤ (b - 4)⁻² ‖F‖_{M₈}²`. Integrating
   `w(y) w(z) e^{(a-4)(x-y) + (b-4)(x-z)}` on `{x < min(y, z), y ≤ 0, z ≤ 0}` by Fubini gives
   `(a + b - 8) ⟨T_a F, T_b F⟩_{M₈} = ⟨F, T_b F⟩_{M₈} + ⟨F, T_a F⟩_{M₈}`. Fubini on `x < t < y ≤ 0`
   gives `(b - a) T_b(T_a F) = T_a F - T_b F`, whence `T₈ F = G - H₈ / 2` for `G = T_{15/2} F`,
   `H₈ = T₈ G`, yielding `⟨F, H₈⟩_{M₈} = -‖G‖_{M₈}² + 30 ‖H₈‖_{M₈}²` and the `224 / 465` identity.
   Fubini on `x < y ≤ 0` gives the Laplace identity on `{Re s < 4}`.

4. **Depleted kernel bounds and square-root factorization.**
   For `u = (Re z)² ∈ [0, 1/4)` and `v = (Im z)² = 331/4 + t` (`t > 0`),
   `Re(4/(1/4 - z²)) ≤ 4(v + 1/4)/v²` and `Re(12/(64 - z²)) > 12(v + 255/4)/(v² + 129v + 4096)`,
   whose difference numerator `8v³ + 248v² - 16513v - 4096 = 8t³ + 2234t² + (377745/2)t + 38885881/8 > 0`
   proves `Re m(z) < 0`. Furthermore `‖253 + 8z²‖² < 64v² - 4016v + 65025` while
   `‖1/4 - z²‖² > v²` and `‖64 - z²‖² > (v + 255/4)²`; expanding
   `(8v³ + 248v² - 16513v - 4096)(v + 255/4)² - 25(64v² - 4016v + 65025)(v² + 129v + 4096)`
   in `t > 0` gives
   `8t⁵ + 2978t⁴ + (759065/2)t³ + (166946553/8)t² + (2660764269/4)t + 381880053719/32 > 0`,
   proving `25 ‖m(z)‖² < -Re m(z)`. Since `-m(z) ∈ {Re w > 0} ⊂ Complex.slitPlane`,
   `Φ̃(z) = ±i exp(log(-m(z)) / 2)` is analytic on each half-strip, conjugate-symmetric, and satisfies
   `Φ̃(z) Φ̃(-z) = (i)(-i) exp(log(-m(z))) = -m(z)` for `Im z ≠ 0`.

5. **Universal multiplier no-go.**
   Testing `u = conj(r(z)), v = 1` on `r(z) := m(z) + Ψ(z)` (`Ψ(z) := ∑_n ψ_n(z) ψ_n(-z)`) forces
   `r = 0` on a neighborhood of `1/4 + 15i` inside the convex preconnected strip `U := {|Re z| < 1/2}`.
   Weierstrass uniform convergence (`‖ψ_n(z) ψ_n(-z)‖ ≤ B_n` on `{|Re z| < 1}`) makes `Ψ` analytic on
   `{|Re z| < 1}`, so `r` is analytic on `U` and vanishes identically on `U` by the identity theorem.
   Along `z_k := 1/2 - 1/(k + 3) ∈ U`, `z_k → 1/2` while `0 = (1/4 - z_k²) r(z_k) → 4 + 0 = 4`,
   contradiction.

## Lean

- `formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/HalfLinePolarThresholdAndGroundStateOrthogonality.lean`
  (wired in `ArithmeticHodgeTheoryOfDegenerations.lean`):
  `HalfLinePolarPositive`, `halfLinePolarThreshold`,
  `polarPaymentCriticalThreshold_eq_halfLinePolarThreshold`,
  `criticalPositivityThreshold_le_halfLinePolarThreshold`,
  `polarPaymentCriticalThreshold_eq_iInf_windowThreshold_iff_halfLinePolarPositive`,
  `IsCriticalHalfLineGroundState`,
  `riemannHypothesis_or_exists_criticalHalfLineGroundState`,
  `polarPaymentCriticalThreshold_le_of_criticalHalfLineGroundState`,
  `polarPaymentCriticalThreshold_lt_of_charged_criticalHalfLineGroundState`,
  `polarPaymentCriticalThreshold_windowThreshold_classification`.
- `formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/HalfLineResolventIdentitiesAndMultiplierNoGo.lean`
  (wired in `ArithmeticHodgeTheoryOfDegenerations.lean`):
  `halfLineResolvent`, `measurable_halfLineResolvent`,
  `integrable_halfLineResolvent_sq_mul_exp_neg_eight`,
  `integral_halfLineResolvent_sq_mul_exp_neg_eight_le`,
  `mul_integral_halfLineResolvent_mul_eq_add_pairings`,
  `integral_mul_halfLineResolvent_exp_neg_eight`,
  `integral_halfLineResolvent_mul_halfLineResolvent_exp_neg_eight`,
  `halfLineResolvent_comp_sub`,
  `integral_mul_iteratedResolvent_fifteen_halves_eight`,
  `iteratedResolvent_depletion_identity`,
  `iteratedResolvent_depletion_ge`,
  `laplace_halfLineResolvent`,
  `depletedResolventKernel`, `depletedResolventKernel_eq_div`,
  `re_depletedResolventKernel_neg_of_strip`,
  `twenty_five_mul_norm_sq_depletedResolventKernel_lt_neg_re`,
  `re_depletedResolventKernel_xiZeroCopy_neg`,
  `twenty_five_mul_norm_sq_depletedResolventKernel_xiZeroCopy_lt`,
  `depletedSquareRootFactor`,
  `analyticOnNhd_depletedSquareRootFactor_upper`,
  `analyticOnNhd_depletedSquareRootFactor_lower`,
  `depletedSquareRootFactor_conj`,
  `depletedSquareRootFactor_mul_neg`,
  `depletedSquareRootFactor_mul_neg_xiZeroCopy`,
  `xiZeroCopy_centered_mem_verified_offLine_strip`,
  `no_universal_holomorphic_multiplier_domination`,
  `no_finite_universal_holomorphic_multiplier_domination`.
- Axioms: `propext, Classical.choice, Quot.sound`.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  compiles with `lake --old env lean`; axioms standard
