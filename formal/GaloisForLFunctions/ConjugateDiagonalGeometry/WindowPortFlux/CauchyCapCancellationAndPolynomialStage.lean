import GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux.PortFluxDecompositionAndBlowup
import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.SharpStripZeroGrowthAndSqrtLowerBound
import GaloisForLFunctions.ConjugateDiagonalGeometry.SeamSmoothThetaPrefixes
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros

/-!
# Cauchy Horizontal-Cap Cancellation and Polynomial-Stage `Θ(√m)` Window Energy Laws

Complete answer to the polynomial-stage `Θ(√m)` port-flux cancellation problem (Obstacles B15 + A10)
building on `PortFluxDecompositionAndBlowup`:

1. **Exact Cauchy horizontal-cap cancellation identity**
   (`rightEdgeFlux_add_horizCapFlux_eq_vertFlux`, `exists_norm_rightEdgeFlux_add_horizCapFlux_le`):
   Whenever `finiteThetaAmplitude N` is nonvanishing on `[σ₁, 3/2] × [y₁, y₂]`, Cauchy's theorem on
   that right sub-rectangle cancels the `e^t` right-edge flux against the horizontal cap flux
   `horizCapFlux σ₁ (3/2)` down to `vertFlux σ₁`, which has magnitude `O(e^{(σ₁ - 1/2) t})`.
   Whereas `rightEdgeFlux + leftEdgeFlux` and `rightEdgeFlux + leftHalfPort` blow up as `Ω(e^t / t)`
   on every Burnol unit window (`exists_burnol_rightAddLeftFlux_exp_blowup`), the true geometric
   partner cancelling the `e^t` endpoint oscillation of `rightEdgeFlux` is the `x = 3/2` endpoint
   contribution of the horizontal caps `[σ₁, 3/2] × {y₁, y₂}`.

2. **Unconditional sub-`e^{t/2}` cap cancellation on every Burnol unit window at `Θ(√m)` prefix**
   (`exists_burnol_subHalfExp_cap_cancellation`):
   Using the threshold-free zero-free region (`ZetaZeroFreeRegionAllZeros.re_le_one_sub_of_zeta_zero`)
   and quantitative zero transfer (`exists_xiZero_near_thetaZero`), at explicit `Θ(√m)` prefix
   `capCancelSqrtPrefix m = capCancelSqrtConst * (Nat.sqrt m + 1)` and cap abscissa
   `burnolCapAbscissa m = 1 - 1 / (116 * log(m + 5)) ∈ (3/4, 1)`, `finiteThetaAmplitude N` is
   zero-free on `[burnolCapAbscissa m, 3/2] × [y₁(m), y₂(m)]` and
   `‖rightEdgeFlux + horizCapFlux (burnolCapAbscissa m) (3/2)‖ ≤ M * exp((burnolCapAbscissa m - 1/2) t)`
   strictly below `e^{t/2}` for every `m : ℕ`.

3. **Window-local subexponential energy characterization and quadratic-horizon vanishing**
   (`subexp_windowEnergy_tfae`, `centeredThetaExpSum_eq_zero_above_quadratic_horizon`):
   On any boundary-regular centered window, subexponential growth of `|𝒵_N(t)|²` is equivalent to
   subexponential growth of `|𝒫_+(t)|²`, Laplace integrability against `e^{-xt}` for all `x > 0`,
   local critical-line purity of `A_N` inside the window, and strip-contained stage-uniform Szegő
   positivity; unconditionally, `𝒵_N(t) = 0` for all `t` above the quadratic horizon
   `C_hor * (N + 2)²` despite `A_N` having infinitely many off-line zeros outside every strip.

4. **Polynomial-stage `Θ_k(√m)`-prefix `RH` equivalence and fixed-degree corridor equivalence**
   (`riemannHypothesis_polynomialStage_tfae`, `invPoly_corridor_iff_fixedDegree_polynomialStage`):
   Explicit `Θ_k(√m)` prefix `polySqrtPrefix k m = polySqrtConst k * (Nat.sqrt m + 1)` dominates
   `besselUnitPrefix m S` for all `S ≤ (m + 6)^k`, yielding unconditional equivalences for
   `RiemannHypothesis` (across all `k, m : ℕ`) and for fixed-degree inverse-polynomial zero-free
   corridors `|Re ρ - 1/2| ≤ C / |Im ρ|^k` (`k ≥ 1`).
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux

open GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ## §1 Exact Cauchy horizontal-cap cancellation and unconditional sub-`e^{t/2}` Burnol law -/

/-- **Exact Cauchy horizontal-cap cancellation identity.**
If `finiteThetaAmplitude N` has no zeros on the closed right sub-rectangle `[σ₁, 3/2] × [y₁, y₂]`
(`σ₁ ≤ 3/2`, `y₁ ≤ y₂`), then the `e^t` right vertical-edge flux plus the horizontal cap flux across
`[σ₁, 3/2] × {y₁, y₂}` equals the shifted vertical-line flux `vertFlux σ₁ y₁ y₂ N t`. -/
theorem rightEdgeFlux_add_horizCapFlux_eq_vertFlux {σ₁ y₁ y₂ : ℝ}
    (hσ : σ₁ ≤ 3 / 2) (hy : y₁ ≤ y₂) (N : ℕ)
    (hnz : ∀ z ∈ Icc σ₁ (3 / 2) ×ℂ Icc y₁ y₂, _root_.RHTower.finiteThetaAmplitude N z ≠ 0)
    (t : ℝ) :
    rightEdgeFlux y₁ y₂ N t + horizCapFlux σ₁ (3 / 2) y₁ y₂ N t = vertFlux σ₁ y₁ y₂ N t := by
  set g : ℂ → ℂ := fun z => cexp ((t : ℂ) * (z - 1 / 2)) * thetaLogDeriv N z with hg_def
  set U : Set ℂ := {z : ℂ | _root_.RHTower.finiteThetaAmplitude N z ≠ 0}
  have hg_an : AnalyticOnNhd ℂ g U := by
    intro z hz
    have hexp_an : AnalyticAt ℂ (fun w : ℂ => cexp ((t : ℂ) * (w - 1 / 2))) z :=
      (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).cexp
    exact hexp_an.mul (analyticAt_thetaLogDeriv hz)
  set z₁ : ℂ := (σ₁ : ℂ) + (y₁ : ℂ) * I
  set z₂ : ℂ := ((3 / 2 : ℝ) : ℂ) + (y₂ : ℂ) * I
  have hz₁_re : z₁.re = σ₁ := by simp [z₁]
  have hz₁_im : z₁.im = y₁ := by simp [z₁]
  have hz₂_re : z₂.re = 3 / 2 := by simp [z₂]
  have hz₂_im : z₂.im = y₂ := by simp [z₂]
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    rw [hz₁_re, hz₂_re, hz₁_im, hz₂_im, uIcc_of_le hσ, uIcc_of_le hy]
    exact fun z hz => hnz z hz
  have hrect0 : _root_.RHTower.rectIntegral g z₁ z₂ = 0 :=
    _root_.RHTower.rectIntegral_eq_zero_of_analyticOnNhd hsub hg_an
  have hedges : _root_.RHTower.rectIntegral g z₁ z₂ =
      (∫ x in σ₁..(3 / 2 : ℝ), g ((x : ℂ) + (y₁ : ℂ) * I)) -
      (∫ x in σ₁..(3 / 2 : ℝ), g ((x : ℂ) + (y₂ : ℂ) * I)) +
      I * (∫ y in y₁..y₂, g (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) -
      I * (∫ y in y₁..y₂, g ((σ₁ : ℂ) + (y : ℂ) * I)) := by
    simpa only [z₁, z₂, HTGeometry.hEdge, HTGeometry.vEdge] using
      HTGeometry.rectIntegral_eq_edges g σ₁ (3 / 2) y₁ y₂
  have hmul0 : (2 * Real.pi * I)⁻¹ * _root_.RHTower.rectIntegral g z₁ z₂ = 0 := by
    rw [hrect0, mul_zero]
  rw [hedges] at hmul0
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hcancel : ∀ w : ℂ, (2 * Real.pi * I)⁻¹ * (I * w) = ((2 * Real.pi : ℂ)⁻¹) * w := fun w => by
    field_simp [hpi, I_ne_zero]
  have hexpand : (2 * Real.pi * I)⁻¹ *
      ((∫ x in σ₁..(3 / 2 : ℝ), g ((x : ℂ) + (y₁ : ℂ) * I)) -
       (∫ x in σ₁..(3 / 2 : ℝ), g ((x : ℂ) + (y₂ : ℂ) * I)) +
       I * (∫ y in y₁..y₂, g (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) -
       I * (∫ y in y₁..y₂, g ((σ₁ : ℂ) + (y : ℂ) * I))) =
      horizCapFlux σ₁ (3 / 2) y₁ y₂ N t + rightEdgeFlux y₁ y₂ N t - vertFlux σ₁ y₁ y₂ N t := by
    unfold horizCapFlux rightEdgeFlux vertFlux
    rw [show (((3 / 2 : ℝ) : ℂ)) = (3 / 2 : ℂ) by push_cast; rfl]
    dsimp only [g]
    rw [mul_sub, mul_add, hcancel, hcancel]
  rw [hexpand] at hmul0
  linear_combination hmul0

/-- Adjacent-interval additivity of `horizCapFlux`. -/
theorem horizCapFlux_add_adjacent {a b c y₁ y₂ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (N : ℕ)
    (hnz₁ : ∀ x ∈ Icc a c, _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₁ : ℂ) * I) ≠ 0)
    (hnz₂ : ∀ x ∈ Icc a c, _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₂ : ℂ) * I) ≠ 0)
    (t : ℝ) :
    horizCapFlux a c y₁ y₂ N t =
      horizCapFlux a b y₁ y₂ N t + horizCapFlux b c y₁ y₂ N t := by
  have hseg : ∀ (y : ℝ),
      (∀ x ∈ Icc a c, _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y : ℂ) * I) ≠ 0) →
      (∫ x in a..c, cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
          thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)) =
        (∫ x in a..b, cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
          thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)) +
        (∫ x in b..c, cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
          thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)) := by
    intro y hnz
    have hcont : ContinuousOn
        (fun x : ℝ => cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
          thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)) (Icc a c) := by
      refine ContinuousOn.mul (by fun_prop) fun x hx => ?_
      have h1 : ContinuousAt (thetaLogDeriv N) ((x : ℂ) + (y : ℂ) * I) :=
        (analyticAt_thetaLogDeriv (hnz x hx)).continuousAt
      have h2 : ContinuousAt (fun u : ℝ => (u : ℂ) + (y : ℂ) * I) x :=
        (by fun_prop : Continuous fun u : ℝ => (u : ℂ) + (y : ℂ) * I).continuousAt
      exact (ContinuousAt.comp (g := thetaLogDeriv N)
        (f := fun u : ℝ => (u : ℂ) + (y : ℂ) * I) h1 h2).continuousWithinAt
    have hi1 := (hcont.mono (Icc_subset_Icc_right hbc)).intervalIntegrable_of_Icc hab
    have hi2 := (hcont.mono (Icc_subset_Icc_left hab)).intervalIntegrable_of_Icc hbc
    exact (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
  unfold horizCapFlux
  rw [hseg y₁ hnz₁, hseg y₂ hnz₂]
  ring

/-- Uniform `O(e^{(σ - 1/2) t})` bound on `vertFlux σ y₁ y₂ N t` when `A_N ≠ 0` along the segment. -/
theorem exists_norm_vertFlux_le_exp {σ y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
    (hnz : ∀ y ∈ Icc y₁ y₂, _root_.RHTower.finiteThetaAmplitude N ((σ : ℂ) + (y : ℂ) * I) ≠ 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ,
      ‖vertFlux σ y₁ y₂ N t‖ ≤ M * Real.exp ((σ - 1 / 2) * t) := by
  have hcont : ContinuousOn (fun y : ℝ => thetaLogDeriv N ((σ : ℂ) + (y : ℂ) * I)) (Icc y₁ y₂) :=
    fun y hy_m => by
      have h1 : ContinuousAt (thetaLogDeriv N) ((σ : ℂ) + (y : ℂ) * I) :=
        (analyticAt_thetaLogDeriv (hnz y hy_m)).continuousAt
      have h2 : ContinuousAt (fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) y :=
        (by fun_prop : Continuous fun u : ℝ => (σ : ℂ) + (u : ℂ) * I).continuousAt
      exact (ContinuousAt.comp (g := thetaLogDeriv N)
        (f := fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) h1 h2).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hB_nn : 0 ≤ B := (norm_nonneg _).trans (hB y₁ ⟨le_rfl, hy⟩)
  have hdy : 0 ≤ y₂ - y₁ := sub_nonneg.mpr hy
  refine ⟨(2 * Real.pi)⁻¹ * B * (y₂ - y₁) + 1, by positivity, fun t => ?_⟩
  unfold vertFlux
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  have hint : ‖∫ y in y₁..y₂, cexp ((t : ℂ) * (((σ : ℂ) + (y : ℂ) * I) - 1 / 2)) *
        thetaLogDeriv N ((σ : ℂ) + (y : ℂ) * I)‖ ≤
      (B * Real.exp ((σ - 1 / 2) * t)) * |y₂ - y₁| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const' hy fun y hy_m => ?_
    rw [norm_mul, Complex.norm_exp]
    have hre : ((t : ℂ) * (((σ : ℂ) + (y : ℂ) * I) - 1 / 2)).re = (σ - 1 / 2) * t := by
      simp; ring
    rw [hre, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB y hy_m) (Real.exp_pos _).le
  rw [abs_of_nonneg hdy] at hint
  calc (2 * Real.pi)⁻¹ * ‖∫ y in y₁..y₂,
          cexp ((t : ℂ) * (((σ : ℂ) + (y : ℂ) * I) - 1 / 2)) *
            thetaLogDeriv N ((σ : ℂ) + (y : ℂ) * I)‖
      ≤ (2 * Real.pi)⁻¹ * ((B * Real.exp ((σ - 1 / 2) * t)) * (y₂ - y₁)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = ((2 * Real.pi)⁻¹ * B * (y₂ - y₁)) * Real.exp ((σ - 1 / 2) * t) := by ring
    _ ≤ ((2 * Real.pi)⁻¹ * B * (y₂ - y₁) + 1) * Real.exp ((σ - 1 / 2) * t) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- **Horizontal-cap cancellation bound.** If `A_N` has no zeros on `[σ₁, 3/2] × [y₁, y₂]`, then
`‖rightEdgeFlux + horizCapFlux σ₁ (3/2)‖ ≤ M * exp((σ₁ - 1/2) t)` for all `t : ℝ`. -/
theorem exists_norm_rightEdgeFlux_add_horizCapFlux_le {σ₁ y₁ y₂ : ℝ}
    (hσ : σ₁ ≤ 3 / 2) (hy : y₁ ≤ y₂) (N : ℕ)
    (hnz : ∀ z ∈ Icc σ₁ (3 / 2) ×ℂ Icc y₁ y₂, _root_.RHTower.finiteThetaAmplitude N z ≠ 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ,
      ‖rightEdgeFlux y₁ y₂ N t + horizCapFlux σ₁ (3 / 2) y₁ y₂ N t‖ ≤
        M * Real.exp ((σ₁ - 1 / 2) * t) := by
  obtain ⟨M, hM, hbd⟩ := exists_norm_vertFlux_le_exp (σ := σ₁) hy N fun y hy_m =>
    hnz ((σ₁ : ℂ) + (y : ℂ) * I) ⟨⟨by simp, by simpa using hσ⟩, ⟨by simpa using hy_m.1, by simpa using hy_m.2⟩⟩
  refine ⟨M, hM, fun t => ?_⟩
  rw [rightEdgeFlux_add_horizCapFlux_eq_vertFlux hσ hy N hnz t]
  exact hbd t

/-- Critical-line specialization (`σ₁ = 1/2`): if `A_N` has no zeros on `[1/2, 3/2] × [y₁, y₂]`,
`rightHalfPort` equals the pure critical-line integral `vertFlux (1/2)` and is uniformly bounded in
`t : ℝ`. -/
theorem rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
    (hnz : ∀ z ∈ Icc (1 / 2) (3 / 2) ×ℂ Icc y₁ y₂, _root_.RHTower.finiteThetaAmplitude N z ≠ 0) :
    (∀ t : ℝ, rightHalfPort y₁ y₂ N t = vertFlux (1 / 2) y₁ y₂ N t) ∧
    (∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, ‖rightHalfPort y₁ y₂ N t‖ ≤ M) := by
  have heq : ∀ t : ℝ, rightHalfPort y₁ y₂ N t = vertFlux (1 / 2) y₁ y₂ N t := fun t =>
    rightEdgeFlux_add_horizCapFlux_eq_vertFlux (by norm_num) hy N hnz t
  obtain ⟨M, hM, hbd⟩ := exists_norm_rightEdgeFlux_add_horizCapFlux_le (σ₁ := 1 / 2)
    (by norm_num) hy N hnz
  refine ⟨heq, M, hM, fun t => ?_⟩
  simpa only [rightHalfPort, sub_self, zero_mul, Real.exp_zero, mul_one] using hbd t

/-- Elementary logarithmic growth bound `(log x)² ≤ 4 x` for all `x ≥ 1`. -/
private lemma sq_log_le_four_mul {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 4 * x := by
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  set u : ℝ := Real.log x / 2
  have hu_nn : 0 ≤ u := div_nonneg (Real.log_nonneg hx) zero_le_two
  have hexp_u : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hsq : u ^ 2 ≤ (Real.exp u) ^ 2 := pow_le_pow_left₀ hu_nn hexp_u 2
  have hexp_sq : (Real.exp u) ^ 2 = x := by
    rw [sq, ← Real.exp_add]
    have : u + u = Real.log x := by dsimp only [u]; ring
    rw [this, Real.exp_log hx_pos]
  rw [hexp_sq] at hsq
  have hu_sq : (Real.log x) ^ 2 = 4 * u ^ 2 := by dsimp only [u]; ring
  linarith

private lemma one_lt_log_add_five (m : ℕ) : 1 < Real.log ((m + 5 : ℕ) : ℝ) := by
  have hlog4 : 1 < Real.log 4 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  exact hlog4.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast (show 4 ≤ m + 5 by omega)))

/-- Strict sub-`1` cap abscissa `1 - 1 / (116 * log(m + 5))` on the `m`-th Burnol unit window. -/
def burnolCapAbscissa (m : ℕ) : ℝ :=
  1 - 1 / (116 * Real.log ((m + 5 : ℕ) : ℝ))

theorem burnolCapAbscissa_mem_Ioo (m : ℕ) :
    3 / 4 < burnolCapAbscissa m ∧ burnolCapAbscissa m < 1 := by
  have hL : 1 < Real.log ((m + 5 : ℕ) : ℝ) := one_lt_log_add_five m
  unfold burnolCapAbscissa
  have hpos : 0 < 1 / (116 * Real.log ((m + 5 : ℕ) : ℝ)) := by positivity
  have hlt : 1 / (116 * Real.log ((m + 5 : ℕ) : ℝ)) < 1 / 4 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  exact ⟨by linarith, by linarith⟩

private def capCancelBaseBudget : ℝ :=
  |Real.log (_root_.RHTower.thetaCuspIntegerTailConstant *
      _root_.RHTower.thetaAmplitudeEnvelope 2 + 1)| +
    |Real.log burnolGoodLowerConst| + 4 + 180 * (burnolPrefixConst : ℝ)

private lemma capCancelBaseBudget_pos : 0 < capCancelBaseBudget := by
  unfold capCancelBaseBudget; positivity

/-- Explicit multiplier constant `≥ fluxSqrtConst` ensuring `finiteThetaAmplitude N` is zero-free on
`[burnolCapAbscissa m, 3/2] × [burnolUnitLower m, burnolUnitUpper m]` for all `m : ℕ`. -/
def capCancelSqrtConst : ℕ :=
  max fluxSqrtConst (Nat.ceil (Real.sqrt capCancelBaseBudget) + 2)

/-- Explicit `Θ(√m)` prefix schedule `capCancelSqrtConst * (Nat.sqrt m + 1)`. -/
def capCancelSqrtPrefix (m : ℕ) : ℕ :=
  capCancelSqrtConst * (Nat.sqrt m + 1)

theorem fluxSqrtPrefix_le_capCancelSqrtPrefix (m : ℕ) :
    fluxSqrtPrefix m ≤ capCancelSqrtPrefix m :=
  Nat.mul_le_mul_right _ (le_max_left _ _)

theorem burnolPrefix_le_capCancelSqrtPrefix (m : ℕ) :
    burnolPrefixConst * (Nat.sqrt m + 1) ≤ capCancelSqrtPrefix m :=
  (burnolPrefix_le_fluxSqrtPrefix m).trans (fluxSqrtPrefix_le_capCancelSqrtPrefix m)

/-- **Unconditional sub-`e^{t/2}` Cauchy horizontal-cap cancellation on every Burnol unit window.**
For every `m : ℕ` and every `N ≥ capCancelSqrtPrefix m`, `finiteThetaAmplitude N` has no zeros on
`[burnolCapAbscissa m, 3/2] × [burnolUnitLower m, burnolUnitUpper m]` and the horizontal cap flux
across `[burnolCapAbscissa m, 3/2]` cancels `rightEdgeFlux` down to
`O(exp((1/2 - 1/(116 log(m + 5))) t))`, strictly below `e^{t/2}`. -/
theorem exists_burnol_subHalfExp_cap_cancellation (m : ℕ) {N : ℕ}
    (hN : capCancelSqrtPrefix m ≤ N) :
    3 / 4 < burnolCapAbscissa m ∧ burnolCapAbscissa m < 1 ∧
    burnolCapAbscissa m - 1 / 2 < 1 / 2 ∧
    (∀ z ∈ Icc (burnolCapAbscissa m) (3 / 2) ×ℂ Icc (burnolUnitLower m) (burnolUnitUpper m),
      _root_.RHTower.finiteThetaAmplitude N z ≠ 0) ∧
    (∃ M : ℝ, 0 < M ∧ ∀ t : ℝ,
      ‖rightEdgeFlux (burnolUnitLower m) (burnolUnitUpper m) N t +
          horizCapFlux (burnolCapAbscissa m) (3 / 2)
            (burnolUnitLower m) (burnolUnitUpper m) N t‖ ≤
        M * Real.exp ((burnolCapAbscissa m - 1 / 2) * t)) := by
  obtain ⟨hσ_lo, hσ_hi⟩ := burnolCapAbscissa_mem_Ioo m
  have hσ_sub : burnolCapAbscissa m - 1 / 2 < 1 / 2 := by linarith
  have hbdry := burnolUnit_bdry_regular m (burnolPrefix_le_capCancelSqrtPrefix m |>.trans hN)
  have hy_le := burnolUnitLower_le_upper m
  have hL_gt1 : 1 < Real.log ((m + 5 : ℕ) : ℝ) := one_lt_log_add_five m
  set L : ℝ := Real.log ((m + 5 : ℕ) : ℝ) with hL_def
  set r : ℝ := 1 / (232 * L) with hr_def
  have hr_pos : 0 < r := by dsimp only [r]; positivity
  -- Verify the zero-transfer tail bound at radius `r = 1 / (232 * log(m + 5))`.
  set d : ℕ := ∑ w ∈ burnolUnitXiZeros m, (analyticOrderAt _root_.RHTower.xi w).toNat
  have hd_le : (d : ℝ) ≤ (burnolPrefixConst : ℝ) * L := burnolUnitXiZeros_totalOrder_le m
  have hlog1856 : Real.log 1856 < 8 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h2 : (2 : ℝ) ≤ Real.exp (7 / 10 : ℝ) := by
      have hln2 : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
      exact (Real.log_lt_iff_lt_exp zero_lt_two).mp hln2 |>.le
    calc (1856 : ℝ) < (2 : ℝ) ^ (11 : ℕ) := by norm_num
      _ ≤ (Real.exp (7 / 10 : ℝ)) ^ (11 : ℕ) := pow_le_pow_left₀ (by norm_num) h2 11
      _ = Real.exp (77 / 10 : ℝ) := by rw [← Real.exp_nat_mul]; congr 1; norm_num
      _ ≤ Real.exp 8 := Real.exp_le_exp.mpr (by norm_num)
  have hlog_8r : Real.log (8 / r) ≤ 9 * L := by
    have h8r : 8 / r = 1856 * L := by dsimp only [r]; field_simp; ring
    rw [h8r, Real.log_mul (by norm_num) (by linarith)]
    have hlogL : Real.log L ≤ L := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < L)]
    linarith
  have hL_sq : L ^ 2 ≤ 20 * ((m : ℝ) + 1) := by
    have h4 := sq_log_le_four_mul (x := ((m + 5 : ℕ) : ℝ))
      (by exact_mod_cast (show 1 ≤ m + 5 by omega))
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h5 : 4 * ((m + 5 : ℕ) : ℝ) ≤ 20 * ((m : ℝ) + 1) := by push_cast; linarith
    exact h4.trans h5
  have hdlog_le : (d : ℝ) * Real.log (8 / r) ≤ 180 * (burnolPrefixConst : ℝ) * ((m : ℝ) + 1) := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hlog_nn : 0 ≤ Real.log (8 / r) := by
      have h8r : 8 / r = 1856 * L := by dsimp only [r]; field_simp; ring
      exact Real.log_nonneg (by rw [h8r]; linarith)
    calc (d : ℝ) * Real.log (8 / r)
        ≤ ((burnolPrefixConst : ℝ) * L) * (9 * L) :=
          mul_le_mul hd_le hlog_8r hlog_nn (by positivity)
      _ = 9 * (burnolPrefixConst : ℝ) * L ^ 2 := by ring
      _ ≤ 9 * (burnolPrefixConst : ℝ) * (20 * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hL_sq (by positivity)
      _ = 180 * (burnolPrefixConst : ℝ) * ((m : ℝ) + 1) := by ring
  have hN_sq : capCancelBaseBudget * ((m : ℝ) + 1) < ((N + 1 : ℕ) : ℝ) ^ 2 := by
    have hK_ge : Nat.ceil (Real.sqrt capCancelBaseBudget) + 2 ≤ capCancelSqrtConst :=
      le_max_right _ _
    have hsq_nat : (Nat.ceil (Real.sqrt capCancelBaseBudget) + 2) * (Nat.sqrt m + 1) ≤ N :=
      (Nat.mul_le_mul_right _ hK_ge).trans hN
    have hc : Real.sqrt capCancelBaseBudget <
        ((Nat.ceil (Real.sqrt capCancelBaseBudget) + 2 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (Real.sqrt capCancelBaseBudget)]
    have hc_sq : capCancelBaseBudget <
        ((Nat.ceil (Real.sqrt capCancelBaseBudget) + 2 : ℕ) : ℝ) ^ 2 := by
      conv_lhs => rw [← Real.sq_sqrt capCancelBaseBudget_pos.le]
      exact pow_lt_pow_left₀ hc (Real.sqrt_nonneg _) two_ne_zero
    have hmR : (m : ℝ) + 1 ≤ ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast Nat.lt_succ_sqrt' m
    have hmul : capCancelBaseBudget * ((m : ℝ) + 1) <
        ((Nat.ceil (Real.sqrt capCancelBaseBudget) + 2 : ℕ) : ℝ) ^ 2 *
          ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_right hc_sq (by positivity))
        (mul_le_mul_of_nonneg_left hmR (by positivity))
    have hNR : ((Nat.ceil (Real.sqrt capCancelBaseBudget) + 2 : ℕ) : ℝ) ^ 2 *
        ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by
      rw [← mul_pow]
      have hleR : ((Nat.ceil (Real.sqrt capCancelBaseBudget) + 2 : ℕ) : ℝ) *
          ((Nat.sqrt m + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        exact_mod_cast (hsq_nat.trans (Nat.le_succ N))
      exact pow_le_pow_left₀ (by positivity) hleR 2
    exact hmul.trans_le hNR
  have htail : thetaStripTailBound N <
      burnolGoodLowerConst * Real.exp (-((m + 3 : ℕ) : ℝ)) * (r / 8) ^ d := by
    set C₀ : ℝ := _root_.RHTower.thetaCuspIntegerTailConstant *
      _root_.RHTower.thetaAmplitudeEnvelope 2
    have hC₀ : 0 ≤ C₀ := mul_nonneg _root_.RHTower.thetaCuspIntegerTailConstant_nonneg
      (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2)
    have hcg : 0 < burnolGoodLowerConst := burnolGoodLowerConst_pos
    have hkey : Real.log (C₀ + 1) - ((N + 1 : ℕ) : ℝ) ^ 2 <
        Real.log burnolGoodLowerConst - ((m + 3 : ℕ) : ℝ) - (d : ℝ) * Real.log (8 / r) := by
      have hL1 := le_abs_self (Real.log (C₀ + 1))
      have hL2 := neg_abs_le (Real.log burnolGoodLowerConst)
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hm3 : ((m + 3 : ℕ) : ℝ) ≤ 4 * ((m : ℝ) + 1) := by push_cast; linarith
      have hB_ge : |Real.log (C₀ + 1)| + |Real.log burnolGoodLowerConst| +
          4 * ((m : ℝ) + 1) + 180 * (burnolPrefixConst : ℝ) * ((m : ℝ) + 1) ≤
          capCancelBaseBudget * ((m : ℝ) + 1) := by
        unfold capCancelBaseBudget
        have ha : 0 ≤ |Real.log (C₀ + 1)| + |Real.log burnolGoodLowerConst| := by positivity
        nlinarith
      linarith
    have hpow : (r / 8) ^ d = Real.exp (-((d : ℝ) * Real.log (8 / r))) := by
      rw [show r / 8 = (8 / r)⁻¹ by field_simp,
        ← Real.exp_log (by positivity : (0 : ℝ) < ((8 / r)⁻¹) ^ d), Real.log_pow, Real.log_inv]
      congr 1; ring
    calc thetaStripTailBound N = C₀ * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) := rfl
      _ ≤ (C₀ + 1) * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = Real.exp (Real.log (C₀ + 1) - ((N + 1 : ℕ) : ℝ) ^ 2) := by
          rw [Real.exp_sub, Real.exp_log (by linarith), Real.exp_neg, div_eq_mul_inv]
      _ < Real.exp (Real.log burnolGoodLowerConst - ((m + 3 : ℕ) : ℝ) -
            (d : ℝ) * Real.log (8 / r)) := Real.exp_lt_exp.mpr hkey
      _ = burnolGoodLowerConst * Real.exp (-((m + 3 : ℕ) : ℝ)) * (r / 8) ^ d := by
          rw [hpow, Real.exp_sub, Real.exp_sub, Real.exp_log hcg, Real.exp_neg, Real.exp_neg,
            div_eq_mul_inv, div_eq_mul_inv]
  have hrect_nz : ∀ z ∈ Icc (burnolCapAbscissa m) (3 / 2) ×ℂ
      Icc (burnolUnitLower m) (burnolUnitUpper m),
      _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
    intro z hz hzero
    obtain ⟨⟨hx_lo, hx_hi⟩, ⟨hy_lo, hy_hi⟩⟩ := hz
    by_cases hedge : z.re = 3 / 2 ∨ z.im = burnolUnitLower m ∨ z.im = burnolUnitUpper m
    · exact edge_ne_zero_of_bdry_regular hy_le hbdry
        ⟨by linarith, hx_hi⟩ ⟨hy_lo, hy_hi⟩ (Or.inr hedge) hzero
    · push Not at hedge
      have hz_open : -1 / 2 < z.re ∧ z.re < 3 / 2 ∧
          burnolUnitLower m < z.im ∧ z.im < burnolUnitUpper m :=
        ⟨by linarith, lt_of_le_of_ne hx_hi hedge.1,
         lt_of_le_of_ne hy_lo hedge.2.1.symm, lt_of_le_of_ne hy_hi hedge.2.2⟩
      obtain ⟨w, hw_mem, hdist⟩ := exists_xiZero_near_thetaZero m N hr_pos htail hz_open hzero
      obtain ⟨⟨hw0, hw1, hwy_lo, hwy_hi⟩, hw_xi⟩ := (mem_burnolUnitXiZeros_iff m w).mp hw_mem
      have hw_ne1 : w ≠ 1 := fun h1 => by rw [h1] at hw1; simp at hw1
      have hw_zeta : riemannZeta w = 0 := (_root_.RHTower.xi_eq_zero_iff hw0 hw_ne1).mp hw_xi
      have hw4 : 4 ≤ |w.im| := _root_.RHTower.four_le_abs_im_of_zeta_zero hw0 hw1 hw_zeta
      have hw_dlvp := _root_.RHTower.re_le_one_sub_of_zeta_zero hw0 hw1 hw_zeta
      obtain ⟨hy₁_c, _, _, hy₂_c, _⟩ := burnolUnit_coords m
      have hw_im_le : |w.im| ≤ ((m + 5 : ℕ) : ℝ) := by
        rw [abs_le]
        constructor <;> (push_cast; linarith)
      have hlog_w_pos : 0 < Real.log |w.im| := by
        have hlog4 : 1 < Real.log 4 := by
          have h2 : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
          linarith [Real.log_two_gt_d9]
        exact lt_of_lt_of_le (zero_lt_one.trans hlog4) (Real.log_le_log (by norm_num) hw4)
      have hlog_w_le : Real.log |w.im| ≤ L := Real.log_le_log (by linarith) hw_im_le
      have hdlvp_m : w.re ≤ 1 - 1 / (58 * L) := by
        have h1 : 1 / (58 * L) ≤ 1 / 58 / Real.log |w.im| := by
          rw [div_div]
          exact div_le_div_of_nonneg_left zero_le_one (by positivity)
            (mul_le_mul_of_nonneg_left hlog_w_le (by norm_num))
        linarith
      have hre_diff : z.re - w.re ≤ r :=
        (le_abs_self _).trans ((Complex.abs_re_le_norm (z - w)).trans hdist)
      have hcontra : z.re < burnolCapAbscissa m := by
        unfold burnolCapAbscissa
        rw [← hL_def]
        have halg : 1 - 1 / (58 * L) + 1 / (232 * L) =
            1 - 1 / (116 * L) - 1 / (232 * L) := by
          field_simp [show L ≠ 0 by linarith]; ring
        have hpos_r : 0 < 1 / (232 * L) := hr_pos
        linarith [hdlvp_m, hre_diff, halg]
      linarith
  exact ⟨hσ_lo, hσ_hi, hσ_sub, hrect_nz,
    exists_norm_rightEdgeFlux_add_horizCapFlux_le (by linarith) hy_le N hrect_nz⟩


/-! ## §2 Subexponential window energy characterization and quadratic-horizon vanishing -/

/-- **5-way window-local subexponential energy characterization (`List.TFAE`).**
On any boundary-regular centered window `[-1/2, 3/2] × [y₁, y₂]` (`y₁ ≤ y₂`), pointwise
subexponential growth of `|𝒵_N(t)|²`, Laplace integrability against `e^{-xt}` (`∀ x > 0`),
pointwise subexponential growth of the right half-port `|𝒫_+(t)|²`, critical-line purity of `A_N`
inside the window, and strip-contained stage-uniform Szegő certificate positivity (`∀ n ≥ 6`) are
unconditionally equivalent. -/
theorem subexp_windowEnergy_tfae {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
    (hbdry : ∀ τ : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) τ) ≠ 0) :
    [ -- 1. Subexponential pointwise growth of `|𝒵_N(t)|²`:
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
        ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2 ≤ C * Real.exp (ε * t),
      -- 2. Subexponential Laplace integrability of `|𝒵_N(t)|²`:
      ∀ x : ℝ, 0 < x →
        IntegrableOn (fun t : ℝ => Real.exp (-(x * t)) * ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2)
          (Ioi (0 : ℝ)),
      -- 3. Subexponential pointwise growth of the right half-port `|𝒫_+(t)|²`:
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
        ‖rightHalfPort y₁ y₂ N t‖ ^ 2 ≤ C * Real.exp (ε * t),
      -- 4. Local critical-line purity of `A_N` inside `(-1/2, 3/2) × (y₁, y₂)`:
      ∀ z : ℂ, -1 / 2 < z.re → z.re < 3 / 2 → y₁ < z.im → z.im < y₂ →
        _root_.RHTower.finiteThetaAmplitude N z = 0 → z.re = 1 / 2,
      -- 5. Strip containment plus stage-uniform circle-nonvanishing, Fredholm index `0`, and
      --    explicit Bessel–Szegő certificate positivity across all `n ≥ 6`:
      (∀ z ∈ (centeredThetaWindow hy N hbdry).Z, z.re < 1) ∧
      ∀ n : ℕ, 6 ≤ n →
        (∀ u : HTGeometry.UnitCircle, centeredThetaLaurentLoop y₁ y₂ n N u ≠ 0) ∧
        HTGeometry.fredholmIndex (centeredThetaCollisionOperator y₁ y₂ n N) = 0 ∧
        (∀ K : ℕ,
          2 * (centeredThetaWindowDegree y₁ y₂ N : ℝ) ^ 2 *
              (1 - 1 / (4 * (n : ℝ))) ^ (K + 1) / (1 / (4 * (n : ℝ))) < Real.pi / 2 →
          ∀ u : HTGeometry.UnitCircle,
            0 < (besselSzegoCertificate n K (fun t => ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2) u *
              centeredThetaLaurentLoop y₁ y₂ n N u).re)
    ].TFAE := by
  set W := centeredThetaWindow hy N hbdry
  tfae_have 1 → 2 := by
    intro h x hx
    obtain ⟨C, hC, hbd⟩ := h (x / 2) (half_pos hx)
    have hdom : IntegrableOn (fun t : ℝ => C * Real.exp (-(x / 2) * t)) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by linarith : -(x / 2) < 0) 0).const_mul C
    have hcont_Z : Continuous (centeredThetaExpSum y₁ y₂ N) := by
      have heq : centeredThetaExpSum y₁ y₂ N = fun t => W.expSum t :=
        funext fun t => (centeredThetaWindow_expSum hy N hbdry t).symm
      rw [heq]; exact W.continuous_expSum
    refine hdom.mono'
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (hcont_Z.norm.pow 2)).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    calc Real.exp (-(x * t)) * ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2
        ≤ Real.exp (-(x * t)) * (C * Real.exp ((x / 2) * t)) :=
          mul_le_mul_of_nonneg_left (hbd t ht0) (Real.exp_pos _).le
      _ = C * (Real.exp (-(x * t)) * Real.exp ((x / 2) * t)) := by ring
      _ = C * Real.exp (-(x / 2) * t) := by rw [← Real.exp_add]; congr 2; ring
  tfae_have 2 → 4 := by
    intro h z hx1 hx2 hy1 hy2 hz0
    have hzW : z ∈ W.Z := (mem_centeredThetaWindow_iff hy N hbdry z).mpr ⟨⟨hx1, hx2, hy1, hy2⟩, hz0⟩
    by_contra hne
    set z₁ : ℂ := if 1 / 2 < z.re then z else 1 - star z
    have hz₁_W : z₁ ∈ W.Z := by
      dsimp only [z₁]; split_ifs
      · exact hzW
      · exact W.refl_mem z hzW
    have hz₁_pos : 0 < z₁.re - 1 / 2 := by
      dsimp only [z₁]; split_ifs with hgt
      · linarith
      · have hlt : z.re < 1 / 2 := lt_of_le_of_ne (not_lt.mp hgt) hne
        simp; linarith
    obtain ⟨z₀, hz₀_W, hmax⟩ := Finset.exists_max_image W.Z (fun w => w.re - 1 / 2) ⟨z₁, hz₁_W⟩
    set δ : ℝ := z₀.re - 1 / 2
    have hδ_pos : 0 < δ := lt_of_lt_of_le hz₁_pos (hmax z₁ hz₁_W)
    have hint_W : IntegrableOn (fun t : ℝ => Real.exp (-(δ * t)) * ‖W.expSum t‖ ^ 2) (Ioi 0) := by
      have heq : (fun t : ℝ => Real.exp (-(δ * t)) * ‖W.expSum t‖ ^ 2) =
          fun t => Real.exp (-(δ * t)) * ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2 :=
        funext fun t => by rw [centeredThetaWindow_expSum]
      rw [heq]
      exact h δ hδ_pos
    have h2δ := W.lt_of_integrableOn_energy hmax hz₀_W rfl hint_W
    linarith
  tfae_have 4 → 3 := by
    intro hpure ε hε
    set σ₁ : ℝ := min 1 (1 / 2 + ε / 4)
    have hσ₁_gt : 1 / 2 < σ₁ := lt_min (by norm_num) (by linarith)
    have hσ₁_le1 : σ₁ ≤ 1 := min_le_left _ _
    have hσ₁_eps : σ₁ - 1 / 2 ≤ ε / 4 := by
      have := min_le_right 1 (1 / 2 + ε / 4); linarith
    have hrect_nz : ∀ z ∈ Icc σ₁ (3 / 2) ×ℂ Icc y₁ y₂,
        _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
      intro z ⟨⟨hzx1, hzx2⟩, ⟨hzy1, hzy2⟩⟩ hz0
      by_cases hedge : z.re = 3 / 2 ∨ z.im = y₁ ∨ z.im = y₂
      · exact edge_ne_zero_of_bdry_regular hy hbdry
          ⟨by linarith, hzx2⟩ ⟨hzy1, hzy2⟩ (Or.inr hedge) hz0
      · push Not at hedge
        have hre := hpure z (by linarith) (lt_of_le_of_ne hzx2 hedge.1)
          (lt_of_le_of_ne hzy1 hedge.2.1.symm) (lt_of_le_of_ne hzy2 hedge.2.2) hz0
        linarith
    obtain ⟨M₁, hM₁, hbd₁⟩ := exists_norm_rightEdgeFlux_add_horizCapFlux_le
      (by linarith : σ₁ ≤ 3 / 2) hy N hrect_nz
    have hnz_h₁ : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
        _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₁ : ℂ) * I) ≠ 0 := fun x hx =>
      edge_ne_zero_of_bdry_regular hy hbdry ⟨by simp; linarith [hx.1], by simpa using hx.2⟩
        ⟨by simp, by simpa using hy⟩ (Or.inr (Or.inr (Or.inl (by simp))))
    have hnz_h₂ : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
        _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₂ : ℂ) * I) ≠ 0 := fun x hx =>
      edge_ne_zero_of_bdry_regular hy hbdry ⟨by simp; linarith [hx.1], by simpa using hx.2⟩
        ⟨by simpa using hy, by simp⟩ (Or.inr (Or.inr (Or.inr (by simp))))
    have hcont₁ : ContinuousOn (fun x : ℝ => thetaLogDeriv N ((x : ℂ) + (y₁ : ℂ) * I))
        (Icc (1 / 2) σ₁) := fun x hx => by
      have h1 : ContinuousAt (thetaLogDeriv N) ((x : ℂ) + (y₁ : ℂ) * I) :=
        (analyticAt_thetaLogDeriv (hnz_h₁ x ⟨hx.1, hx.2.trans (by linarith)⟩)).continuousAt
      have h2 : ContinuousAt (fun u : ℝ => (u : ℂ) + (y₁ : ℂ) * I) x :=
        (by fun_prop : Continuous fun u : ℝ => (u : ℂ) + (y₁ : ℂ) * I).continuousAt
      exact (ContinuousAt.comp (g := thetaLogDeriv N)
        (f := fun u : ℝ => (u : ℂ) + (y₁ : ℂ) * I) h1 h2).continuousWithinAt
    have hcont₂ : ContinuousOn (fun x : ℝ => thetaLogDeriv N ((x : ℂ) + (y₂ : ℂ) * I))
        (Icc (1 / 2) σ₁) := fun x hx => by
      have h1 : ContinuousAt (thetaLogDeriv N) ((x : ℂ) + (y₂ : ℂ) * I) :=
        (analyticAt_thetaLogDeriv (hnz_h₂ x ⟨hx.1, hx.2.trans (by linarith)⟩)).continuousAt
      have h2 : ContinuousAt (fun u : ℝ => (u : ℂ) + (y₂ : ℂ) * I) x :=
        (by fun_prop : Continuous fun u : ℝ => (u : ℂ) + (y₂ : ℂ) * I).continuousAt
      exact (ContinuousAt.comp (g := thetaLogDeriv N)
        (f := fun u : ℝ => (u : ℂ) + (y₂ : ℂ) * I) h1 h2).continuousWithinAt
    obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont₁
    obtain ⟨B₂, hB₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont₂
    set B := max (max B₁ B₂) 1
    have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    set M₂ : ℝ := (2 * Real.pi)⁻¹ * (2 * B)
    have hM₂_pos : 0 < M₂ := by dsimp only [M₂]; positivity
    refine ⟨(M₁ + M₂) ^ 2, by positivity, fun t ht => ?_⟩
    have hcap_split : rightHalfPort y₁ y₂ N t =
        (rightEdgeFlux y₁ y₂ N t + horizCapFlux σ₁ (3 / 2) y₁ y₂ N t) +
          horizCapFlux (1 / 2) σ₁ y₁ y₂ N t := by
      unfold rightHalfPort
      rw [horizCapFlux_add_adjacent (b := σ₁) hσ₁_gt.le (by linarith) N hnz_h₁ hnz_h₂ t]
      ring
    have hcap_short : ‖horizCapFlux (1 / 2) σ₁ y₁ y₂ N t‖ ≤ M₂ * Real.exp ((ε / 4) * t) := by
      have hseg_bd : ∀ (y : ℝ),
          (∀ x ∈ Icc (1 / 2) σ₁, ‖thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)‖ ≤ B) →
          ‖∫ x in (1 / 2 : ℝ)..σ₁, cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
              thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * Real.exp ((ε / 4) * t) := by
        intro y hyB
        have h1 : ‖∫ x in (1 / 2 : ℝ)..σ₁, cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
              thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)‖ ≤
            (B * Real.exp ((ε / 4) * t)) * |σ₁ - 1 / 2| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const' hσ₁_gt.le fun x hx => ?_
          rw [norm_mul, Complex.norm_exp]
          have hre : ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)).re = (x - 1 / 2) * t := by
            simp; ring
          rw [hre, mul_comm B]
          exact mul_le_mul
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
              ((sub_le_sub_right hx.2 _).trans hσ₁_eps) ht))
            (hyB x hx) (norm_nonneg _) (Real.exp_pos _).le
        rw [abs_of_nonneg (by linarith)] at h1
        have hlen : σ₁ - 1 / 2 ≤ 1 := by linarith
        exact h1.trans (mul_le_of_le_one_right (by positivity) hlen)
      unfold horizCapFlux
      rw [norm_mul, norm_inv, norm_mul, norm_I, mul_one, norm_mul, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      have hs1 := hseg_bd y₁ fun x hx => (hB₁ x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
      have hs2 := hseg_bd y₂ fun x hx => (hB₂ x hx).trans ((le_max_right _ _).trans (le_max_left _ _))
      calc (2 * Real.pi)⁻¹ * ‖_ - _‖
          ≤ (2 * Real.pi)⁻¹ * (B * Real.exp ((ε / 4) * t) + B * Real.exp ((ε / 4) * t)) :=
            mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hs1 hs2)) (by positivity)
        _ = M₂ * Real.exp ((ε / 4) * t) := by dsimp only [M₂]; ring
    have hport_bd : ‖rightHalfPort y₁ y₂ N t‖ ≤ (M₁ + M₂) * Real.exp ((ε / 4) * t) := by
      rw [hcap_split]
      have h1 : ‖rightEdgeFlux y₁ y₂ N t + horizCapFlux σ₁ (3 / 2) y₁ y₂ N t‖ ≤
          M₁ * Real.exp ((ε / 4) * t) :=
        (hbd₁ t).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσ₁_eps ht)) hM₁.le)
      calc ‖_ + _‖ ≤ _ + _ := norm_add_le _ _
        _ ≤ M₁ * Real.exp ((ε / 4) * t) + M₂ * Real.exp ((ε / 4) * t) := add_le_add h1 hcap_short
        _ = (M₁ + M₂) * Real.exp ((ε / 4) * t) := by ring
    calc ‖rightHalfPort y₁ y₂ N t‖ ^ 2
        ≤ ((M₁ + M₂) * Real.exp ((ε / 4) * t)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hport_bd 2
      _ = (M₁ + M₂) ^ 2 * Real.exp ((ε / 2) * t) := by
          rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; congr 2; ring
      _ ≤ (M₁ + M₂) ^ 2 * Real.exp (ε * t) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) ht)) (by positivity)
  tfae_have 3 → 2 := by
    intro h x hx
    rw [integrableOn_windowEnergy_iff_rightHalfPort hy N hbdry hx.le]
    obtain ⟨C, hC, hbd⟩ := h (x / 2) (half_pos hx)
    have hdom : IntegrableOn (fun t : ℝ => C * Real.exp (-(x / 2) * t)) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by linarith : -(x / 2) < 0) 0).const_mul C
    have hcont_right : Continuous (rightHalfPort y₁ y₂ N) := by
      unfold rightHalfPort rightEdgeFlux
      refine (continuous_vertFlux_of_ne_zero hy fun y hy_m =>
        edge_ne_zero_of_bdry_regular hy hbdry ⟨by simp; norm_num, by simp⟩
          ⟨by simpa using hy_m.1, by simpa using hy_m.2⟩ (Or.inr (Or.inl (by simp)))).add
        (continuous_horizCapFlux_of_ne_zero (by norm_num)
          (fun u hu => edge_ne_zero_of_bdry_regular hy hbdry
            ⟨by simp; linarith [hu.1], by simpa using hu.2⟩ ⟨by simp, by simpa using hy⟩
            (Or.inr (Or.inr (Or.inl (by simp)))))
          (fun u hu => edge_ne_zero_of_bdry_regular hy hbdry
            ⟨by simp; linarith [hu.1], by simpa using hu.2⟩ ⟨by simpa using hy, by simp⟩
            (Or.inr (Or.inr (Or.inr (by simp))))))
    refine hdom.mono'
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (hcont_right.norm.pow 2)).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    calc Real.exp (-(x * t)) * ‖rightHalfPort y₁ y₂ N t‖ ^ 2
        ≤ Real.exp (-(x * t)) * (C * Real.exp ((x / 2) * t)) :=
          mul_le_mul_of_nonneg_left (hbd t ht0) (Real.exp_pos _).le
      _ = C * (Real.exp (-(x * t)) * Real.exp ((x / 2) * t)) := by ring
      _ = C * Real.exp (-(x / 2) * t) := by rw [← Real.exp_add]; congr 2; ring
  tfae_have 4 → 1 := by
    intro hpure ε hε
    have hδ0 : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ 0 := fun z hz => by
      obtain ⟨⟨hx1, hx2, hy1, hy2⟩, hz0⟩ := (mem_centeredThetaWindow_iff hy N hbdry z).mp hz
      rw [hpure z hx1 hx2 hy1 hy2 hz0]; norm_num
    refine ⟨(W.degree : ℝ) ^ 2 + 1, by positivity, fun t ht => ?_⟩
    have hnorm := W.norm_expSum_le hδ0 ht
    rw [zero_mul, Real.exp_zero, mul_one, centeredThetaWindow_expSum hy N hbdry t] at hnorm
    have hsq : ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2 ≤ (W.degree : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hexp1 : 1 ≤ Real.exp (ε * t) := Real.one_le_exp (mul_nonneg hε.le ht)
    calc ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2
        ≤ ((W.degree : ℝ) ^ 2 + 1) * 1 := by linarith
      _ ≤ ((W.degree : ℝ) ^ 2 + 1) * Real.exp (ε * t) :=
          mul_le_mul_of_nonneg_left hexp1 (by positivity)
  tfae_have 4 → 5 := by
    intro hpure
    have hre_half : ∀ z ∈ W.Z, z.re = 1 / 2 := fun z hz => by
      obtain ⟨⟨hx1, hx2, hy1, hy2⟩, hz0⟩ := (mem_centeredThetaWindow_iff hy N hbdry z).mp hz
      exact hpure z hx1 hx2 hy1 hy2 hz0
    refine ⟨fun z hz => by rw [hre_half z hz]; norm_num, fun n hn6 => ?_⟩
    have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn6
    have hη : 0 < 1 / (4 * (n : ℝ)) := by positivity
    have hη2 : 1 / (4 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hcorr : W.InCorridor n (1 / (4 * (n : ℝ))) := by
      intro z hz
      rw [hre_half z hz, zhukovskyMajorAxis_of_six_le hn6]
      have halg : 1 / 2 - (1 / 2 - 1 / (2 * (n : ℝ))) - 1 / (4 * (n : ℝ)) =
          1 / (4 * (n : ℝ)) := by ring
      linarith
    have heval := eval_centeredThetaDifferencePoly_eq_window hy N hbdry
    have hK0 := exists_certificate_order (centeredThetaWindowDegree y₁ y₂ N : ℝ) _ hη (by linarith)
    obtain ⟨K₀, hK₀_lt⟩ := hK0
    have hcert : ∀ K : ℕ,
        2 * (centeredThetaWindowDegree y₁ y₂ N : ℝ) ^ 2 *
            (1 - 1 / (4 * (n : ℝ))) ^ (K + 1) / (1 / (4 * (n : ℝ))) < Real.pi / 2 →
        ∀ u : HTGeometry.UnitCircle,
          0 < (besselSzegoCertificate n K (fun t => ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2) u *
            centeredThetaLaurentLoop y₁ y₂ n N u).re := by
      intro K hK u
      rw [← centeredThetaWindow_degree hy N hbdry] at hK
      have hpos := hcorr.besselSzegoCertificate_mul_loop_pos heval hη hη2 hK u
      have hE : (fun t => ‖W.expSum t‖ ^ 2) = fun t => ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2 :=
        funext fun t => by rw [centeredThetaWindow_expSum]
      rwa [hE] at hpos
    obtain ⟨hnz, hind₀⟩ := fredholmIndex_eq_zero_of_diskUnit_re_pos _
      (isDiskUnit_besselSzegoCertificate n K₀ _) (hcert K₀ hK₀_lt)
    exact ⟨hnz, hind₀, hcert⟩
  tfae_have 5 → 4 := by
    rintro ⟨hstrip, hstage⟩ z hx1 hx2 hy1 hy2 hz0
    have hzW : z ∈ W.Z := (mem_centeredThetaWindow_iff hy N hbdry z).mpr ⟨⟨hx1, hx2, hy1, hy2⟩, hz0⟩
    by_contra hne
    set z₀ : ℂ := if 1 / 2 < z.re then z else 1 - star z
    have hz₀_W : z₀ ∈ W.Z := by
      dsimp only [z₀]; split_ifs
      · exact hzW
      · exact W.refl_mem z hzW
    have hz₀_gt : 1 / 2 < z₀.re := by
      dsimp only [z₀]; split_ifs with hgt
      · exact hgt
      · have hlt : z.re < 1 / 2 := lt_of_le_of_ne (not_lt.mp hgt) hne
        simp; linarith
    have hz₀_lt1 : z₀.re < 1 := hstrip z₀ hz₀_W
    set μ : ℝ := min (2 * (z₀.re - 1 / 2)) (1 - 2 * (z₀.re - 1 / 2))
    have hμ_pos : 0 < μ := lt_min (by linarith) (by linarith)
    set n : ℕ := max 6 (Nat.ceil (1 / μ) + 1)
    have hn6 : 6 ≤ n := le_max_left _ _
    obtain ⟨hnz, hind₀, _⟩ := hstage n hn6
    have hgap : 1 / (2 * (n : ℝ)) < μ := by
      have hn_gt : 1 / μ < (n : ℝ) := by
        calc 1 / μ ≤ (Nat.ceil (1 / μ) : ℝ) := Nat.le_ceil _
          _ < ((Nat.ceil (1 / μ) + 1 : ℕ) : ℝ) := by push_cast; linarith
          _ ≤ (n : ℝ) := by exact_mod_cast le_max_right 6 _
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have h1 : 1 / (n : ℝ) < μ := (div_lt_iff₀ hn_pos).mpr
        (by have := (div_lt_iff₀ hμ_pos).mp hn_gt; linarith)
      exact (div_le_div_of_nonneg_left zero_le_one hn_pos (by linarith)).trans_lt h1
    have hlo : 1 / 2 - zhukovskyMajorAxis n < 2 * (z₀.re - 1 / 2) := by
      rw [zhukovskyMajorAxis_of_six_le hn6]
      linarith [hgap, min_le_left (2 * (z₀.re - 1 / 2)) (1 - 2 * (z₀.re - 1 / 2))]
    have hhi : 2 * (z₀.re - 1 / 2) < 1 / 2 + zhukovskyMajorAxis n := by
      rw [zhukovskyMajorAxis_of_six_le hn6]
      linarith [hgap, min_le_right (2 * (z₀.re - 1 / 2)) (1 - 2 * (z₀.re - 1 / 2))]
    have hnz_sq : ∀ u : HTGeometry.UnitCircle,
        ((centeredThetaDifferencePoly y₁ y₂ N).eval (zhukovskyLoop n u)) ^ 2 ≠ 0 :=
      fun u => by simpa only [centeredThetaLaurentLoop, polyZhukovskyLaurentLoop_apply] using hnz u
    have hge2 := W.two_le_fredholmIndex_of_gap_lt_two_mul_depth
      (eval_centeredThetaDifferencePoly_eq_window hy N hbdry) hnz_sq hz₀_W hlo hhi
    change 2 ≤ HTGeometry.fredholmIndex (centeredThetaCollisionOperator y₁ y₂ n N) at hge2
    omega
  tfae_finish

/-- **Identical vanishing of `𝒵_N(t)` above the quadratic horizon despite infinitely many wide
off-line zeros.** There exists `C_hor ≥ 1` such that for every `N : ℕ`:
- `finiteThetaAmplitude N` has infinitely many off-line zeros outside `|Re z - 1/2| ≤ 1`, yet
- for every window `[y₁, y₂]` above `C_hor * (N + 2)²` (or below `-C_hor * (N + 2)²`),
  `centeredThetaExpSum y₁ y₂ N t = 0` for all `t : ℝ`. -/
theorem centeredThetaExpSum_eq_zero_above_quadratic_horizon :
    ∃ C_hor : ℝ, 1 ≤ C_hor ∧ ∀ N : ℕ,
      {z : ℂ | _root_.RHTower.finiteThetaAmplitude N z = 0 ∧ 1 < |z.re - 1 / 2|}.Infinite ∧
      ∀ (y₁ y₂ : ℝ), y₁ ≤ y₂ →
        (C_hor * ((N + 2 : ℕ) : ℝ) ^ 2 ≤ y₁ ∨ y₂ ≤ -(C_hor * ((N + 2 : ℕ) : ℝ) ^ 2)) →
        ∀ t : ℝ, centeredThetaExpSum y₁ y₂ N t = 0 := by
  obtain ⟨C_hor, hC1, hhor⟩ := finiteThetaAmplitude_ne_zero_above_quadratic_horizon
  refine ⟨C_hor, hC1, fun N => ⟨finiteThetaAmplitude_offline_zeros_outside_strip_infinite N 1, ?_⟩⟩
  intro y₁ y₂ hy hheight t
  set g : ℂ → ℂ := fun z => cexp ((t : ℂ) * (z - 1 / 2)) *
    (-_root_.RHTower.finiteThetaFirstMoment N z / _root_.RHTower.finiteThetaAmplitude N z)
  set U : Set ℂ := {z : ℂ | _root_.RHTower.finiteThetaAmplitude N z ≠ 0}
  have hg_an : AnalyticOnNhd ℂ g U := fun z hz =>
    ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).cexp).mul
      (analyticAt_thetaLogDeriv hz)
  have hsub : (uIcc (centeredWindowLowerLeft y₁).re (centeredWindowUpperRight y₂).re ×ℂ
      uIcc (centeredWindowLowerLeft y₁).im (centeredWindowUpperRight y₂).im) ⊆ U := by
    intro z ⟨hzx, hzy⟩
    have hl_re : (centeredWindowLowerLeft y₁).re = -1 / 2 := by simp [centeredWindowLowerLeft]
    have hu_re : (centeredWindowUpperRight y₂).re = 3 / 2 := by simp [centeredWindowUpperRight]
    have hl_im : (centeredWindowLowerLeft y₁).im = y₁ := by simp [centeredWindowLowerLeft]
    have hu_im : (centeredWindowUpperRight y₂).im = y₂ := by simp [centeredWindowUpperRight]
    rw [hl_re, hu_re, uIcc_of_le (by norm_num)] at hzx
    rw [hl_im, hu_im, uIcc_of_le hy] at hzy
    have hre1 : |z.re - 1 / 2| ≤ 1 := abs_le.mpr ⟨by linarith [hzx.1], by linarith [hzx.2]⟩
    have him_ge : C_hor * ((N + 2 : ℕ) : ℝ) ^ 2 ≤ |z.im| := by
      rcases hheight with hlo | hhi
      · exact (hlo.trans hzy.1).trans (le_abs_self _)
      · have : C_hor * ((N + 2 : ℕ) : ℝ) ^ 2 ≤ -z.im := by linarith [hzy.2, hhi]
        exact this.trans (neg_le_abs _)
    exact (hhor N z hre1 him_ge).2
  unfold centeredThetaExpSum
  rw [_root_.RHTower.rectIntegral_eq_zero_of_analyticOnNhd hsub hg_an, mul_zero]


/-! ## §3 Polynomial-stage `Θ_k(√m)`-prefix `RH` equivalence and fixed-degree corridor equivalence -/

private lemma sq_log_add_six_le_fifty_mul_sqrt (m : ℕ) :
    (Real.log ((m + 6 : ℕ) : ℝ)) ^ 2 ≤ 50 * ((Nat.sqrt m + 1 : ℕ) : ℝ) := by
  set s : ℕ := Nat.sqrt m + 1
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (Nat.succ_pos (Nat.sqrt m))
  have hm_sq : m + 1 ≤ s ^ 2 := Nat.lt_succ_sqrt' m
  have hm6_le : ((m + 6 : ℕ) : ℝ) ≤ 6 * (s : ℝ) ^ 2 := by
    have hmR : (m : ℝ) + 1 ≤ (s : ℝ) ^ 2 := by exact_mod_cast hm_sq
    have hs_sq1 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := one_le_pow₀ hs1
    push_cast; linarith
  have hlog6 : Real.log 6 ≤ 3 := by
    have h6_8 : (6 : ℝ) ≤ 2 ^ (3 : ℕ) := by norm_num
    have hln2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
    calc Real.log 6 ≤ Real.log ((2 : ℝ) ^ (3 : ℕ)) := Real.log_le_log (by norm_num) h6_8
      _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 3 := by linarith
  have hL_le : Real.log ((m + 6 : ℕ) : ℝ) ≤ 3 + 2 * Real.log (s : ℝ) := by
    calc Real.log ((m + 6 : ℕ) : ℝ)
        ≤ Real.log (6 * (s : ℝ) ^ 2) := Real.log_le_log (by positivity) hm6_le
      _ = Real.log 6 + Real.log ((s : ℝ) ^ 2) := Real.log_mul (by norm_num) (by positivity)
      _ = Real.log 6 + 2 * Real.log (s : ℝ) := by rw [Real.log_pow]; ring
      _ ≤ 3 + 2 * Real.log (s : ℝ) := by linarith
  have hL_nn : 0 ≤ Real.log ((m + 6 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 6 by omega))
  have hsq_s := sq_log_le_four_mul hs1
  calc (Real.log ((m + 6 : ℕ) : ℝ)) ^ 2
      ≤ (3 + 2 * Real.log (s : ℝ)) ^ 2 := pow_le_pow_left₀ hL_nn hL_le 2
    _ ≤ 2 * 3 ^ 2 + 2 * (2 * Real.log (s : ℝ)) ^ 2 := by
        nlinarith [sq_nonneg (3 - 2 * Real.log (s : ℝ))]
    _ = 18 + 8 * (Real.log (s : ℝ)) ^ 2 := by ring
    _ ≤ 18 + 8 * (4 * (s : ℝ)) := by linarith
    _ ≤ 50 * (s : ℝ) := by linarith

private def polyTransferCoeff (k : ℕ) : ℝ :=
  |Real.log (_root_.RHTower.thetaCuspIntegerTailConstant *
      _root_.RHTower.thetaAmplitudeEnvelope 2 + 1)| +
    |Real.log burnolGoodLowerConst| + 4 +
    50 * (burnolPrefixConst : ℝ) *
      (Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) + ((k + 1 : ℕ) : ℝ))

private lemma polyTransferCoeff_pos (k : ℕ) : 0 < polyTransferCoeff k := by
  unfold polyTransferCoeff
  have hlog : 0 ≤ Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) :=
    Real.log_nonneg (by linarith [sq_nonneg (burnolPrefixConst : ℝ)])
  positivity

/-- Explicit degree-`k` multiplier constant ensuring `polySqrtPrefix k m` dominates both
`capCancelSqrtPrefix m` and `besselUnitPrefix m S` for every `S ≤ (m + 6) ^ k`. -/
def polySqrtConst (k : ℕ) : ℕ :=
  max capCancelSqrtConst
    (burnolPrefixConst * (1 + 150 * (k + 6)) +
      Nat.ceil (Real.sqrt (polyTransferCoeff k)) + 3)

/-- Explicit `Θ_k(√m)` prefix schedule `polySqrtConst k * (Nat.sqrt m + 1)`. -/
def polySqrtPrefix (k m : ℕ) : ℕ :=
  polySqrtConst k * (Nat.sqrt m + 1)

theorem capCancelSqrtPrefix_le_polySqrtPrefix (k m : ℕ) :
    capCancelSqrtPrefix m ≤ polySqrtPrefix k m :=
  Nat.mul_le_mul_right _ (le_max_left _ _)

/-- **Polynomial-stage `Θ_k(√m)` prefix domination.**
For every degree `k : ℕ`, window index `m : ℕ`, and stage parameter `S ≤ (m + 6) ^ k`,
`besselUnitPrefix m S ≤ polySqrtPrefix k m`. -/
theorem besselUnitPrefix_le_polySqrtPrefix_of_le (k m : ℕ) {S : ℕ} (hS : S ≤ (m + 6) ^ k) :
    besselUnitPrefix m S ≤ polySqrtPrefix k m := by
  set s : ℕ := Nat.sqrt m + 1
  have hs1_nat : 1 ≤ s := Nat.succ_pos _
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1_nat
  set L : ℝ := Real.log ((m + 6 : ℕ) : ℝ)
  have hL_gt1 : 1 < L :=
    (one_lt_log_add_five m).trans_le
      (Real.log_le_log (by positivity) (by exact_mod_cast (show m + 5 ≤ m + 6 by omega)))
  have hL5_le : Real.log ((m + 5 : ℕ) : ℝ) ≤ L :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show m + 5 ≤ m + 6 by omega))
  have hL_sq : L ^ 2 ≤ 50 * (s : ℝ) := sq_log_add_six_le_fifty_mul_sqrt m
  have hm6_k1 : 6 ≤ ((m + 6 : ℕ) : ℝ) ^ (k + 1) := by
    calc (6 : ℝ) = (6 : ℝ) ^ 1 := (pow_one 6).symm
      _ ≤ ((m + 6 : ℕ) : ℝ) ^ 1 :=
          pow_le_pow_left₀ (by norm_num) (by exact_mod_cast (show 6 ≤ m + 6 by omega)) 1
      _ ≤ ((m + 6 : ℕ) : ℝ) ^ (k + 1) :=
          pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ m + 6 by omega)) (by omega)
  have hS6_le : ((S + 6 : ℕ) : ℝ) ≤ 7 * ((m + 6 : ℕ) : ℝ) ^ (k + 1) := by
    have hSR : (S : ℝ) ≤ ((m + 6 : ℕ) : ℝ) ^ k := by exact_mod_cast hS
    have hpow_le : ((m + 6 : ℕ) : ℝ) ^ k ≤ ((m + 6 : ℕ) : ℝ) ^ (k + 1) :=
      pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ m + 6 by omega)) (Nat.le_succ k)
    rw [Nat.cast_add S 6, Nat.cast_ofNat]; linarith
  have hlog7 : Real.log 7 ≤ 3 := by
    have h7_8 : (7 : ℝ) ≤ 2 ^ (3 : ℕ) := by norm_num
    have hln2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
    calc Real.log 7 ≤ Real.log ((2 : ℝ) ^ (3 : ℕ)) := Real.log_le_log (by norm_num) h7_8
      _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 3 := by linarith
  have hlog_S6 : Real.log ((S + 6 : ℕ) : ℝ) ≤ ((k + 4 : ℕ) : ℝ) * L := by
    calc Real.log ((S + 6 : ℕ) : ℝ)
        ≤ Real.log (7 * ((m + 6 : ℕ) : ℝ) ^ (k + 1)) := Real.log_le_log (by positivity) hS6_le
      _ = Real.log 7 + ((k + 1 : ℕ) : ℝ) * L := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      _ ≤ 3 * L + ((k + 1 : ℕ) : ℝ) * L := by nlinarith
      _ = ((k + 4 : ℕ) : ℝ) * L := by push_cast; ring
  -- Bound `doorUnitPrefix m S`.
  have hdoor_prod : (Nat.ceil (Real.log ((m + 5 : ℕ) : ℝ)) + 1) *
      (Nat.ceil (Real.sqrt (Real.log ((S + 6 : ℕ) : ℝ))) + 1) ≤ 150 * (k + 6) * s := by
    have h1 : ((Nat.ceil (Real.log ((m + 5 : ℕ) : ℝ)) + 1 : ℕ) : ℝ) ≤ 3 * L := by
      have hc := (Nat.ceil_lt_add_one (Real.log_nonneg
        (by exact_mod_cast (show 1 ≤ m + 5 by omega) : (1 : ℝ) ≤ ((m + 5 : ℕ) : ℝ)))).le
      rw [Nat.cast_add, Nat.cast_one]
      linarith
    have h2 : ((Nat.ceil (Real.sqrt (Real.log ((S + 6 : ℕ) : ℝ))) + 1 : ℕ) : ℝ) ≤
        ((k + 6 : ℕ) : ℝ) * L := by
      have hrt_le : Real.sqrt (Real.log ((S + 6 : ℕ) : ℝ)) ≤ ((k + 4 : ℕ) : ℝ) * L := by
        have hge1 : 1 ≤ ((k + 4 : ℕ) : ℝ) * L := by
          have hk1 : (1 : ℝ) ≤ ((k + 4 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k + 4 by omega)
          nlinarith
        calc Real.sqrt (Real.log ((S + 6 : ℕ) : ℝ))
            ≤ Real.sqrt (((k + 4 : ℕ) : ℝ) * L) := Real.sqrt_le_sqrt hlog_S6
          _ ≤ Real.sqrt ((((k + 4 : ℕ) : ℝ) * L) ^ 2) :=
              Real.sqrt_le_sqrt (by nlinarith)
          _ = ((k + 4 : ℕ) : ℝ) * L := Real.sqrt_sq (by positivity)
      have hc := (Nat.ceil_lt_add_one
        (Real.sqrt_nonneg (Real.log ((S + 6 : ℕ) : ℝ)))).le
      rw [Nat.cast_add, Nat.cast_one]
      have hk4_eq : ((k + 6 : ℕ) : ℝ) = ((k + 4 : ℕ) : ℝ) + 2 := by push_cast; ring
      rw [hk4_eq]
      linarith [hc, hrt_le, hL_gt1]
    have hmulR : (((Nat.ceil (Real.log ((m + 5 : ℕ) : ℝ)) + 1) *
        (Nat.ceil (Real.sqrt (Real.log ((S + 6 : ℕ) : ℝ))) + 1) : ℕ) : ℝ) ≤
        ((150 * (k + 6) * s : ℕ) : ℝ) := by
      push_cast
      have hp := mul_le_mul h1 h2 (by positivity) (by positivity)
      push_cast at hp
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [hp, hL_sq]
    exact_mod_cast hmulR
  have hdoor_le : doorUnitPrefix m S ≤ burnolPrefixConst * (1 + 150 * (k + 6)) * s := by
    unfold doorUnitPrefix
    have hinner : s + (Nat.ceil (Real.log ((m + 5 : ℕ) : ℝ)) + 1) *
        (Nat.ceil (Real.sqrt (Real.log ((S + 6 : ℕ) : ℝ))) + 1) ≤ (1 + 150 * (k + 6)) * s := by
      calc s + (Nat.ceil (Real.log ((m + 5 : ℕ) : ℝ)) + 1) *
              (Nat.ceil (Real.sqrt (Real.log ((S + 6 : ℕ) : ℝ))) + 1)
          ≤ s + 150 * (k + 6) * s := Nat.add_le_add_left hdoor_prod s
        _ = (1 + 150 * (k + 6)) * s := by ring
    calc burnolPrefixConst * (s + (Nat.ceil (Real.log ((m + 5 : ℕ) : ℝ)) + 1) *
            (Nat.ceil (Real.sqrt (Real.log ((S + 6 : ℕ) : ℝ))) + 1))
        ≤ burnolPrefixConst * ((1 + 150 * (k + 6)) * s) := Nat.mul_le_mul_left _ hinner
      _ = burnolPrefixConst * (1 + 150 * (k + 6)) * s := (Nat.mul_assoc _ _ _).symm
  -- Bound `besselTransferBudget m S`.
  have hbud_le : besselTransferBudget m S ≤ polyTransferCoeff k * (s : ℝ) ^ 2 := by
    have hm3 : ((m + 3 : ℕ) : ℝ) ≤ 4 * (s : ℝ) ^ 2 := by
      have hmR : (m : ℝ) + 1 ≤ (s : ℝ) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' m
      have hs_sq1 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := one_le_pow₀ hs1
      push_cast; linarith
    have hord_le : burnolOrderBound m ≤ (burnolPrefixConst : ℝ) * L :=
      mul_le_mul_of_nonneg_left hL5_le (Nat.cast_nonneg _)
    have hord_nn : 0 ≤ burnolOrderBound m := by
      unfold burnolOrderBound
      exact mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 5 by omega)))
    have hs_le_pow : (s : ℝ) ≤ ((m + 6 : ℕ) : ℝ) ^ (k + 1) := by
      have hs_m6 : s ≤ m + 6 := by
        have := Nat.sqrt_le_self m; omega
      have hs_m6R : (s : ℝ) ≤ ((m + 6 : ℕ) : ℝ) := by exact_mod_cast hs_m6
      calc (s : ℝ) ≤ ((m + 6 : ℕ) : ℝ) ^ 1 := by rwa [pow_one]
        _ ≤ ((m + 6 : ℕ) : ℝ) ^ (k + 1) :=
            pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ m + 6 by omega)) (by omega)
    have h2ord_sq : 2 * burnolOrderBound m ^ 2 ≤
        100 * (burnolPrefixConst : ℝ) ^ 2 * ((m + 6 : ℕ) : ℝ) ^ (k + 1) := by
      calc 2 * burnolOrderBound m ^ 2
          ≤ 2 * ((burnolPrefixConst : ℝ) * L) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hord_nn hord_le 2) zero_le_two
        _ = 2 * (burnolPrefixConst : ℝ) ^ 2 * L ^ 2 := by ring
        _ ≤ 2 * (burnolPrefixConst : ℝ) ^ 2 * (50 * (s : ℝ)) :=
            mul_le_mul_of_nonneg_left hL_sq (by positivity)
        _ = 100 * (burnolPrefixConst : ℝ) ^ 2 * (s : ℝ) := by ring
        _ ≤ 100 * (burnolPrefixConst : ℝ) ^ 2 * ((m + 6 : ℕ) : ℝ) ^ (k + 1) :=
            mul_le_mul_of_nonneg_left hs_le_pow (by positivity)
    have harg_le : 128 * ((S : ℝ) + 6 + 2 * burnolOrderBound m ^ 2) ≤
        (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) * ((m + 6 : ℕ) : ℝ) ^ (k + 1) := by
      have hS6R : (S : ℝ) + 6 = ((S + 6 : ℕ) : ℝ) := by push_cast; ring
      rw [hS6R]
      linarith [hS6_le, h2ord_sq]
    have hlog_arg : Real.log (128 * ((S : ℝ) + 6 + 2 * burnolOrderBound m ^ 2)) ≤
        (Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) + ((k + 1 : ℕ) : ℝ)) * L := by
      have hpos_arg : 0 < 128 * ((S : ℝ) + 6 + 2 * burnolOrderBound m ^ 2) := by positivity
      have hlogC_nn : 0 ≤ Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) :=
        Real.log_nonneg (by linarith [sq_nonneg (burnolPrefixConst : ℝ)])
      calc Real.log (128 * ((S : ℝ) + 6 + 2 * burnolOrderBound m ^ 2))
          ≤ Real.log ((128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) *
              ((m + 6 : ℕ) : ℝ) ^ (k + 1)) := Real.log_le_log hpos_arg harg_le
        _ = Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) +
              ((k + 1 : ℕ) : ℝ) * L := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        _ ≤ Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) * L +
              ((k + 1 : ℕ) : ℝ) * L := by nlinarith
        _ = (Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) +
              ((k + 1 : ℕ) : ℝ)) * L := by ring
    have hlog_arg_nn : 0 ≤ Real.log (128 * ((S : ℝ) + 6 + 2 * burnolOrderBound m ^ 2)) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg S : (0 : ℝ) ≤ S), sq_nonneg (burnolOrderBound m)])
    have hterm_le : burnolOrderBound m *
        Real.log (128 * ((S : ℝ) + 6 + 2 * burnolOrderBound m ^ 2)) ≤
        50 * (burnolPrefixConst : ℝ) *
          (Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) +
            ((k + 1 : ℕ) : ℝ)) * (s : ℝ) ^ 2 := by
      have hs_le_sq : (s : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
      have hC_nn : 0 ≤ (burnolPrefixConst : ℝ) *
          (Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) + ((k + 1 : ℕ) : ℝ)) := by
        have : 0 ≤ Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) :=
          Real.log_nonneg (by linarith [sq_nonneg (burnolPrefixConst : ℝ)])
        positivity
      calc burnolOrderBound m * Real.log (128 * ((S : ℝ) + 6 + 2 * burnolOrderBound m ^ 2))
          ≤ ((burnolPrefixConst : ℝ) * L) *
              ((Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) + ((k + 1 : ℕ) : ℝ)) * L) :=
            mul_le_mul hord_le hlog_arg hlog_arg_nn (by positivity)
        _ = ((burnolPrefixConst : ℝ) *
              (Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) + ((k + 1 : ℕ) : ℝ))) *
              L ^ 2 := by ring
        _ ≤ ((burnolPrefixConst : ℝ) *
              (Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) + ((k + 1 : ℕ) : ℝ))) *
              (50 * (s : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (hL_sq.trans (by linarith)) hC_nn
        _ = 50 * (burnolPrefixConst : ℝ) *
              (Real.log (128 * (7 + 100 * (burnolPrefixConst : ℝ) ^ 2)) +
                ((k + 1 : ℕ) : ℝ)) * (s : ℝ) ^ 2 := by ring
    unfold besselTransferBudget polyTransferCoeff
    have hs_sq1 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := one_le_pow₀ hs1
    have hbase_nn : 0 ≤ |Real.log (_root_.RHTower.thetaCuspIntegerTailConstant *
        _root_.RHTower.thetaAmplitudeEnvelope 2 + 1)| + |Real.log burnolGoodLowerConst| := by
      positivity
    nlinarith
  have hceil_bud : Nat.ceil (Real.sqrt (besselTransferBudget m S)) + 1 ≤
      (Nat.ceil (Real.sqrt (polyTransferCoeff k)) + 3) * s := by
    have hrt : Real.sqrt (besselTransferBudget m S) ≤
        Real.sqrt (polyTransferCoeff k) * (s : ℝ) := by
      calc Real.sqrt (besselTransferBudget m S)
          ≤ Real.sqrt (polyTransferCoeff k * (s : ℝ) ^ 2) := Real.sqrt_le_sqrt hbud_le
        _ = Real.sqrt (polyTransferCoeff k) * Real.sqrt ((s : ℝ) ^ 2) :=
            Real.sqrt_mul (polyTransferCoeff_pos k).le _
        _ = Real.sqrt (polyTransferCoeff k) * (s : ℝ) := by rw [Real.sqrt_sq (by positivity)]
    have hcR : ((Nat.ceil (Real.sqrt (besselTransferBudget m S)) + 1 : ℕ) : ℝ) ≤
        (((Nat.ceil (Real.sqrt (polyTransferCoeff k)) + 3) * s : ℕ) : ℝ) := by
      have hc1 := (Nat.ceil_lt_add_one (Real.sqrt_nonneg (besselTransferBudget m S))).le
      have hc2 := Nat.le_ceil (Real.sqrt (polyTransferCoeff k))
      push_cast
      nlinarith
    exact_mod_cast hcR
  unfold besselUnitPrefix polySqrtPrefix polySqrtConst
  calc doorUnitPrefix m S + Nat.ceil (Real.sqrt (besselTransferBudget m S)) + 1
      = doorUnitPrefix m S + (Nat.ceil (Real.sqrt (besselTransferBudget m S)) + 1) := by omega
    _ ≤ burnolPrefixConst * (1 + 150 * (k + 6)) * s +
          (Nat.ceil (Real.sqrt (polyTransferCoeff k)) + 3) * s := Nat.add_le_add hdoor_le hceil_bud
    _ = (burnolPrefixConst * (1 + 150 * (k + 6)) +
          Nat.ceil (Real.sqrt (polyTransferCoeff k)) + 3) * s := by ring
    _ ≤ max capCancelSqrtConst
          (burnolPrefixConst * (1 + 150 * (k + 6)) +
            Nat.ceil (Real.sqrt (polyTransferCoeff k)) + 3) * s :=
        Nat.mul_le_mul_right s (le_max_right _ _)

/-- **6-way unconditional `RiemannHypothesis` equivalence at polynomial stage and `Θ_k(√m)` prefix.**
Closes Obstacles A10 + B15 unconditionally: `RiemannHypothesis` holds iff across every polynomial
degree `k : ℕ`, every Burnol unit window `m : ℕ`, and every prefix `N ≥ polySqrtPrefix k m`, at the
polynomial stage `n_{k,m} = doorUnitStage m ((m + 6)^k)` both `|𝒵_N(t)|²` and the right half-port
`|𝒫_+(t)|²` are subexponential below the stage threshold `1 / (2 n_{k,m})`, the explicit
Bessel–Szegő certificate holds, and the Wiener–Hopf collision operator has Fredholm index `0`. -/
theorem riemannHypothesis_polynomialStage_tfae :
    [ -- 1. `RiemannHypothesis`:
      RiemannHypothesis,
      -- 2. Sub-stage-threshold pointwise growth `|𝒵_N(t)|² ≤ C exp(t / (4 n_{k,m}))`:
      ∀ k m : ℕ, ∀ N ≥ polySqrtPrefix k m,
        ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
          ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 ≤
            C * Real.exp ((1 / (4 * (doorUnitStage m ((m + 6) ^ k) : ℝ))) * t),
      -- 3. Sub-stage-threshold Laplace integrability of `|𝒵_N(t)|²`:
      ∀ k m : ℕ, ∀ N ≥ polySqrtPrefix k m,
        IntegrableOn
          (fun t : ℝ => Real.exp (-((1 / (2 * (doorUnitStage m ((m + 6) ^ k) : ℝ))) * t)) *
            ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
          (Ioi (0 : ℝ)),
      -- 4. Sub-stage-threshold Laplace integrability of the right half-port `|𝒫_+(t)|²`:
      ∀ k m : ℕ, ∀ N ≥ polySqrtPrefix k m,
        IntegrableOn
          (fun t : ℝ => Real.exp (-((1 / (2 * (doorUnitStage m ((m + 6) ^ k) : ℝ))) * t)) *
            ‖rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
          (Ioi (0 : ℝ)),
      -- 5. Explicit Bessel–Szegő certificate positivity at polynomial stage and `Θ_k(√m)` prefix:
      ∀ k m : ℕ, ∀ N ≥ polySqrtPrefix k m, ∀ K : ℕ,
        2 * (centeredThetaWindowDegree (burnolUnitLower m) (burnolUnitUpper m) N : ℝ) ^ 2 *
            (1 - 1 / (4 * (doorUnitStage m ((m + 6) ^ k) : ℝ))) ^ (K + 1) /
              (1 / (4 * (doorUnitStage m ((m + 6) ^ k) : ℝ))) < Real.pi / 2 →
        ∀ u : HTGeometry.UnitCircle,
          0 < (besselSzegoCertificate (doorUnitStage m ((m + 6) ^ k)) K
              (fun t => ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2) u *
            centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
              (doorUnitStage m ((m + 6) ^ k)) N u).re,
      -- 6. Circle-nonvanishing and vanishing Wiener–Hopf Fredholm index at polynomial stage:
      ∀ k m : ℕ, ∀ N ≥ polySqrtPrefix k m,
        (∀ u : HTGeometry.UnitCircle,
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
            (doorUnitStage m ((m + 6) ^ k)) N u ≠ 0) ∧
        HTGeometry.fredholmIndex
          (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
            (doorUnitStage m ((m + 6) ^ k)) N) = 0
    ].TFAE := by
  tfae_have 1 → 2 := by
    intro hRH k m N hN
    set S := (m + 6) ^ k
    have hNbessel := (besselUnitPrefix_le_polySqrtPrefix_of_le k m le_rfl).trans hN
    have hNdoor := (doorUnitPrefix_le_besselUnitPrefix m S).trans hNbessel
    have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_doorUnitPrefix m S).trans hNdoor)
    obtain ⟨hstage, -⟩ := doorUnitStage_spec m S
    set n := doorUnitStage m S
    have hn6 : 6 ≤ n := (le_max_right S 6).trans (Finset.mem_Icc.mp hstage).1
    have hn_le : (n : ℝ) ≤ (S : ℝ) + 6 + 2 * ((∑ w ∈ burnolUnitXiZeros m,
        (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ) ^ 2 := by
      have h := (Finset.mem_Icc.mp hstage).2
      have hmax : max S 6 ≤ S + 6 := max_le (by omega) (by omega)
      exact_mod_cast (show n ≤ S + 6 + 2 * (∑ w ∈ burnolUnitXiZeros m,
        (analyticOrderAt _root_.RHTower.xi w).toNat) ^ 2 by omega)
    have htail := unitStage_tail_lt m S hn6 hn_le hNbessel
    set W := centeredThetaWindow (burnolUnitLower_le_upper m) N hbdry
    have hδ : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ 1 / (8 * (n : ℝ)) := by
      intro z hz
      obtain ⟨hz_rect, hz_zero⟩ := (mem_centeredThetaWindow_iff _ N hbdry z).mp hz
      obtain ⟨w, hw, hdist⟩ := exists_xiZero_near_thetaZero m N (r := 1 / (16 * (n : ℝ)))
        (by positivity) htail hz_rect hz_zero
      have hw_xi := ((mem_burnolUnitXiZeros_iff m w).mp hw).2
      have hw_re := _root_.RHTower.xi_zero_re_eq_half_of_RH hRH hw_xi
      have hre_close : z.re - w.re ≤ 1 / (16 * (n : ℝ)) :=
        (le_abs_self _).trans ((Complex.abs_re_le_norm (z - w)).trans hdist)
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have : 0 < 1 / (16 * (n : ℝ)) := by positivity
      have halg : 1 / (8 * (n : ℝ)) = 2 * (1 / (16 * (n : ℝ))) := by ring
      linarith
    refine ⟨(W.degree : ℝ) ^ 2 + 1, by positivity, fun t ht => ?_⟩
    have hnorm := W.norm_expSum_le hδ ht
    rw [centeredThetaWindow_expSum (burnolUnitLower_le_upper m) N hbdry t] at hnorm
    calc ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2
        ≤ ((W.degree : ℝ) * Real.exp ((1 / (8 * (n : ℝ))) * t)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = (W.degree : ℝ) ^ 2 * Real.exp ((1 / (4 * (n : ℝ))) * t) := by
          rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; congr 2; ring
      _ ≤ ((W.degree : ℝ) ^ 2 + 1) * Real.exp ((1 / (4 * (n : ℝ))) * t) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  tfae_have 2 → 3 := by
    intro h k m N hN
    obtain ⟨C, hC, hbd⟩ := h k m N hN
    set n := doorUnitStage m ((m + 6) ^ k)
    have hn6 : 6 ≤ n :=
      (le_max_right ((m + 6) ^ k) 6).trans (Finset.mem_Icc.mp (doorUnitStage_spec m _).1).1
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hdom : IntegrableOn
        (fun t : ℝ => C * Real.exp (-(1 / (4 * (n : ℝ))) * t)) (Ioi (0 : ℝ)) := by
      have hneg : -(1 / (4 * (n : ℝ))) < 0 := neg_lt_zero.mpr (by positivity)
      exact (integrableOn_exp_mul_Ioi hneg 0).const_mul C
    have hbdry := burnolUnit_bdry_regular m
      ((burnolPrefix_le_capCancelSqrtPrefix m).trans
        ((capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN))
    have hcont_Z : Continuous (centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N) := by
      have heq : centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N =
          fun t => (centeredThetaWindow (burnolUnitLower_le_upper m) N hbdry).expSum t :=
        funext fun t => (centeredThetaWindow_expSum _ N hbdry t).symm
      rw [heq]; exact (centeredThetaWindow _ N hbdry).continuous_expSum
    refine hdom.mono'
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (hcont_Z.norm.pow 2)).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    calc Real.exp (-((1 / (2 * (n : ℝ))) * t)) *
            ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2
        ≤ Real.exp (-((1 / (2 * (n : ℝ))) * t)) *
            (C * Real.exp ((1 / (4 * (n : ℝ))) * t)) :=
          mul_le_mul_of_nonneg_left (hbd t ht0) (Real.exp_pos _).le
      _ = C * (Real.exp (-((1 / (2 * (n : ℝ))) * t)) * Real.exp ((1 / (4 * (n : ℝ))) * t)) := by ring
      _ = C * Real.exp (-(1 / (4 * (n : ℝ))) * t) := by rw [← Real.exp_add]; congr 2; ring
  tfae_have 3 ↔ 4 := by
    constructor <;> intro h k m N hN
    · have hbdry := burnolUnit_bdry_regular m
        ((burnolPrefix_le_capCancelSqrtPrefix m).trans
          ((capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN))
      exact (integrableOn_windowEnergy_iff_rightHalfPort
        (burnolUnitLower_le_upper m) N hbdry (by positivity)).mp (h k m N hN)
    · have hbdry := burnolUnit_bdry_regular m
        ((burnolPrefix_le_capCancelSqrtPrefix m).trans
          ((capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN))
      exact (integrableOn_windowEnergy_iff_rightHalfPort
        (burnolUnitLower_le_upper m) N hbdry (by positivity)).mpr (h k m N hN)
  tfae_have 1 → 5 := by
    intro hRH k m N hN
    exact riemannHypothesis_iff_unitStage_besselSzego.mp hRH m ((m + 6) ^ k) N
      ((besselUnitPrefix_le_polySqrtPrefix_of_le k m le_rfl).trans hN)
  tfae_have 5 → 6 := by
    intro hcert k m N hN
    set n := doorUnitStage m ((m + 6) ^ k)
    have hn6 : 6 ≤ n :=
      (le_max_right ((m + 6) ^ k) 6).trans (Finset.mem_Icc.mp (doorUnitStage_spec m _).1).1
    have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn6
    have hη : 0 < 1 / (4 * (n : ℝ)) := by positivity
    have hη1 : 1 / (4 * (n : ℝ)) < 1 := by rw [div_lt_one (by positivity)]; linarith
    obtain ⟨K, hK⟩ := exists_certificate_order
      (centeredThetaWindowDegree (burnolUnitLower m) (burnolUnitUpper m) N : ℝ) _ hη hη1
    exact fredholmIndex_eq_zero_of_diskUnit_re_pos _
      (isDiskUnit_besselSzegoCertificate n K _) (hcert k m N hN K hK)
  tfae_have 3 → 6 := by
    intro hint k m N hN
    set S := (m + 6) ^ k
    have hNbessel := (besselUnitPrefix_le_polySqrtPrefix_of_le k m le_rfl).trans hN
    have hNdoor := (doorUnitPrefix_le_besselUnitPrefix m S).trans hNbessel
    have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_doorUnitPrefix m S).trans hNdoor)
    obtain ⟨hstage, hspec⟩ := doorUnitStage_spec m S
    obtain ⟨hnz, _⟩ := hspec N hNdoor
    set n := doorUnitStage m S
    have hn6 : 6 ≤ n := (le_max_right S 6).trans (Finset.mem_Icc.mp hstage).1
    set W := centeredThetaWindow (burnolUnitLower_le_upper m) N hbdry
    have hint_W : IntegrableOn
        (fun t : ℝ => Real.exp (-((1 / 2 - zhukovskyMajorAxis n) * t)) * ‖W.expSum t‖ ^ 2)
        (Ioi 0) := by
      have hgap : 1 / 2 - zhukovskyMajorAxis n = 1 / (2 * (n : ℝ)) := by
        rw [zhukovskyMajorAxis_of_six_le hn6]; ring
      have heq : (fun t : ℝ => Real.exp (-((1 / 2 - zhukovskyMajorAxis n) * t)) * ‖W.expSum t‖ ^ 2) =
          fun t => Real.exp (-((1 / (2 * (doorUnitStage m ((m + 6) ^ k) : ℝ))) * t)) *
            ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 :=
        funext fun t => by rw [hgap, centeredThetaWindow_expSum]
      rw [heq]
      exact hint k m N hN
    exact ⟨hnz, W.fredholmIndex_eq_zero_of_integrableOn_energy
      (eval_centeredThetaDifferencePoly_eq_window (burnolUnitLower_le_upper m) N hbdry) hint_W⟩
  tfae_have 6 → 1 := by
    intro h
    rw [_root_.RHTower.rh_iff_forall_boxZeros_empty]
    intro U
    rw [Set.eq_empty_iff_forall_notMem]
    intro ρ hρ
    obtain ⟨⟨hr_lo, hr_hi, him_pos, _⟩, hxi_ρ⟩ := hρ
    set m : ℕ := Nat.floor ρ.im
    set δ_ρ : ℝ := min (ρ.re - 1 / 2) (1 - ρ.re)
    have hδ_pos : 0 < δ_ρ := lt_min (by linarith) (by linarith)
    -- Since `6 ≤ m + 6`, `(m + 6) ^ k ≥ 2 ^ k ≥ k` exceeds `⌈1 / δ_ρ⌉₊ + 6` for `k := ⌈1 / δ_ρ⌉₊ + 7`.
    set k : ℕ := Nat.ceil (1 / δ_ρ) + 7
    have hpow_ge : Nat.ceil (1 / δ_ρ) + 6 ≤ (m + 6) ^ k := by
      have hk_lt_2k : k < 2 ^ k := Nat.lt_two_pow_self
      have h2_le_m6 : 2 ^ k ≤ (m + 6) ^ k := Nat.pow_le_pow_left (by omega) k
      omega
    set S : ℕ := (m + 6) ^ k
    set N : ℕ := polySqrtPrefix k m
    have hNdoor : doorUnitPrefix m S ≤ N :=
      (doorUnitPrefix_le_besselUnitPrefix m S).trans
        (besselUnitPrefix_le_polySqrtPrefix_of_le k m le_rfl)
    obtain ⟨hn_Icc, hspec⟩ := doorUnitStage_spec m S
    obtain ⟨_, hind_sum⟩ := hspec N hNdoor
    have hind0 := (h k m N le_rfl).2
    have hn_ge_S : S ≤ doorUnitStage m S := (le_max_left S 6).trans (Finset.mem_Icc.mp hn_Icc).1
    have hn6 : 6 ≤ doorUnitStage m S := (le_max_right S 6).trans (Finset.mem_Icc.mp hn_Icc).1
    have hs_eq : (zhukovskyStage (doorUnitStage m S) : ℝ) = (doorUnitStage m S : ℝ) := by
      exact_mod_cast zhukovskyStage_eq_self hn6
    have hinv_lt : 1 / (4 * (zhukovskyStage (doorUnitStage m S) : ℝ)) < δ_ρ := by
      rw [hs_eq]
      have hS_gt : 1 / δ_ρ < (doorUnitStage m S : ℝ) := by
        calc 1 / δ_ρ ≤ (Nat.ceil (1 / δ_ρ) : ℝ) := Nat.le_ceil _
          _ < ((Nat.ceil (1 / δ_ρ) + 6 : ℕ) : ℝ) := by push_cast; linarith
          _ ≤ (doorUnitStage m S : ℝ) := by exact_mod_cast (hpow_ge.trans hn_ge_S)
      have hn_pos : (0 : ℝ) < (doorUnitStage m S : ℝ) := by
        exact_mod_cast (show 0 < doorUnitStage m S by omega)
      have h1 : 1 / (doorUnitStage m S : ℝ) < δ_ρ := (div_lt_iff₀ hn_pos).mpr
        (by have := (div_lt_iff₀ hδ_pos).mp hS_gt; linarith)
      exact (one_div_le_one_div_of_le hn_pos (by linarith)).trans_lt h1
    have hρ_unit : ρ ∈ xiUnitWindowZeros (m : ℝ) :=
      mem_xiUnitWindowZeros.mpr
        ⟨(_root_.RHTower.stripZeros_finite ((m : ℝ) + 1)).mem_toFinset.mpr
          ⟨⟨by linarith, hr_hi, him_pos, Nat.lt_floor_add_one ρ.im⟩, hxi_ρ⟩,
          Nat.floor_le him_pos⟩
    have hρ_Z : ρ ∈ burnolUnitXiZeros m := xiUnitWindowZeros_subset_burnolUnitXiZeros m hρ_unit
    have hmult_pos : ∀ w ∈ burnolUnitXiZeros m, 1 ≤ (analyticOrderAt _root_.RHTower.xi w).toNat :=
      fun w hw => Nat.one_le_iff_ne_zero.mpr
        (_root_.RHTower.xi_order_toNat_ne_zero (((mem_burnolUnitXiZeros_iff m w).mp hw).2))
    have hge2 := two_le_collision_sum_of_offLine_in_band
      (one_sub_star_mem_burnolUnitXiZeros m) hmult_pos hρ_Z
      (hinv_lt.trans_le ((min_le_left _ _).trans (le_abs_self _)))
      (by
        rw [abs_of_pos (by linarith : 0 < ρ.re - 1 / 2)]
        linarith [min_le_right (ρ.re - 1 / 2) (1 - ρ.re)])
    rw [← hind_sum, hind0] at hge2
    omega
  tfae_finish

/-- Canonical polynomial stage `doorUnitStage m ⌈c * (m + 6)^k⌉₊` at fixed degree `k`. -/
def fixedPolyDoorStage (k : ℕ) (c : ℝ) (m : ℕ) : ℕ :=
  doorUnitStage m (Nat.ceil (c * ((m + 6 : ℕ) : ℝ) ^ k))

private lemma ceil_mul_pow_le_pow (k : ℕ) {c : ℝ} (hc1 : c ≤ 1) (m : ℕ) :
    Nat.ceil (c * ((m + 6 : ℕ) : ℝ) ^ k) ≤ (m + 6) ^ k :=
  Nat.ceil_le.mpr (by
    push_cast
    exact mul_le_of_le_one_left (by positivity) hc1)

private lemma exists_invPoly_thetaZero_re_le {k : ℕ} (hk : 1 ≤ k)
    (h1 : ∃ T₁ C : ℝ, 2 ≤ T₁ ∧ 0 < C ∧
      ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → T₁ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ C / |ρ.im| ^ k) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ m₁ : ℕ, ∀ m ≥ m₁, ∀ (N : ℕ) (hN : polySqrtPrefix k m ≤ N),
      ∀ z ∈ (centeredThetaWindow (burnolUnitLower_le_upper m) N
          (burnolUnit_bdry_regular m
            ((burnolPrefix_le_capCancelSqrtPrefix m).trans
              ((capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN)))).Z,
        z.re - 1 / 2 ≤ 1 / (12 * (fixedPolyDoorStage k c m : ℝ)) := by
  rcases h1 with ⟨T₁, C, hT₁, hC, hcorr⟩
  set c : ℝ := min 1 (1 / (96 * C * (2 : ℝ) ^ k))
  have hc_pos : 0 < c := lt_min zero_lt_one (by positivity)
  have hc_le1 : c ≤ 1 := min_le_left _ _
  set B_ord : ℝ := 7 + 100 * (burnolPrefixConst : ℝ) ^ 2
  have hB_pos : 0 < B_ord := by dsimp only [B_ord]; positivity
  set m₁ : ℕ := max (Nat.ceil T₁ + 12) (Nat.ceil ((2 * B_ord / c) ^ 2) + 12)
  refine ⟨c, hc_pos, hc_le1, m₁, fun m hm N hN z hz => ?_⟩
  set S : ℕ := Nat.ceil (c * ((m + 6 : ℕ) : ℝ) ^ k)
  have hS_pow := ceil_mul_pow_le_pow k hc_le1 m
  have hNbessel := (besselUnitPrefix_le_polySqrtPrefix_of_le k m hS_pow).trans hN
  have hbdry := burnolUnit_bdry_regular m
    ((burnolPrefix_le_capCancelSqrtPrefix m).trans
      ((capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN))
  obtain ⟨hstage, -⟩ := doorUnitStage_spec m S
  set n := fixedPolyDoorStage k c m
  have hn_def : n = doorUnitStage m S := rfl
  have hn6 : 6 ≤ n := (le_max_right S 6).trans (Finset.mem_Icc.mp hstage).1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn_le : (n : ℝ) ≤ (S : ℝ) + 6 + 2 * ((∑ w ∈ burnolUnitXiZeros m,
      (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ) ^ 2 := by
    have h := (Finset.mem_Icc.mp hstage).2
    have hmax : max S 6 ≤ S + 6 := max_le (by omega) (by omega)
    rw [hn_def]
    exact_mod_cast (show doorUnitStage m S ≤ S + 6 + 2 * (∑ w ∈ burnolUnitXiZeros m,
      (analyticOrderAt _root_.RHTower.xi w).toNat) ^ 2 by omega)
  have htail := unitStage_tail_lt m S hn6 hn_le hNbessel
  have hn_2c : (n : ℝ) ≤ 2 * c * ((m + 6 : ℕ) : ℝ) ^ k := by
    set s : ℕ := Nat.sqrt m + 1
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast Nat.succ_pos (Nat.sqrt m)
    have hs_le_rt : (s : ℝ) ≤ 2 * Real.sqrt ((m + 6 : ℕ) : ℝ) := by
      have hrt_m : (Nat.sqrt m : ℝ) ≤ Real.sqrt ((m + 6 : ℕ) : ℝ) := by
        rw [← Real.sqrt_sq (Nat.cast_nonneg (Nat.sqrt m))]
        exact Real.sqrt_le_sqrt (by
          have h1 : (Nat.sqrt m : ℝ) ^ 2 ≤ (m : ℝ) := by rw [sq]; exact_mod_cast Nat.sqrt_le m
          push_cast; linarith)
      have h1_rt : (1 : ℝ) ≤ Real.sqrt ((m + 6 : ℕ) : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ m + 6 by omega))
      have hs_eq : (s : ℝ) = (Nat.sqrt m : ℝ) + 1 := by dsimp only [s]; push_cast; rfl
      linarith
    have hL_sq : (Real.log ((m + 5 : ℕ) : ℝ)) ^ 2 ≤ 50 * (s : ℝ) := by
      have hle : Real.log ((m + 5 : ℕ) : ℝ) ≤ Real.log ((m + 6 : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (show m + 5 ≤ m + 6 by omega))
      have hnn : 0 ≤ Real.log ((m + 5 : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 5 by omega))
      exact (pow_le_pow_left₀ hnn hle 2).trans (sq_log_add_six_le_fifty_mul_sqrt m)
    have hd_le : ((∑ w ∈ burnolUnitXiZeros m,
        (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ) ≤ burnolOrderBound m :=
      burnolUnitXiZeros_totalOrder_le m
    have h2d_sq : 7 + 2 * ((∑ w ∈ burnolUnitXiZeros m,
        (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ) ^ 2 ≤ B_ord * (s : ℝ) := by
      have hd0 : (0 : ℝ) ≤ (∑ w ∈ burnolUnitXiZeros m,
        (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) := Nat.cast_nonneg _
      have hd_sq : ((∑ w ∈ burnolUnitXiZeros m,
          (analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℝ) ^ 2 ≤ burnolOrderBound m ^ 2 :=
        pow_le_pow_left₀ hd0 hd_le 2
      have hord_sq : burnolOrderBound m ^ 2 ≤ 50 * (burnolPrefixConst : ℝ) ^ 2 * (s : ℝ) := by
        unfold burnolOrderBound
        calc ((burnolPrefixConst : ℝ) * Real.log ((m + 5 : ℕ) : ℝ)) ^ 2
            = (burnolPrefixConst : ℝ) ^ 2 * (Real.log ((m + 5 : ℕ) : ℝ)) ^ 2 := mul_pow _ _ 2
          _ ≤ (burnolPrefixConst : ℝ) ^ 2 * (50 * (s : ℝ)) :=
              mul_le_mul_of_nonneg_left hL_sq (sq_nonneg _)
          _ = 50 * (burnolPrefixConst : ℝ) ^ 2 * (s : ℝ) := by ring
      dsimp only [B_ord]
      linarith [hd_sq, hord_sq, hs1]
    have hm_ge : Nat.ceil ((2 * B_ord / c) ^ 2) ≤ m :=
      (Nat.le_add_right _ 12).trans ((le_max_right _ _).trans hm)
    have hrt_ge : 2 * B_ord / c ≤ Real.sqrt ((m + 6 : ℕ) : ℝ) := by
      have hsq : (2 * B_ord / c) ^ 2 ≤ ((m + 6 : ℕ) : ℝ) := by
        calc (2 * B_ord / c) ^ 2 ≤ (Nat.ceil ((2 * B_ord / c) ^ 2) : ℝ) := Nat.le_ceil _
          _ ≤ (m : ℝ) := by exact_mod_cast hm_ge
          _ ≤ ((m + 6 : ℕ) : ℝ) := by push_cast; linarith
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * B_ord / c)]
      exact Real.sqrt_le_sqrt hsq
    have h2B_le : 2 * B_ord * Real.sqrt ((m + 6 : ℕ) : ℝ) ≤ c * ((m + 6 : ℕ) : ℝ) ^ k := by
      have h1 : 2 * B_ord ≤ c * Real.sqrt ((m + 6 : ℕ) : ℝ) := by
        linarith [(div_le_iff₀ hc_pos).mp hrt_ge]
      have h2 : 2 * B_ord * Real.sqrt ((m + 6 : ℕ) : ℝ) ≤
          c * (Real.sqrt ((m + 6 : ℕ) : ℝ) * Real.sqrt ((m + 6 : ℕ) : ℝ)) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      rw [Real.mul_self_sqrt (by positivity)] at h2
      have hpow_ge : ((m + 6 : ℕ) : ℝ) ≤ ((m + 6 : ℕ) : ℝ) ^ k := by
        conv_lhs => rw [← pow_one ((m + 6 : ℕ) : ℝ)]
        exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ m + 6 by omega)) hk
      exact h2.trans (mul_le_mul_of_nonneg_left hpow_ge hc_pos.le)
    have hS_lt : (S : ℝ) ≤ c * ((m + 6 : ℕ) : ℝ) ^ k + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hBs_le : B_ord * (s : ℝ) ≤ 2 * B_ord * Real.sqrt ((m + 6 : ℕ) : ℝ) := by
      calc B_ord * (s : ℝ) ≤ B_ord * (2 * Real.sqrt ((m + 6 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hs_le_rt hB_pos.le
        _ = 2 * B_ord * Real.sqrt ((m + 6 : ℕ) : ℝ) := by ring
    linarith [hn_le, hS_lt, h2d_sq, hBs_le, h2B_le]
  obtain ⟨hz_rect, hz_zero⟩ := (mem_centeredThetaWindow_iff _ N hbdry z).mp hz
  obtain ⟨w, hw_mem, hdist⟩ := exists_xiZero_near_thetaZero m N (r := 1 / (16 * (n : ℝ)))
    (by positivity) htail hz_rect hz_zero
  obtain ⟨⟨_, _, hwy_lo, _⟩, hw_xi⟩ := (mem_burnolUnitXiZeros_iff m w).mp hw_mem
  have hcoords := burnolUnit_coords m
  have hm12 : 12 ≤ m := (Nat.le_add_left 12 _).trans ((le_max_left _ _).trans hm)
  have hmT1 : Nat.ceil T₁ + 12 ≤ m := (le_max_left _ _).trans hm
  have hw_im_ge_half : ((m + 6 : ℕ) : ℝ) / 2 ≤ |w.im| := by
    have hmR : (12 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm12
    have hlo : (m : ℝ) - 3 ≤ w.im := by linarith [hcoords.2.2.1, hcoords.2.2.2.2, hwy_lo]
    have hhalf : ((m + 6 : ℕ) : ℝ) / 2 ≤ (m : ℝ) - 3 := by push_cast; linarith
    exact (hhalf.trans hlo).trans (le_abs_self _)
  have hw_T1 : T₁ ≤ |w.im| := by
    have hceil : T₁ ≤ (Nat.ceil T₁ : ℝ) := Nat.le_ceil T₁
    have hmR : (Nat.ceil T₁ : ℝ) + 12 ≤ (m : ℝ) := by exact_mod_cast hmT1
    have hlo : (m : ℝ) - 3 ≤ w.im := by linarith [hcoords.2.2.1, hcoords.2.2.2.2, hwy_lo]
    exact (by linarith : T₁ ≤ w.im).trans (le_abs_self _)
  have hw_re_bd : |w.re - 1 / 2| ≤ 1 / (48 * (n : ℝ)) := by
    have h1 := hcorr w hw_xi hw_T1
    have hpow_ge : (((m + 6 : ℕ) : ℝ) / 2) ^ k ≤ |w.im| ^ k :=
      pow_le_pow_left₀ (by positivity) hw_im_ge_half k
    have h2 : C / |w.im| ^ k ≤ (C * (2 : ℝ) ^ k) / ((m + 6 : ℕ) : ℝ) ^ k := by
      calc C / |w.im| ^ k
          ≤ C / (((m + 6 : ℕ) : ℝ) / 2) ^ k :=
            div_le_div_of_nonneg_left hC.le (by positivity) hpow_ge
        _ = (C * (2 : ℝ) ^ k) / ((m + 6 : ℕ) : ℝ) ^ k := by
            rw [div_pow, div_div_eq_mul_div]
    have hc_bound : c ≤ 1 / (96 * C * (2 : ℝ) ^ k) := min_le_right _ _
    have h96 : 96 * c * (C * (2 : ℝ) ^ k) ≤ 1 := by
      have := (le_div_iff₀ (by positivity : 0 < 96 * C * (2 : ℝ) ^ k)).mp hc_bound
      linarith
    have h3 : (C * (2 : ℝ) ^ k) / ((m + 6 : ℕ) : ℝ) ^ k ≤ 1 / (48 * (n : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      calc C * (2 : ℝ) ^ k * (48 * (n : ℝ))
          ≤ C * (2 : ℝ) ^ k * (48 * (2 * c * ((m + 6 : ℕ) : ℝ) ^ k)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (96 * c * (C * (2 : ℝ) ^ k)) * ((m + 6 : ℕ) : ℝ) ^ k := by ring
        _ ≤ 1 * ((m + 6 : ℕ) : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right h96 (by positivity)
        _ = ((m + 6 : ℕ) : ℝ) ^ k := one_mul _
    exact (h1.trans h2).trans h3
  have hz_close : z.re - w.re ≤ 1 / (16 * (n : ℝ)) :=
    (le_abs_self _).trans ((Complex.abs_re_le_norm (z - w)).trans hdist)
  have hw_sub : w.re - 1 / 2 ≤ 1 / (48 * (n : ℝ)) := (le_abs_self _).trans hw_re_bd
  have halg : 1 / (48 * (n : ℝ)) + 1 / (16 * (n : ℝ)) = 1 / (12 * (n : ℝ)) := by ring
  linarith

private lemma invPoly_corridor_of_fredholmIndex_eq_zero {k : ℕ} (hk : 1 ≤ k)
    (h4 : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ polySqrtPrefix k m,
      (∀ u : HTGeometry.UnitCircle,
        centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
          (fixedPolyDoorStage k c m) N u ≠ 0) ∧
      HTGeometry.fredholmIndex
        (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
          (fixedPolyDoorStage k c m) N) = 0) :
    ∃ T₁ C : ℝ, 2 ≤ T₁ ∧ 0 < C ∧
      ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → T₁ ≤ |ρ.im| →
        |ρ.re - 1 / 2| ≤ C / |ρ.im| ^ k := by
  rcases h4 with ⟨c, hc_pos, hc_le1, m₀, hind⟩
  set m₂ : ℕ := max m₀ (Nat.ceil ((600 / c) ^ 2) + 12)
  refine ⟨((m₂ + 1 : ℕ) : ℝ), 1 / (4 * c), ?_, by positivity, fun ρ hxi_ρ hT₁ => ?_⟩
  · have : 12 ≤ m₂ := (Nat.le_add_left 12 _).trans (le_max_right _ _)
    exact_mod_cast (show 2 ≤ m₂ + 1 by omega)
  · set ρ1 : ℂ := if 0 ≤ ρ.im then ρ else 1 - ρ
    have hxi_1 : _root_.RHTower.xi ρ1 = 0 := by
      dsimp only [ρ1]; split_ifs
      · exact hxi_ρ
      · rw [_root_.RHTower.xi_one_sub]; exact hxi_ρ
    have him_1 : ρ1.im = |ρ.im| := by
      dsimp only [ρ1]; split_ifs with hnn
      · exact (abs_of_nonneg hnn).symm
      · simp [abs_of_neg (not_le.mp hnn)]
    have hre_abs : |ρ1.re - 1 / 2| = |ρ.re - 1 / 2| := by
      dsimp only [ρ1]; split_ifs
      · rfl
      · simp only [Complex.sub_re, Complex.one_re]
        rw [show 1 - ρ.re - 1 / 2 = -(ρ.re - 1 / 2) by ring, abs_neg]
    have hre_lt1 : ρ1.re < 1 :=
      not_le.mp fun hge => _root_.RHTower.xi_ne_zero_of_one_le_re hge hxi_1
    have hre_gt0 : 0 < ρ1.re := by
      by_contra hle
      push Not at hle
      have hge1 : 1 ≤ (1 - ρ1).re := by simp; linarith
      exact _root_.RHTower.xi_ne_zero_of_one_le_re hge1
        (by rw [_root_.RHTower.xi_one_sub]; exact hxi_1)
    have hne1 : ρ1 ≠ 1 := fun h1 => by rw [h1] at hre_lt1; simp at hre_lt1
    have hzeta_1 : riemannZeta ρ1 = 0 :=
      (_root_.RHTower.xi_eq_zero_iff hre_gt0 hne1).mp hxi_1
    have hm₂_12 : 12 ≤ m₂ := (Nat.le_add_left 12 _).trans (le_max_right _ _)
    have him_ge_m₂ : ((m₂ + 1 : ℕ) : ℝ) ≤ ρ1.im := him_1 ▸ hT₁
    have him_pos : 0 < ρ1.im := by
      have : (0 : ℝ) < ((m₂ + 1 : ℕ) : ℝ) := by positivity
      linarith
    set m : ℕ := Nat.floor ρ1.im
    have hm_ge_m₂ : m₂ ≤ m := by
      have h1 : m₂ + 1 ≤ m := Nat.le_floor him_ge_m₂
      omega
    have hm_ge_m₀ : m₀ ≤ m := (le_max_left _ _).trans hm_ge_m₂
    have hm_ge_ceil : Nat.ceil ((600 / c) ^ 2) + 12 ≤ m := (le_max_right _ _).trans hm_ge_m₂
    have hm_le_im : (m : ℝ) ≤ ρ1.im := Nat.floor_le him_pos.le
    have him_lt_m1 : ρ1.im < (m : ℝ) + 1 := Nat.lt_floor_add_one ρ1.im
    have hρ_unit : ρ1 ∈ xiUnitWindowZeros (m : ℝ) :=
      mem_xiUnitWindowZeros.mpr
        ⟨(_root_.RHTower.stripZeros_finite ((m : ℝ) + 1)).mem_toFinset.mpr
          ⟨⟨hre_gt0, hre_lt1, him_pos.le, him_lt_m1⟩, hxi_1⟩, hm_le_im⟩
    have hρ_Z : ρ1 ∈ burnolUnitXiZeros m := xiUnitWindowZeros_subset_burnolUnitXiZeros m hρ_unit
    set S : ℕ := Nat.ceil (c * ((m + 6 : ℕ) : ℝ) ^ k)
    set n : ℕ := fixedPolyDoorStage k c m
    set N : ℕ := polySqrtPrefix k m
    have hNdoor : doorUnitPrefix m S ≤ N :=
      (doorUnitPrefix_le_besselUnitPrefix m S).trans
        (besselUnitPrefix_le_polySqrtPrefix_of_le k m (ceil_mul_pow_le_pow k hc_le1 m))
    obtain ⟨hn_Icc, hspec⟩ := doorUnitStage_spec m S
    obtain ⟨_, hind_sum⟩ := hspec N hNdoor
    have hind0 := (hind m hm_ge_m₀ N le_rfl).2
    have hn_ge_S : S ≤ n := (le_max_left S 6).trans (Finset.mem_Icc.mp hn_Icc).1
    have hn6 : 6 ≤ n := (le_max_right S 6).trans (Finset.mem_Icc.mp hn_Icc).1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hs_eq : (zhukovskyStage n : ℝ) = (n : ℝ) := by
      exact_mod_cast zhukovskyStage_eq_self hn6
    have hn_ge_pow : c * ((m + 6 : ℕ) : ℝ) ^ k ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr hn_ge_S)
    rw [← hre_abs, ← him_1]
    by_contra hgt
    push Not at hgt
    have him_le_m6 : ρ1.im ≤ ((m + 6 : ℕ) : ℝ) := by push_cast; linarith
    have hlo_band : 1 / (4 * (zhukovskyStage n : ℝ)) < |ρ1.re - 1 / 2| := by
      rw [hs_eq]
      have hpow_le : ρ1.im ^ k ≤ ((m + 6 : ℕ) : ℝ) ^ k :=
        pow_le_pow_left₀ him_pos.le him_le_m6 k
      have h1 : 1 / (4 * (n : ℝ)) ≤ (1 / (4 * c)) / ((m + 6 : ℕ) : ℝ) ^ k := by
        rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
        linarith
      have h2 : (1 / (4 * c)) / ((m + 6 : ℕ) : ℝ) ^ k ≤ (1 / (4 * c)) / ρ1.im ^ k :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpow_le
      exact (h1.trans h2).trans_lt hgt
    have hhi_band : |ρ1.re - 1 / 2| < 1 / 2 - 1 / (4 * (zhukovskyStage n : ℝ)) := by
      rw [hs_eq]
      have hup := _root_.RHTower.re_le_one_sub_of_zeta_zero hre_gt0 hre_lt1 hzeta_1
      have hdn := _root_.RHTower.one_div_le_re_of_zeta_zero hre_gt0 hre_lt1 hzeta_1
      rw [abs_of_pos him_pos] at hup hdn
      have habs_zfr : |ρ1.re - 1 / 2| ≤ 1 / 2 - 1 / (58 * Real.log ρ1.im) := by
        rw [div_div] at hup hdn
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have him_gt1 : 1 < ρ1.im := by
        have : (12 : ℝ) < ((m₂ + 1 : ℕ) : ℝ) := by exact_mod_cast (show 12 < m₂ + 1 by omega)
        linarith
      have hlog_pos : 0 < Real.log ρ1.im := Real.log_pos him_gt1
      have hlog_le_rt : Real.log ρ1.im ≤ 2 * Real.sqrt ((m + 6 : ℕ) : ℝ) := by
        have h1 : Real.log ρ1.im ≤ Real.log ((m + 6 : ℕ) : ℝ) :=
          Real.log_le_log him_pos him_le_m6
        have hsq := sq_log_le_four_mul (x := ((m + 6 : ℕ) : ℝ))
          (by exact_mod_cast (show 1 ≤ m + 6 by omega))
        have h2 : Real.log ((m + 6 : ℕ) : ℝ) ≤ 2 * Real.sqrt ((m + 6 : ℕ) : ℝ) := by
          have hnn : 0 ≤ Real.log ((m + 6 : ℕ) : ℝ) :=
            Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 6 by omega))
          rw [← Real.sqrt_sq hnn]
          calc Real.sqrt ((Real.log ((m + 6 : ℕ) : ℝ)) ^ 2)
              ≤ Real.sqrt (4 * ((m + 6 : ℕ) : ℝ)) := Real.sqrt_le_sqrt hsq
            _ = 2 * Real.sqrt ((m + 6 : ℕ) : ℝ) := by
                rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num]
        exact h1.trans h2
      have hrt_gt : 600 / c < Real.sqrt ((m + 6 : ℕ) : ℝ) := by
        have hsq : (600 / c) ^ 2 < ((m + 6 : ℕ) : ℝ) := by
          have hc1 : (600 / c) ^ 2 ≤ (Nat.ceil ((600 / c) ^ 2) : ℝ) := Nat.le_ceil _
          have hc2 : (Nat.ceil ((600 / c) ^ 2) : ℝ) + 12 ≤ (m : ℝ) := by exact_mod_cast hm_ge_ceil
          push_cast; linarith
        rw [← Real.sqrt_sq (by positivity : 0 ≤ 600 / c)]
        exact Real.sqrt_lt_sqrt (by positivity) hsq
      have h58_lt : 58 * Real.log ρ1.im < 4 * (n : ℝ) := by
        have h1 : 600 < c * Real.sqrt ((m + 6 : ℕ) : ℝ) := by
          linarith [(div_lt_iff₀ hc_pos).mp hrt_gt]
        have hrt_pos : 0 < Real.sqrt ((m + 6 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
        have h2 : 116 * Real.sqrt ((m + 6 : ℕ) : ℝ) < c * ((m + 6 : ℕ) : ℝ) := by
          have hmul : 600 * Real.sqrt ((m + 6 : ℕ) : ℝ) <
              c * (Real.sqrt ((m + 6 : ℕ) : ℝ) * Real.sqrt ((m + 6 : ℕ) : ℝ)) := by
            simpa only [mul_assoc] using mul_lt_mul_of_pos_right h1 hrt_pos
          rw [Real.mul_self_sqrt (by positivity)] at hmul
          linarith [hmul, hrt_pos]
        have hpow_ge : ((m + 6 : ℕ) : ℝ) ≤ ((m + 6 : ℕ) : ℝ) ^ k := by
          conv_lhs => rw [← pow_one ((m + 6 : ℕ) : ℝ)]
          exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ m + 6 by omega)) hk
        have h3 : c * ((m + 6 : ℕ) : ℝ) ≤ c * ((m + 6 : ℕ) : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left hpow_ge hc_pos.le
        linarith [hlog_le_rt, h2, h3, hn_ge_pow]
      have hinv_lt : 1 / (4 * (n : ℝ)) < 1 / (58 * Real.log ρ1.im) :=
        one_div_lt_one_div_of_lt (by positivity) h58_lt
      linarith [habs_zfr, hinv_lt]
    have hmult_pos : ∀ w ∈ burnolUnitXiZeros m, 1 ≤ (analyticOrderAt _root_.RHTower.xi w).toNat :=
      fun w hw => Nat.one_le_iff_ne_zero.mpr
        (_root_.RHTower.xi_order_toNat_ne_zero (((mem_burnolUnitXiZeros_iff m w).mp hw).2))
    have hge2 := two_le_collision_sum_of_offLine_in_band
      (one_sub_star_mem_burnolUnitXiZeros m) hmult_pos hρ_Z hlo_band hhi_band
    have hn_door : doorUnitStage m S = n := rfl
    rw [hn_door] at hind_sum
    rw [← hind_sum, hind0] at hge2
    omega

/-- **Fixed-degree inverse-polynomial corridor equivalence (`List.TFAE`).**
At each fixed integer `k ≥ 1`, an inverse-polynomial zero-free corridor
`|Re ρ - 1/2| ≤ C / |Im ρ|^k` for `ξ` is unconditionally equivalent to sub-stage-threshold Laplace
integrability of `|𝒵_N(t)|²` and `|𝒫_+(t)|²`, explicit Bessel–Szegő certificate positivity, and
vanishing Wiener–Hopf Fredholm index at polynomial stage `fixedPolyDoorStage k c m` (`0 < c ≤ 1`)
and the `c`-independent `Θ_k(√m)` prefix `N ≥ polySqrtPrefix k m`. -/
theorem invPoly_corridor_iff_fixedDegree_polynomialStage {k : ℕ} (hk : 1 ≤ k) :
    [ -- 1. Inverse-polynomial zero-free corridor of degree `k`:
      ∃ T₁ C : ℝ, 2 ≤ T₁ ∧ 0 < C ∧
        ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → T₁ ≤ |ρ.im| →
          |ρ.re - 1 / 2| ≤ C / |ρ.im| ^ k,
      -- 2. Sub-stage-threshold Laplace integrability of `|𝒵_N(t)|²` and `|𝒫_+(t)|²`:
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ polySqrtPrefix k m,
        IntegrableOn
          (fun t : ℝ => Real.exp (-((1 / (2 * (fixedPolyDoorStage k c m : ℝ))) * t)) *
            ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
          (Ioi (0 : ℝ)) ∧
        IntegrableOn
          (fun t : ℝ => Real.exp (-((1 / (2 * (fixedPolyDoorStage k c m : ℝ))) * t)) *
            ‖rightHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
          (Ioi (0 : ℝ)),
      -- 3. Explicit Bessel–Szegő certificate positivity at stage `fixedPolyDoorStage k c m`:
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ polySqrtPrefix k m, ∀ K : ℕ,
        2 * (centeredThetaWindowDegree (burnolUnitLower m) (burnolUnitUpper m) N : ℝ) ^ 2 *
            (1 - 1 / (4 * (fixedPolyDoorStage k c m : ℝ))) ^ (K + 1) /
              (1 / (4 * (fixedPolyDoorStage k c m : ℝ))) < Real.pi / 2 →
        ∀ u : HTGeometry.UnitCircle,
          0 < (besselSzegoCertificate (fixedPolyDoorStage k c m) K
              (fun t => ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2) u *
            centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
              (fixedPolyDoorStage k c m) N u).re,
      -- 4. Circle-nonvanishing and vanishing Wiener–Hopf Fredholm index:
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ polySqrtPrefix k m,
        (∀ u : HTGeometry.UnitCircle,
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
            (fixedPolyDoorStage k c m) N u ≠ 0) ∧
        HTGeometry.fredholmIndex
          (centeredThetaCollisionOperator (burnolUnitLower m) (burnolUnitUpper m)
            (fixedPolyDoorStage k c m) N) = 0
    ].TFAE := by
  tfae_have 1 → 2 := by
    intro h1
    obtain ⟨c, hc_pos, hc_le1, m₁, hcorr⟩ := exists_invPoly_thetaZero_re_le hk h1
    refine ⟨c, hc_pos, hc_le1, m₁, fun m hm N hN => ?_⟩
    set n := fixedPolyDoorStage k c m
    have hn6 : 6 ≤ n :=
      (le_max_right _ 6).trans (Finset.mem_Icc.mp (doorUnitStage_spec m _).1).1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hbdry := burnolUnit_bdry_regular m
      ((burnolPrefix_le_capCancelSqrtPrefix m).trans
        ((capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN))
    set W := centeredThetaWindow (burnolUnitLower_le_upper m) N hbdry
    have hδ := hcorr m hm N hN
    have hint_Z : IntegrableOn
        (fun t : ℝ => Real.exp (-((1 / (2 * (n : ℝ))) * t)) *
          ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2)
        (Ioi (0 : ℝ)) := by
      have hdom : IntegrableOn
          (fun t : ℝ => ((W.degree : ℝ) ^ 2 + 1) * Real.exp (-(1 / (3 * (n : ℝ))) * t))
          (Ioi (0 : ℝ)) := by
        have hneg : -(1 / (3 * (n : ℝ))) < 0 := neg_lt_zero.mpr (by positivity)
        exact (integrableOn_exp_mul_Ioi hneg 0).const_mul _
      have hcont_Z : Continuous (centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N) := by
        have heq : centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N =
            fun t => W.expSum t :=
          funext fun t => (centeredThetaWindow_expSum _ N hbdry t).symm
        rw [heq]; exact W.continuous_expSum
      refine hdom.mono'
        (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
          (hcont_Z.norm.pow 2)).aestronglyMeasurable) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
      have hnorm := W.norm_expSum_le hδ ht0
      rw [centeredThetaWindow_expSum (burnolUnitLower_le_upper m) N hbdry t] at hnorm
      have hsq : ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 ≤
          ((W.degree : ℝ) ^ 2 + 1) * Real.exp ((1 / (6 * (n : ℝ))) * t) := by
        calc ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2
            ≤ ((W.degree : ℝ) * Real.exp ((1 / (12 * (n : ℝ))) * t)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hnorm 2
          _ = (W.degree : ℝ) ^ 2 * Real.exp ((1 / (6 * (n : ℝ))) * t) := by
              rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; congr 2; ring
          _ ≤ ((W.degree : ℝ) ^ 2 + 1) * Real.exp ((1 / (6 * (n : ℝ))) * t) :=
              mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      calc Real.exp (-((1 / (2 * (n : ℝ))) * t)) *
              ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2
          ≤ Real.exp (-((1 / (2 * (n : ℝ))) * t)) *
              (((W.degree : ℝ) ^ 2 + 1) * Real.exp ((1 / (6 * (n : ℝ))) * t)) :=
            mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
        _ = ((W.degree : ℝ) ^ 2 + 1) *
              (Real.exp (-((1 / (2 * (n : ℝ))) * t)) * Real.exp ((1 / (6 * (n : ℝ))) * t)) := by ring
        _ = ((W.degree : ℝ) ^ 2 + 1) * Real.exp (-(1 / (3 * (n : ℝ))) * t) := by
            rw [← Real.exp_add]; congr 2; ring
    exact ⟨hint_Z, (integrableOn_windowEnergy_iff_rightHalfPort
      (burnolUnitLower_le_upper m) N hbdry (by positivity)).mp hint_Z⟩
  tfae_have 1 → 3 := by
    intro h1
    obtain ⟨c, hc_pos, hc_le1, m₁, hcorr⟩ := exists_invPoly_thetaZero_re_le hk h1
    refine ⟨c, hc_pos, hc_le1, m₁, fun m hm N hN K hK u => ?_⟩
    set n := fixedPolyDoorStage k c m
    have hn6 : 6 ≤ n :=
      (le_max_right _ 6).trans (Finset.mem_Icc.mp (doorUnitStage_spec m _).1).1
    have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn6
    have hbdry := burnolUnit_bdry_regular m
      ((burnolPrefix_le_capCancelSqrtPrefix m).trans
        ((capCancelSqrtPrefix_le_polySqrtPrefix k m).trans hN))
    set W := centeredThetaWindow (burnolUnitLower_le_upper m) N hbdry
    have hη : 0 < 1 / (4 * (n : ℝ)) := by positivity
    have hη2 : 1 / (4 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hin : W.InCorridor n (1 / (4 * (n : ℝ))) := by
      intro z hz
      have h12 := hcorr m hm N hN z hz
      rw [zhukovskyMajorAxis_of_six_le hn6]
      have hpos12 : 0 < 1 / (12 * (n : ℝ)) := by positivity
      have halg : 1 / 2 - (1 / 2 - 1 / (2 * (n : ℝ))) - 1 / (4 * (n : ℝ)) =
          3 * (1 / (12 * (n : ℝ))) := by ring
      linarith
    rw [← centeredThetaWindow_degree (burnolUnitLower_le_upper m) N hbdry] at hK
    have hpos := hin.besselSzegoCertificate_mul_loop_pos
      (eval_centeredThetaDifferencePoly_eq_window (burnolUnitLower_le_upper m) N hbdry) hη hη2 hK u
    have hE : (fun t => ‖W.expSum t‖ ^ 2) =
        fun t => ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 :=
      funext fun t => by rw [centeredThetaWindow_expSum]
    rwa [hE] at hpos
  tfae_have 2 → 4 := by
    rintro ⟨c, hc_pos, hc_le1, m₀, hint⟩
    refine ⟨c, hc_pos, hc_le1, m₀, fun m hm N hN => ?_⟩
    set S : ℕ := Nat.ceil (c * ((m + 6 : ℕ) : ℝ) ^ k)
    have hNbessel := (besselUnitPrefix_le_polySqrtPrefix_of_le k m (ceil_mul_pow_le_pow k hc_le1 m)).trans hN
    have hNdoor := (doorUnitPrefix_le_besselUnitPrefix m S).trans hNbessel
    have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_doorUnitPrefix m S).trans hNdoor)
    obtain ⟨hstage, hspec⟩ := doorUnitStage_spec m S
    obtain ⟨hnz, _⟩ := hspec N hNdoor
    set n := fixedPolyDoorStage k c m
    have hn6 : 6 ≤ n := (le_max_right S 6).trans (Finset.mem_Icc.mp hstage).1
    set W := centeredThetaWindow (burnolUnitLower_le_upper m) N hbdry
    have hint_W : IntegrableOn
        (fun t : ℝ => Real.exp (-((1 / 2 - zhukovskyMajorAxis n) * t)) * ‖W.expSum t‖ ^ 2)
        (Ioi 0) := by
      have hgap : 1 / 2 - zhukovskyMajorAxis n = 1 / (2 * (n : ℝ)) := by
        rw [zhukovskyMajorAxis_of_six_le hn6]; ring
      have heq : (fun t : ℝ => Real.exp (-((1 / 2 - zhukovskyMajorAxis n) * t)) * ‖W.expSum t‖ ^ 2) =
          fun t => Real.exp (-((1 / (2 * (fixedPolyDoorStage k c m : ℝ))) * t)) *
            ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 :=
        funext fun t => by rw [hgap, centeredThetaWindow_expSum]
      rw [heq]
      exact (hint m hm N hN).1
    exact ⟨hnz, W.fredholmIndex_eq_zero_of_integrableOn_energy
      (eval_centeredThetaDifferencePoly_eq_window (burnolUnitLower_le_upper m) N hbdry) hint_W⟩
  tfae_have 3 → 4 := by
    rintro ⟨c, hc_pos, hc_le1, m₀, hcert⟩
    refine ⟨c, hc_pos, hc_le1, m₀, fun m hm N hN => ?_⟩
    set n := fixedPolyDoorStage k c m
    have hn6 : 6 ≤ n :=
      (le_max_right _ 6).trans (Finset.mem_Icc.mp (doorUnitStage_spec m _).1).1
    have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn6
    have hη : 0 < 1 / (4 * (n : ℝ)) := by positivity
    have hη1 : 1 / (4 * (n : ℝ)) < 1 := by rw [div_lt_one (by positivity)]; linarith
    obtain ⟨K, hK⟩ := exists_certificate_order
      (centeredThetaWindowDegree (burnolUnitLower m) (burnolUnitUpper m) N : ℝ) _ hη hη1
    exact fredholmIndex_eq_zero_of_diskUnit_re_pos _
      (isDiskUnit_besselSzegoCertificate n K _) (hcert m hm N hN K hK)
  tfae_have 4 → 1 := invPoly_corridor_of_fredholmIndex_eq_zero hk
  tfae_finish

end GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux
