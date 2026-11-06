import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheHardySpaceOfTheDisc
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheInnerMassIsAMollifierInfimum
import GaloisForLFunctions.RHTower.ZetaTypicalHeightLogDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Near-extremal mollifiers are rigid

With `E(s) = (s − 1)ζ(s)/s` and `M_Q(s) = exp Q(φ(s))`, `φ(s) = (s − 1)/s`, a budget is `B(Q) = ∫ |ζ M_Q|² P₁`, and RH is the existence of budgets
tending to `1`. In the disc coordinate `u = φ(s)`, the function `E M_Q` is of Hardy type, with value `1` at `u = 0` (`isHardyDisc_mollified`), so:

* **The rigidity law** (`norm_sub_one_sq_le`). For every `Q` with `Q(0) = 0` and every `Re s > ½`,

  `|E(s) M_Q(s) − 1|² ≤ (B(Q) − 1) |s − 1|²/(2 Re s − 1)`.

* **The limit is forced** (`tendsto_of_tendsto_budget`). Along any family with `B(Q_k) → 1`, `M_{Q_k}(s) E(s) → 1` for every `Re s > ½`: the only
  limit of near-extremal mollifiers is `1/E`. There is nothing to choose.
* **The coefficients are forced** (`norm_coeff_one_add_le`, `sum_taylorCoeff_le`). All Taylor coefficients of `E M_Q` beyond the first are
  bounded by the excess: `Σ_{k≥1} |a_k|² ≤ B(Q) − 1`. The first says `|q₁ − (1 − γ)|² ≤ B(Q) − 1`, where `q₁` is the linear coefficient of `Q` and `γ` is Euler's constant.
* **A single zero costs** (`le_budget_of_zero`). If `ζ(ρ) = 0` with `Re ρ > ½`, every budget is at least `|ρ|²/|ρ − 1|²`, by the rigidity law alone.
* **Near-extremal mollifiers flatten `ζ`** (`integral_abs_flatten_le`). At any inner mass, `∫ | |ζ M_Q|²/B − 1 | P₁ ≤ 2 √(log B − 2I(1))`: a mollifier near the true
  infimum makes `|ζ M_Q|` constant in `L¹`.

Over a curve Castelnuovo says that the extremal mollifier exists, and it is explicit: `1/L`. Over `ℤ` the target is the same object. So the role of Castelnuovo is not to find the mollifier, which is forced, but to prove that this
candidate has finite, then small, excess.
-/

open Complex Filter Topology MeasureTheory Set Metric
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

local notation "𝕋" => AddCircle (2 * π)

/-! ### The disc function -/

/-- `E M_Q` in the coordinate `u = φ(s)`, `s = (1 − u)⁻¹`. -/
def mollified (Q : Polynomial ℂ) (u : ℂ) : ℂ :=
  (1 - u) * zetaEntire (1 - u)⁻¹ * Complex.exp (Q.eval u)

theorem exists_exp_bound (Q : Polynomial ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖u‖ ≤ 1 → ‖Complex.exp (Q.eval u)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (f := fun z => Complex.exp (Q.eval z)) (Complex.continuous_exp.comp Q.continuous).continuousOn
  exact ⟨max C 0, le_max_right _ _, fun u hu =>
    (hC u (by simpa using hu)).trans (le_max_left _ _)⟩

theorem one_half_le_re_inv {u : ℂ} (hu : ‖u‖ ≤ 1) (h1 : u ≠ 1) : 1 / 2 ≤ ((1 - u)⁻¹).re := by
  have hz : (1 - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hn : 0 < Complex.normSq (1 - u) := Complex.normSq_pos.mpr hz
  have hu2 : Complex.normSq u ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg u]
  rw [Complex.inv_re, le_div_iff₀ hn]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im] at hn hu2 ⊢
  nlinarith

theorem differentiableAt_mollified (Q : Polynomial ℂ) {u : ℂ} (hu : u ≠ 1) :
    DifferentiableAt ℂ (mollified Q) u := by
  have hne : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h1 : DifferentiableAt ℂ (fun v : ℂ => (1 - v)⁻¹) u :=
    ((differentiableAt_const _).sub differentiableAt_id).inv hne
  have h2 : DifferentiableAt ℂ (fun v : ℂ => zetaEntire (1 - v)⁻¹) u :=
    differentiable_zetaEntire.differentiableAt.comp u h1
  have h3 : DifferentiableAt ℂ (fun v : ℂ => Complex.exp (Q.eval v)) u :=
    Complex.differentiable_exp.differentiableAt.comp u Q.differentiable.differentiableAt
  exact (((differentiableAt_const _).sub differentiableAt_id).mul h2).mul h3

/-- For `u ≠ 0, 1`, `E M_Q = u ζ((1 − u)⁻¹) exp Q(u)`. -/
theorem mollified_eq {Q : Polynomial ℂ} {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    mollified Q u = u * riemannZeta (1 - u)⁻¹ * Complex.exp (Q.eval u) := by
  have hne : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have hs1 : (1 - u)⁻¹ ≠ 1 := by
    intro h
    have : (1 : ℂ) - u = 1 := by
      rw [← inv_inv (1 - u), h, inv_one]
    exact hu0 (by linear_combination -this)
  rw [mollified, zetaEntire_eq hs1]
  have e : (1 - u) * (((1 - u)⁻¹ - 1) * riemannZeta (1 - u)⁻¹) = u * riemannZeta (1 - u)⁻¹ := by
    field_simp
    ring
  rw [e]

theorem mollified_zero {Q : Polynomial ℂ} (hQ : Q.coeff 0 = 0) : mollified Q 0 = 1 := by
  rw [mollified, sub_zero, inv_one, zetaEntire_eval_one, ← Polynomial.coeff_zero_eq_eval_zero, hQ]
  simp

theorem discChart_one (u : ℂ) : discChart 1 u = (1 - u)⁻¹ := by
  simp [discChart, halfPlaneShift, halfPlaneOfDisc]
  norm_num

/-- On the line `|s − 1| = |s|`. -/
theorem norm_sub_one_line (τ : ℝ) : ‖(1 / 2 + τ * I : ℂ) - 1‖ = ‖(1 / 2 + τ * I : ℂ)‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

theorem blaschkeCoord_one (s : ℂ) : blaschkeCoord 1 s = (s - 1) / s := by
  simp [blaschkeCoord]

theorem norm_blaschkeCoord_one_line (τ : ℝ) : ‖blaschkeCoord 1 (1 / 2 + τ * I)‖ = 1 := by
  rw [blaschkeCoord_one, norm_div, norm_sub_one_line]
  refine div_self (norm_ne_zero_iff.mpr ?_)
  intro h
  have := congrArg Complex.re h
  norm_num at this

/-- The budget in the disc coordinate. -/
theorem integrable_and_circleAverage_mollified (Q : Polynomial ℂ) :
    CircleIntegrable (fun z => ‖mollified Q z‖ ^ 2) 0 1 ∧
      Real.circleAverage (fun z => ‖mollified Q z‖ ^ 2) 0 1 = budget 1 Q := by
  have hw : (1 / 2 : ℝ) < (1 : ℂ).re := by norm_num
  set F : ℝ → ℝ := fun τ => ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 *
    ‖Complex.exp (Q.eval (blaschkeCoord 1 (1 / 2 + τ * I)))‖ ^ 2 with hF
  have hg : ∀ t : ℝ, (fun z => ‖mollified Q z‖ ^ 2) (circleMap 0 1 (criticalLineAngle t)) =
      F ((2 * (1 : ℂ).re - 1) * t + (1 : ℂ).im) := by
    intro t
    set u := circleMap 0 1 (criticalLineAngle t) with hu
    have hu1 : u ≠ 1 := circleMap_criticalLineAngle_ne_one t
    have hun : ‖u‖ = 1 := norm_circleMap_zero_one _
    have hu0 : u ≠ 0 := fun h => by
      rw [h, norm_zero] at hun
      exact zero_ne_one hun
    have hs := discChart_circleMap 1 t
    rw [discChart_one, ← hu] at hs
    have hb := blaschkeCoord_line (w := 1) hw t
    rw [← hu] at hb
    simp only [hF]
    rw [hb, ← hs, mollified_eq hu0 hu1, norm_mul, norm_mul, hun, one_mul, mul_pow]
  have hP := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num) F _ hg
  obtain ⟨C, hC0, hC⟩ := exists_exp_bound Q
  have hi := integrable_norm_sq_zeta_poisson (w := 1) (by norm_num)
  have hne : ∀ τ : ℝ, (1 / 2 + τ * I : ℂ) ≠ 0 := fun τ h => by
    have := congrArg Complex.re h
    norm_num at this
  have hexp : Continuous fun τ : ℝ => ‖Complex.exp (Q.eval (blaschkeCoord 1 (1 / 2 + τ * I)))‖ ^ 2 := by
    have hb : Continuous fun τ : ℝ => blaschkeCoord 1 (1 / 2 + τ * I) := by
      simp only [blaschkeCoord_one]
      exact Continuous.div (by fun_prop) (by fun_prop) hne
    exact ((Complex.continuous_exp.comp (Q.continuous.comp hb)).norm).pow 2
  have hint : Integrable fun τ : ℝ => F τ * halfPlanePoissonKernel 1 τ := by
    refine (hi.const_mul (C ^ 2)).mono' ?_ (Eventually.of_forall fun τ => ?_)
    · have := hexp.aestronglyMeasurable.mul (μ := volume) hi.aestronglyMeasurable
      refine this.congr (Eventually.of_forall fun τ => ?_)
      simp only [hF, Pi.mul_apply]
      ring
    · have hP0 := (halfPlanePoissonKernel_pos (w := 1) (by norm_num) τ).le
      have hb : ‖Complex.exp (Q.eval (blaschkeCoord 1 (1 / 2 + τ * I)))‖ ≤ C :=
        hC _ (norm_blaschkeCoord_one_line τ).le
      have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hP0)]
      simp only [hF]
      calc ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * ‖Complex.exp (Q.eval (blaschkeCoord 1 (1 / 2 + τ * I)))‖ ^ 2 *
            halfPlanePoissonKernel 1 τ
          ≤ ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * C ^ 2 * halfPlanePoissonKernel 1 τ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 (sq_nonneg _)) hP0
        _ = _ := by ring
  exact ⟨hP.1.mpr hint, hP.2⟩

/-- **`E M_Q` is of Hardy type.** -/
theorem isHardyDisc_mollified (Q : Polynomial ℂ) : IsHardyDisc (mollified Q) := by
  obtain ⟨C, hC0, hC⟩ := exists_exp_bound Q
  refine ⟨fun u hu => (differentiableAt_mollified Q hu).differentiableWithinAt, ?_, ?_, ?_,
    (integrable_and_circleAverage_mollified Q).1⟩
  · refine measurable_of_continuousOn_compl_singleton 1 fun u hu => ?_
    exact (differentiableAt_mollified Q hu).continuousAt.continuousWithinAt
  · obtain ⟨K, hK1, hK⟩ := isHalfPlaneDatum_zetaEntire.growth
    refine ⟨50 * K * C, by positivity, fun u hu hu1 => ?_⟩
    set d := ‖1 - u‖ with hd
    have hdpos : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hu1))
    have hd2 : d ≤ 2 := by
      calc d ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    have hs : ‖(1 - u)⁻¹‖ = d⁻¹ := by rw [norm_inv]
    have hz := hK _ (one_half_le_re_inv hu hu1)
    rw [hs] at hz
    have hdi : d⁻¹ + 2 ≤ 5 * d⁻¹ := by
      have : 1 ≤ 2 * d⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hdpos]
        linarith
      linarith
    have hdi0 : 0 ≤ d⁻¹ + 2 := by positivity
    have hsq : (d⁻¹ + 2) ^ 2 ≤ (5 * d⁻¹) ^ 2 := pow_le_pow_left₀ hdi0 hdi 2
    have hK0 : 0 ≤ K := by linarith
    rw [mollified, norm_mul, norm_mul, ← hd, le_div_iff₀ (by positivity)]
    have hzC : ‖zetaEntire (1 - u)⁻¹‖ ≤ K * (5 * d⁻¹) ^ 2 :=
      hz.trans (mul_le_mul_of_nonneg_left hsq hK0)
    calc d * ‖zetaEntire (1 - u)⁻¹‖ * ‖Complex.exp (Q.eval u)‖ * d ^ 2
        ≤ d * (K * (5 * d⁻¹) ^ 2) * C * d ^ 2 := by
          gcongr
          exact hC u hu
      _ = 25 * K * C * d := by
          field_simp
          ring
      _ ≤ 50 * K * C := by
          have : 0 ≤ K * C := by positivity
          nlinarith
  · refine ⟨2 * C, fun x hx hx1 => ?_⟩
    have hu0 : (x : ℂ) ≠ 0 := by
      intro h
      have : x = 0 := by exact_mod_cast h
      linarith
    have hu1 : (x : ℂ) ≠ 1 := by
      intro h
      have : x = 1 := by exact_mod_cast h
      linarith
    have hxn : ‖(x : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact hx1.le
    have hre : 2 ≤ ((1 - (x : ℂ))⁻¹).re := by
      have e : (1 - (x : ℂ))⁻¹ = (((1 - x)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [e, Complex.ofReal_re, le_inv_comm₀ (by norm_num) (by linarith)]
      linarith
    have hz := (norm_riemannZeta_bounds_of_two_le_re hre).2
    rw [mollified_eq hu0 hu1, norm_mul, norm_mul]
    calc ‖(x : ℂ)‖ * ‖riemannZeta (1 - (x : ℂ))⁻¹‖ * ‖Complex.exp (Q.eval (x : ℂ))‖
        ≤ 1 * 2 * C := by
          gcongr
          exact hC _ hxn
      _ = 2 * C := by ring

/-! ### The rigidity law -/

/-- **The rigidity law.** -/
theorem norm_sub_one_sq_le {Q : Polynomial ℂ} (hQ : Q.coeff 0 = 0) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖zetaEntire s / s * polyMollifier 1 Q s - 1‖ ^ 2 ≤
      (budget 1 Q - 1) * (‖s - 1‖ ^ 2 / (2 * s.re - 1)) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    linarith
  have hu : ‖blaschkeCoord 1 s‖ < 1 := norm_blaschkeCoord_lt_one (by norm_num) hs
  set u := blaschkeCoord 1 s with hud
  have hue : u = (s - 1) / s := blaschkeCoord_one s
  have h1 : (1 : ℂ) - u = s⁻¹ := by
    rw [hue]
    field_simp
    ring
  have hval : mollified Q u = zetaEntire s / s * polyMollifier 1 Q s := by
    rw [mollified, h1, inv_inv, polyMollifier, ← hud]
    field_simp
  have hB := (isHardyDisc_mollified Q).norm_sub_sq_le hu
  rw [hval, mollified_zero hQ, (integrable_and_circleAverage_mollified Q).2, norm_one, one_pow] at hB
  refine hB.trans (le_of_eq ?_)
  congr 1
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hdiff : ‖s‖ ^ 2 - ‖s - 1‖ ^ 2 = 2 * s.re - 1 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  have hun : ‖u‖ = ‖s - 1‖ / ‖s‖ := by rw [hue, norm_div]
  have hd : 0 < 2 * s.re - 1 := by linarith
  have e1 : 1 - ‖u‖ ^ 2 = (2 * s.re - 1) / ‖s‖ ^ 2 := by
    rw [hun, div_pow, ← hdiff]
    field_simp
  rw [e1, hun, div_pow]
  field_simp

/-- **A single zero costs.** Every budget is at least `|ρ|²/|ρ − 1|²`. -/
theorem le_budget_of_zero {Q : Polynomial ℂ} (hQ : Q.coeff 0 = 0) {ρ : ℂ} (hρ : 1 / 2 < ρ.re)
    (h0 : riemannZeta ρ = 0) : ‖ρ‖ ^ 2 / ‖ρ - 1‖ ^ 2 ≤ budget 1 Q := by
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    exact riemannZeta_one_ne_zero h0
  have hz : zetaEntire ρ = 0 := by rw [zetaEntire_eq hρ1, h0, mul_zero]
  have h := norm_sub_one_sq_le hQ hρ
  rw [hz, zero_div, zero_mul, zero_sub, norm_neg, norm_one, one_pow] at h
  have hd : 0 < 2 * ρ.re - 1 := by linarith
  have hn : 0 < ‖ρ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hρ1)
  have hdiff : ‖ρ‖ ^ 2 = ‖ρ - 1‖ ^ 2 + (2 * ρ.re - 1) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  rw [hdiff, div_le_iff₀ (by positivity)]
  rw [mul_div_assoc', le_div_iff₀ hd] at h
  nlinarith

/-- **The limit is forced.** Along any family with budgets tending to `1`, `E M_{Q_k} → 1` at every point of the half-plane. -/
theorem tendsto_of_tendsto_budget {Q : ℕ → Polynomial ℂ} (hQ : ∀ k, (Q k).coeff 0 = 0)
    (hB : Tendsto (fun k => budget 1 (Q k)) atTop (𝓝 1)) {s : ℂ} (hs : 1 / 2 < s.re) :
    Tendsto (fun k => zetaEntire s / s * polyMollifier 1 (Q k) s) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set R := ‖s - 1‖ ^ 2 / (2 * s.re - 1) with hR
  have h1 : Tendsto (fun k => (budget 1 (Q k) - 1) * R) atTop (𝓝 0) := by
    have := (hB.sub_const 1).mul_const R
    simpa using this
  have h2 : Tendsto (fun k => ‖zetaEntire s / s * polyMollifier 1 (Q k) s - 1‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun k => norm_sub_one_sq_le (hQ k) hs) h1
  have h3 := h2.sqrt
  simpa [Real.sqrt_sq, norm_nonneg] using h3

/-- **RH is the existence of a near-extremal family, and its limit is `1/E`.** -/
theorem riemannHypothesis_iff_exists_near_extremal :
    RiemannHypothesis ↔ ∃ Q : ℕ → Polynomial ℂ, (∀ k, (Q k).coeff 0 = 0) ∧
      Tendsto (fun k => budget 1 (Q k)) atTop (𝓝 1) ∧
      ∀ s : ℂ, 1 / 2 < s.re → Tendsto (fun k => zetaEntire s / s * polyMollifier 1 (Q k) s) atTop (𝓝 1) := by
  constructor
  · intro hRH
    have h := riemannHypothesis_iff_exists_budget_lt.mp hRH
    choose Q hQ hlt using fun k : ℕ => h (1 / ((k : ℝ) + 1)) (by positivity)
    have hB : Tendsto (fun k => budget 1 (Q k)) atTop (𝓝 1) := by
      have hlim : Tendsto (fun k : ℕ => 1 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at hlim
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun k => one_le_budget_one (hQ k)) fun k => (hlt k).le
    exact ⟨Q, hQ, hB, fun s hs => tendsto_of_tendsto_budget hQ hB hs⟩
  · rintro ⟨Q, hQ, hB, -⟩
    refine riemannHypothesis_iff_exists_budget_lt.mpr fun ε hε => ?_
    obtain ⟨k, hk⟩ := (hB.eventually (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + ε))).exists
    exact ⟨Q k, hQ k, hk⟩

/-! ### The coefficients are forced -/

/-- **Bessel for a mollifier.** `Σ_{k≥1} |a_k|² ≤ B(Q) − 1`. -/
theorem sum_taylorCoeff_le {Q : Polynomial ℂ} (hQ : Q.coeff 0 = 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, ‖taylorCoeff (mollified Q) (k + 1)‖ ^ 2 ≤ budget 1 Q - 1 := by
  have h := (isHardyDisc_mollified Q).sum_norm_sq_le (n + 1)
  rw [Finset.sum_range_succ', (integrable_and_circleAverage_mollified Q).2] at h
  have h0 : taylorCoeff (mollified Q) 0 = 1 := mollified_zero hQ
  rw [h0, norm_one, one_pow] at h
  linarith

/-- `(s − 1)ζ(s)` has derivative `γ` at `1`. -/
theorem hasDerivAt_zetaEntire_one : HasDerivAt zetaEntire (Real.eulerMascheroniConstant : ℂ) 1 := by
  rw [hasDerivAt_iff_tendsto_slope]
  refine tendsto_riemannZeta_sub_one_div.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [slope_def_field, zetaEntire_eq hs, zetaEntire_eval_one]
  field_simp

/-- **The first coefficient is forced.** `|q₁ − (1 − γ)|² ≤ B(Q) − 1`. -/
theorem norm_coeff_one_add_le {Q : Polynomial ℂ} (hQ : Q.coeff 0 = 0) :
    ‖Q.coeff 1 - (1 - (Real.eulerMascheroniConstant : ℂ))‖ ^ 2 ≤ budget 1 Q - 1 := by
  have h := sum_taylorCoeff_le hQ 1
  rw [Finset.sum_range_one] at h
  have e : taylorCoeff (mollified Q) 1 = Q.coeff 1 - (1 - (Real.eulerMascheroniConstant : ℂ)) := by
    have h1 : taylorCoeff (mollified Q) 1 = deriv (mollified Q) 0 := by
      rw [taylorCoeff, zero_add ,peel_succ, peel_zero, dslope_same]
    rw [h1]
    have hinv : HasDerivAt (fun u : ℂ => (1 - u)⁻¹) 1 0 := by
      have h2 : HasDerivAt (fun u : ℂ => 1 - u) (-1) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
      have h3 := h2.fun_inv (by simp)
      simpa using h3
    have hz : HasDerivAt (fun u : ℂ => zetaEntire (1 - u)⁻¹) (Real.eulerMascheroniConstant : ℂ) 0 := by
      have h4 : HasDerivAt zetaEntire (Real.eulerMascheroniConstant : ℂ) ((1 - (0 : ℂ))⁻¹) := by
        simpa using hasDerivAt_zetaEntire_one
      simpa using h4.comp (0 : ℂ) hinv
    have hl : HasDerivAt (fun u : ℂ => 1 - u) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
    have hF := hl.fun_mul hz
    have hexp : HasDerivAt (fun u : ℂ => Complex.exp (Q.eval u)) (Complex.exp (Q.eval 0) * Q.coeff 1) 0 := by
      have h5 := Q.hasDerivAt 0
      have e5 : Polynomial.eval 0 (Polynomial.derivative Q) = Q.coeff 1 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
        simp
      rw [e5] at h5
      exact h5.cexp
    have hall := hF.fun_mul hexp
    have hd : deriv (mollified Q) 0 = _ := hall.deriv
    rw [hd, ← Polynomial.coeff_zero_eq_eval_zero, hQ, sub_zero, inv_one, zetaEntire_eval_one]
    simp
    ring
  rw [e] at h
  exact h

/-! ### Flattening -/

/-- `(x − 1)² ≤ 2(x − 1 − log x)(1 + x)` for `x > 0`. -/
theorem sq_sub_one_le {x : ℝ} (hx : 0 < x) : (x - 1) ^ 2 ≤ 2 * (x - 1 - Real.log x) * (1 + x) := by
  set k : ℝ → ℝ := fun y => 2 * (y - 1 - Real.log y) * (1 + y) - (y - 1) ^ 2 with hk
  have hd : ∀ y : ℝ, 0 < y → HasDerivAt k (2 * (y - y⁻¹ - Real.log y)) y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => z - 1 - Real.log z) (1 - y⁻¹) y :=
      ((hasDerivAt_id y).sub_const 1).fun_sub (Real.hasDerivAt_log hy.ne')
    have h2 : HasDerivAt (fun z : ℝ => 1 + z) 1 y := by
      simpa using (hasDerivAt_id y).const_add 1
    have h3 := ((h1.const_mul 2).fun_mul h2).fun_sub (((hasDerivAt_id y).sub_const 1).fun_pow 2)
    refine h3.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hk1 : k 1 = 0 := by simp [hk]
  have hcont : ContinuousOn k (Ioi 0) := fun y hy => (hd y hy).continuousAt.continuousWithinAt
  rcases le_total 1 x with h1 | h1
  · have hmono : MonotoneOn k (Ici 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
        (hcont.mono fun y hy => lt_of_lt_of_le one_pos hy)
        (fun y hy => ?_) (fun y hy => ?_)
      · rw [interior_Ici] at hy
        have hy0 : 0 < y := lt_trans one_pos hy
        exact (hd y hy0).differentiableAt.differentiableWithinAt
      · rw [interior_Ici] at hy
        have hy1 : 1 < y := hy
        have hy0 : 0 < y := lt_trans one_pos hy
        rw [(hd y hy0).deriv]
        have h2 := Real.log_le_sub_one_of_pos hy0
        have h3 : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy1.le
        linarith
    have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr h1) h1
    rw [hk1] at this
    simp only [hk] at this
    linarith
  · have hanti : AntitoneOn k (Ioc 0 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 1) (hcont.mono fun y hy => hy.1)
        (fun y hy => ?_) (fun y hy => ?_)
      · rw [interior_Ioc] at hy
        exact (hd y hy.1).differentiableAt.differentiableWithinAt
      · rw [interior_Ioc] at hy
        rw [(hd y hy.1).deriv]
        have h2 := Real.one_sub_inv_le_log_of_pos hy.1
        have h3 := hy.2
        nlinarith
    have := hanti (mem_Ioc.mpr ⟨hx, h1⟩) (mem_Ioc.mpr ⟨one_pos, le_rfl⟩) h1
    rw [hk1] at this
    simp only [hk] at this
    linarith

/-- The pointwise form used for integration. -/
theorem abs_sub_one_le {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    |x - 1| ≤ (x - 1 - Real.log x) / t + t * (1 + x) / 2 := by
  have hψ : 0 ≤ x - 1 - Real.log x := by
    have := Real.log_le_sub_one_of_pos hx
    linarith
  have hR : 0 ≤ (x - 1 - Real.log x) / t + t * (1 + x) / 2 := by positivity
  refine abs_le_of_sq_le_sq ?_ hR
  have h := sq_sub_one_le hx
  have e : ((x - 1 - Real.log x) / t + t * (1 + x) / 2) ^ 2 -
      2 * (x - 1 - Real.log x) * (1 + x) =
      ((x - 1 - Real.log x) / t - t * (1 + x) / 2) ^ 2 := by
    field_simp
    ring
  nlinarith [sq_nonneg ((x - 1 - Real.log x) / t - t * (1 + x) / 2)]

/-- **Stability of Jensen on a probability space.** `∫ |U/A − 1| ≤ 2√(log A − ∫ log U)`, `A = ∫ U`. -/
theorem integral_abs_div_sub_one_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {U : X → ℝ} (hpos : ∀ᵐ x ∂μ, 0 < U x) (hint : Integrable U μ)
    (hlog : Integrable (fun x => Real.log (U x)) μ) :
    ∫ x, |U x / (∫ y, U y ∂μ) - 1| ∂μ ≤
      2 * Real.sqrt (Real.log (∫ y, U y ∂μ) - ∫ x, Real.log (U x) ∂μ) := by
  set A := ∫ y, U y ∂μ with hA
  set L := ∫ x, Real.log (U x) ∂μ with hL
  have hJ : Real.exp L ≤ A := by
    have h := exp_integral_log_le (μ := μ) hpos hint hlog (g := fun _ => 0) measurable_const
      ⟨0, fun _ => by simp⟩ (by simp)
    simpa using h
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hJ
  have hδ : 0 ≤ Real.log A - L := by
    have := Real.log_le_log (Real.exp_pos L) hJ
    rw [Real.log_exp] at this
    linarith
  have hint1 : Integrable (fun x => |U x / A - 1|) μ :=
    ((hint.div_const A).sub (integrable_const 1)).abs
  have hbound : ∀ t : ℝ, 0 < t → ∫ x, |U x / A - 1| ∂μ ≤ (Real.log A - L) / t + t := by
    intro t ht
    set a := (1 / t + t / 2) / A with ha
    set c := (Real.log A - 1) / t + t / 2 with hc
    have hR : Integrable (fun x => a * U x + (-(1 / t)) * Real.log (U x) + c) μ :=
      ((hint.const_mul a).add (hlog.const_mul _)).add (integrable_const c)
    have hle : ∫ x, |U x / A - 1| ∂μ ≤ ∫ x, a * U x + (-(1 / t)) * Real.log (U x) + c ∂μ := by
      refine integral_mono_ae hint1 hR ?_
      filter_upwards [hpos] with x hx
      have hxA : 0 < U x / A := div_pos hx hApos
      have h := abs_sub_one_le hxA ht
      refine h.trans (le_of_eq ?_)
      rw [Real.log_div hx.ne' hApos.ne', ha, hc]
      field_simp
      ring
    refine hle.trans (le_of_eq ?_)
    rw [integral_add ((hint.const_mul a).add (hlog.const_mul _)) (integrable_const c),
      integral_add (hint.const_mul a) (hlog.const_mul _), integral_const_mul, integral_const_mul,
      integral_const, ← hA, ← hL, ha, hc]
    simp
    field_simp
    ring
  rcases hδ.eq_or_lt with h0 | hpos'
  · rw [← h0, Real.sqrt_zero, mul_zero]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := hbound ε hε
    rw [← h0, zero_div, zero_add] at this
    linarith
  · have hs := Real.sqrt_pos.mpr hpos'
    have := hbound _ hs
    have e : (Real.log A - L) / Real.sqrt (Real.log A - L) = Real.sqrt (Real.log A - L) :=
      Real.div_sqrt
    rw [e] at this
    linarith

/-- **Near-extremal mollifiers flatten `ζ`**, at any inner mass:
`∫ | |ζ M_Q|²/B − 1 | P₁ ≤ 2√(log B − 2I(1))`. -/
theorem integral_abs_flatten_le {Q : Polynomial ℂ} (hQ : Q.coeff 0 = 0) :
    ∫ τ : ℝ, |‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 *
        ‖Complex.exp (Q.eval (blaschkeCoord 1 (1 / 2 + τ * I)))‖ ^ 2 / budget 1 Q - 1| *
        halfPlanePoissonKernel 1 τ ≤
      2 * Real.sqrt (Real.log (budget 1 Q) - 2 * innerField 1) := by
  have hw : (1 / 2 : ℝ) < (1 : ℂ).re := by norm_num
  set G : ℂ → ℝ := fun z => chartWeight 1 z * ‖Complex.exp (Q.eval z)‖ ^ 2 with hG
  have hGm : Measurable G := (measurable_chartWeight 1).mul
    ((Complex.continuous_exp.comp Q.continuous).norm.pow 2).measurable
  have hline : ∀ t : ℝ, G (circleMap 0 1 (criticalLineAngle t)) =
      ‖riemannZeta (1 / 2 + (((2 * (1 : ℂ).re - 1) * t + (1 : ℂ).im : ℝ) : ℂ) * I)‖ ^ 2 *
        ‖Complex.exp (Q.eval (blaschkeCoord 1 (1 / 2 + (((2 * (1 : ℂ).re - 1) * t + (1 : ℂ).im : ℝ) : ℂ) * I)))‖ ^ 2 := by
    intro t
    simp only [hG, chartWeight, discChart_circleMap, blaschkeCoord_line hw]
  have hP := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num) (fun τ : ℝ =>
    ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * ‖Complex.exp (Q.eval (blaschkeCoord 1 (1 / 2 + τ * I)))‖ ^ 2)
    G hline
  have hB : Real.circleAverage G 0 1 = budget 1 Q := hP.2
  have hint : CircleIntegrable G 0 1 := by
    have h1 := (integrable_and_circleAverage_mollified Q).1
    refine hP.1.mpr ?_
    have h2 := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num) (fun τ : ℝ =>
      ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * ‖Complex.exp (Q.eval (blaschkeCoord 1 (1 / 2 + τ * I)))‖ ^ 2)
      (fun z => ‖mollified Q z‖ ^ 2) (fun t => by
        set u := circleMap 0 1 (criticalLineAngle t) with hu
        have hu1 : u ≠ 1 := circleMap_criticalLineAngle_ne_one t
        have hun : ‖u‖ = 1 := norm_circleMap_zero_one _
        have hu0 : u ≠ 0 := fun h => by
          rw [h, norm_zero] at hun
          exact zero_ne_one hun
        have hs := discChart_circleMap 1 t
        rw [discChart_one, ← hu] at hs
        have hb := blaschkeCoord_line (w := 1) hw t
        rw [← hu] at hb
        simp only
        rw [hb, ← hs, mollified_eq hu0 hu1, norm_mul, norm_mul, hun, one_mul, mul_pow])
    exact h2.1.mp h1
  have hUi : Integrable (fun x : 𝕋 => G (circleZ x)) AddCircle.haarAddCircle :=
    (integrable_haar_circleZ_iff hGm).mpr hint
  have hlogW : Integrable (fun x : 𝕋 => Real.log (chartWeight 1 (circleZ x))) AddCircle.haarAddCircle := by
    have hl := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num)
      (fun τ : ℝ => 2 * Real.log ‖riemannZeta (1 / 2 + τ * I)‖) (fun z => Real.log (chartWeight 1 z))
      (fun t => by simp only [chartWeight, discChart_circleMap, Real.log_pow]; norm_num)
    refine (integrable_haar_circleZ_iff (Real.measurable_log.comp (measurable_chartWeight 1))).mpr
      (hl.1.mpr ?_)
    have := (integrable_log_zeta_poisson (w := 1) (by norm_num)).const_mul 2
    refine this.congr (Eventually.of_forall fun τ => ?_)
    simp only
    ring
  have hpos0 := ae_chartWeight_pos (w := 1) (by norm_num)
  have hlogU : ∀ᵐ x : 𝕋 ∂AddCircle.haarAddCircle, Real.log (G (circleZ x)) =
      Real.log (chartWeight 1 (circleZ x)) + circleValue Q x := by
    filter_upwards [hpos0] with x hx
    simp only [hG, circleValue]
    rw [Real.log_mul hx.ne' (by positivity), Real.log_pow, Complex.norm_exp, Real.log_exp]
    norm_num
  have hUl : Integrable (fun x : 𝕋 => Real.log (G (circleZ x))) AddCircle.haarAddCircle := by
    have hb : Integrable (circleValue Q) AddCircle.haarAddCircle :=
      (continuous_circleValue Q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    exact (hlogW.add hb).congr (hlogU.mono fun x hx => hx.symm)
  have hpos : ∀ᵐ x : 𝕋 ∂AddCircle.haarAddCircle, 0 < G (circleZ x) := by
    filter_upwards [hpos0] with x hx
    exact mul_pos hx (by positivity)
  have hS := integral_abs_div_sub_one_le hpos hUi hUl
  have eA : ∫ x : 𝕋, G (circleZ x) ∂AddCircle.haarAddCircle = budget 1 Q := by
    rw [integral_haar_circleZ, hB]
  have eL : ∫ x : 𝕋, Real.log (G (circleZ x)) ∂AddCircle.haarAddCircle = 2 * innerField 1 := by
    rw [integral_congr_ae hlogU, integral_add hlogW
      ((continuous_circleValue Q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_circleValue hQ, add_zero, integral_haar_circleZ fun z => Real.log (chartWeight 1 z)]
    have hl := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num)
      (fun τ : ℝ => 2 * Real.log ‖riemannZeta (1 / 2 + τ * I)‖) (fun z => Real.log (chartWeight 1 z))
      (fun t => by simp only [chartWeight, discChart_circleMap, Real.log_pow]; norm_num)
    rw [hl.2, innerField, norm_one, Real.log_one, zetaEntire_eval_one, norm_one, Real.log_one, ← integral_const_mul]
    simp only [add_zero, sub_zero]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only
    ring
  rw [eA, eL] at hS
  refine le_trans (le_of_eq ?_) hS
  have hA := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num) (fun τ : ℝ =>
    |‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * ‖Complex.exp (Q.eval (blaschkeCoord 1 (1 / 2 + τ * I)))‖ ^ 2 /
      budget 1 Q - 1|) (fun z => |G z / budget 1 Q - 1|) (fun t => by
        simp only
        rw [hline t])
  rw [← hA.2, integral_haar_circleZ fun z => |G z / budget 1 Q - 1|]

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
