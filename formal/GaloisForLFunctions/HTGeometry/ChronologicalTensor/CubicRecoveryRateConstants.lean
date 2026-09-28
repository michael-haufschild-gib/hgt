import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The constants of the recovery rate

Put `I(a) = ∫_0^{π/2} ds/(1 - a cos s)`.  For `a = cos θ`, `0 < θ < π`, the antiderivative
`(2/sin θ) arctan(cot(θ/2) tan(s/2))` gives the closed form

  `I(cos θ) = (π - θ)/sin θ`.

The equation `2(π - θ) = 3π sin θ` has exactly one solution `θ ∈ (0, π/2)` (its left side minus
right side is strictly decreasing, with opposite signs at the endpoints); with `b = cos θ` this is
`I(b) = 3π/2`.  The recovery rate is

  `ρ = (b²/16) exp((2/π) ∫_0^{π/2} log(1 - b cos s) ds)`,  `0 < ρ < b²/16 < 1/16`.
-/

open Set Filter intervalIntegral
open scoped Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- `I(a) = ∫_0^{π/2} ds/(1 - a cos s)`. -/
def recoveryI (a : ℝ) : ℝ := ∫ s in (0 : ℝ)..π / 2, 1 / (1 - a * Real.cos s)

/-- The rate function `ρ(b) = (b²/16) exp((2/π) ∫_0^{π/2} log(1 - b cos s) ds)`. -/
def recoveryRateFun (b : ℝ) : ℝ :=
  b ^ 2 / 16 * Real.exp (2 / π * ∫ s in (0 : ℝ)..π / 2, Real.log (1 - b * Real.cos s))

/-- **Closed form.** `I(cos θ) = (π - θ)/sin θ` for `0 < θ < π`. -/
theorem recoveryI_cos {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < π) :
    recoveryI (Real.cos θ) = (π - θ) / Real.sin θ := by
  set A := θ / 2 with hA
  have hA0 : 0 < A := by positivity
  have hAπ : A < π / 2 := by linarith
  have hsA : 0 < Real.sin A := Real.sin_pos_of_pos_of_lt_pi hA0 (by linarith)
  have hcA : 0 < Real.cos A := Real.cos_pos_of_mem_Ioo ⟨by linarith, hAπ⟩
  have hsθ : Real.sin θ = 2 * Real.sin A * Real.cos A := by
    rw [hA, ← Real.sin_two_mul]; ring_nf
  have hcθ : Real.cos θ = Real.cos A ^ 2 - Real.sin A ^ 2 := by
    rw [show θ = 2 * A by rw [hA]; ring, Real.cos_two_mul]
    linarith [Real.sin_sq_add_cos_sq A]
  set c := Real.cos A / Real.sin A with hc
  set G : ℝ → ℝ := fun s => 2 / Real.sin θ * Real.arctan (c * Real.tan (s / 2)) with hG
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) (π / 2), HasDerivAt G (1 / (1 - Real.cos θ * Real.cos s)) s := by
    intro s hs
    rw [uIcc_of_le (by positivity)] at hs
    set u := s / 2 with hu
    have hcu : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have htan : HasDerivAt Real.tan (1 / Real.cos u ^ 2) u := Real.hasDerivAt_tan hcu.ne'
    have hdiv : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const (2 : ℝ)
    have ht' := HasDerivAt.comp s (h₂ := Real.tan) (h := fun x : ℝ => x / 2) htan hdiv
    have ht : HasDerivAt (fun s : ℝ => Real.tan (s / 2)) (1 / Real.cos u ^ 2 * (1 / 2)) s := ht'
    have h1 := ((Real.hasDerivAt_arctan (c * Real.tan u)).comp s (ht.const_mul c)).const_mul
      (2 / Real.sin θ)
    refine h1.congr_deriv ?_
    have hcs : Real.cos s = Real.cos u ^ 2 - Real.sin u ^ 2 := by
      rw [show s = 2 * u by rw [hu]; ring, Real.cos_two_mul]
      linarith [Real.sin_sq_add_cos_sq u]
    have h1 := Real.sin_sq_add_cos_sq A
    have h2 := Real.sin_sq_add_cos_sq u
    have hkey : 1 - Real.cos θ * Real.cos s =
        2 * (Real.sin A ^ 2 * Real.cos u ^ 2 + Real.cos A ^ 2 * Real.sin u ^ 2) := by
      rw [hcθ, hcs]
      linear_combination (-(Real.sin u ^ 2 + Real.cos u ^ 2)) * h1 - h2
    have hpos : 0 < Real.sin A ^ 2 * Real.cos u ^ 2 + Real.cos A ^ 2 * Real.sin u ^ 2 := by
      have : 0 < Real.sin A ^ 2 * Real.cos u ^ 2 := by positivity
      nlinarith [sq_nonneg (Real.cos A * Real.sin u)]
    rw [hkey, Real.tan_eq_sin_div_cos, hsθ, hc]
    field_simp
  have hcont : IntervalIntegrable (fun s => 1 / (1 - Real.cos θ * Real.cos s)) MeasureTheory.volume
      0 (π / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun s hs => ?_
    rw [uIcc_of_le (by positivity)] at hs
    have hcs : Real.cos s ≤ 1 := Real.cos_le_one s
    have hcs0 : 0 ≤ Real.cos s := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1], hs.2⟩
    have hct : Real.cos θ < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0
      rwa [Real.cos_zero] at this
    rcases le_or_gt 0 (Real.cos θ) with h | h
    · nlinarith
    · nlinarith
  rw [recoveryI, integral_eq_sub_of_hasDerivAt hderiv hcont, hG]
  simp only [zero_div, Real.tan_zero, mul_zero, Real.arctan_zero]
  rw [show π / 2 / 2 = π / 4 by ring, Real.tan_pi_div_four, mul_one, hc,
    show Real.cos A / Real.sin A = Real.tan (π / 2 - A) by
      rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, inv_div],
    Real.arctan_tan (by linarith) (by linarith), hA]
  field_simp
  ring

/-- **The angle.** `2(π - θ) = 3π sin θ` has exactly one solution in `(0, π/2)`. -/
theorem existsUnique_recoveryAngle :
    ∃! θ : ℝ, θ ∈ Ioo 0 (π / 2) ∧ 2 * (π - θ) = 3 * π * Real.sin θ := by
  set f : ℝ → ℝ := fun θ => 2 * (π - θ) - 3 * π * Real.sin θ with hf
  have hπ := Real.pi_pos
  have hcont : ContinuousOn f (Icc 0 (π / 2)) := by fun_prop
  have hanti : StrictAntiOn f (Icc 0 (π / 2)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont fun θ hθ => ?_
    rw [interior_Icc] at hθ
    have hd : HasDerivAt f (-2 - 3 * π * Real.cos θ) θ := by
      have h1 : HasDerivAt (fun y : ℝ => 2 * (π - y)) (2 * (-1)) θ :=
        ((hasDerivAt_id θ).const_sub π).const_mul 2
      have h2 : HasDerivAt (fun y : ℝ => 3 * π * Real.sin y) (3 * π * Real.cos θ) θ :=
        (Real.hasDerivAt_sin θ).const_mul _
      exact (h1.sub h2).congr_deriv (by ring)
    rw [hd.deriv]
    have := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2.le⟩
    nlinarith
  have h0 : f 0 = 2 * π := by simp [hf]
  have hπ2 : f (π / 2) = -2 * π := by simp [hf]; ring
  obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_Icc' (by positivity) hcont
    (show (0 : ℝ) ∈ Icc (f (π / 2)) (f 0) by rw [h0, hπ2]; constructor <;> linarith)
  have hθ' : θ ∈ Ioo 0 (π / 2) := by
    refine ⟨lt_of_le_of_ne hθ.1 fun h => ?_, lt_of_le_of_ne hθ.2 fun h => ?_⟩
    · rw [← h, h0] at hθ0; linarith
    · rw [h, hπ2] at hθ0; linarith
  have hfθ : f θ = 0 := hθ0
  refine ⟨θ, ⟨hθ', by simp only [hf] at hfθ; linarith⟩, fun θ' ⟨hθ'', heq⟩ => ?_⟩
  have hfθ' : f θ' = 0 := by simp only [hf]; linarith
  exact hanti.injOn ⟨hθ''.1.le, hθ''.2.le⟩ ⟨hθ'.1.le, hθ'.2.le⟩ (hfθ'.trans hfθ.symm)

/-- The recovery angle `θ ∈ (0, π/2)` with `2(π - θ) = 3π sin θ`. -/
def recoveryAngle : ℝ := Classical.choose existsUnique_recoveryAngle.exists

theorem recoveryAngle_mem : recoveryAngle ∈ Ioo 0 (π / 2) :=
  (Classical.choose_spec existsUnique_recoveryAngle.exists).1

theorem recoveryAngle_eq : 2 * (π - recoveryAngle) = 3 * π * Real.sin recoveryAngle :=
  (Classical.choose_spec existsUnique_recoveryAngle.exists).2

/-- The support endpoint `b = cos θ`. -/
def recoveryEdge : ℝ := Real.cos recoveryAngle

theorem recoveryEdge_mem : recoveryEdge ∈ Ioo 0 1 := by
  obtain ⟨h0, h1⟩ := recoveryAngle_mem
  refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩, ?_⟩
  have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_pos]) h0
  rwa [Real.cos_zero] at this

/-- **`I(b) = 3π/2`.** -/
theorem recoveryI_edge : recoveryI recoveryEdge = 3 * π / 2 := by
  obtain ⟨h0, h1⟩ := recoveryAngle_mem
  have hs : 0 < Real.sin recoveryAngle := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  rw [recoveryEdge, recoveryI_cos h0 (by linarith), div_eq_iff hs.ne']
  linarith [recoveryAngle_eq]

/-- The exact recovery rate `ρ`. -/
def recoveryRate : ℝ := recoveryRateFun recoveryEdge

theorem integral_log_one_sub_mul_cos_neg {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    ∫ s in (0 : ℝ)..π / 2, Real.log (1 - b * Real.cos s) < 0 := by
  have hint : IntervalIntegrable (fun s => -Real.log (1 - b * Real.cos s)) MeasureTheory.volume
      0 (π / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (ContinuousOn.log (by fun_prop) fun s _ => ?_).neg
    have := Real.cos_le_one s; nlinarith [hb.1, hb.2]
  have hpos := intervalIntegral_pos_of_pos_on hint (fun s hs => by
    have hcos : 0 < Real.cos s := Real.cos_pos_of_mem_Ioo ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩
    have hc1 := Real.cos_le_one s
    have h1 : 1 - b * Real.cos s < 1 := by nlinarith [hb.1]
    have h0 : 0 < 1 - b * Real.cos s := by nlinarith [hb.2]
    exact neg_pos.mpr (Real.log_neg h0 h1)) (by positivity)
  rw [intervalIntegral.integral_neg] at hpos
  linarith

/-- **`0 < ρ(b) < b²/16`.** -/
theorem recoveryRateFun_bounds {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    0 < recoveryRateFun b ∧ recoveryRateFun b < b ^ 2 / 16 := by
  have hneg := integral_log_one_sub_mul_cos_neg hb
  have hb2 : 0 < b ^ 2 / 16 := by have := hb.1; positivity
  refine ⟨mul_pos hb2 (Real.exp_pos _), ?_⟩
  rw [recoveryRateFun]
  refine lt_of_lt_of_le (mul_lt_mul_of_pos_left (Real.exp_lt_one_iff.mpr ?_) hb2) (by rw [mul_one])
  exact mul_neg_of_pos_of_neg (by positivity) hneg

/-- **`0 < ρ < 1/16`.** -/
theorem recoveryRate_bounds : 0 < recoveryRate ∧ recoveryRate < 1 / 16 := by
  obtain ⟨h0, h1⟩ := recoveryRateFun_bounds recoveryEdge_mem
  refine ⟨h0, h1.trans_le ?_⟩
  have := recoveryEdge_mem
  rw [div_le_div_iff_of_pos_right (by norm_num)]
  nlinarith [this.1, this.2]

end GaloisForLFunctions.HTGeometry.ChronologicalTensor
