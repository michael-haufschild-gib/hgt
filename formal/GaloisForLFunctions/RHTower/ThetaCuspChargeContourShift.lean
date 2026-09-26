import GaloisForLFunctions.RHTower.ThetaGroupCuspChargeTail
import GaloisForLFunctions.RHTower.StripHorizontalShift

open Complex MeasureTheory Filter Topology
open scoped Real

namespace RHTower

noncomputable section

/-- Holomorphic extension of the tail `½e^{x/2}F(ie^{2x})` into the strip `|Im z| < π/4`. -/
def chargeTailC (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (z / 2) * F (Complex.I * Complex.exp (2 * z)) / 2

theorem chargeTailC_ofReal (F : ℂ → ℂ) (x : ℝ) : chargeTailC F (x : ℂ) = modTail F 0 x := by
  unfold chargeTailC modTail modAxisPoint
  rw [sub_zero, Complex.ofReal_exp, Complex.ofReal_exp]
  push_cast
  ring_nf

theorem im_I_mul_cexp_two_mul (z : ℂ) :
    (Complex.I * Complex.exp (2 * z)).im = Real.exp (2 * z.re) * Real.cos (2 * z.im) := by
  simp [Complex.mul_im, Complex.exp_re, Complex.mul_re]

theorem norm_cexp_half (z : ℂ) : ‖Complex.exp (z / 2)‖ = Real.exp (z.re / 2) := by
  rw [Complex.norm_exp]; congr 1; simp

theorem im_I_mul_cexp_pos {z : ℂ} (hz : |z.im| < π / 4) :
    0 < (Complex.I * Complex.exp (2 * z)).im := by
  rw [im_I_mul_cexp_two_mul]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have := neg_abs_le z.im; linarith
  · have := le_abs_self z.im; linarith

theorem cos_two_le_of_abs_le {y β : ℝ} (hβ : β < π / 4) (hy : |y| ≤ β) :
    Real.cos (2 * β) ≤ Real.cos (2 * y) := by
  rw [← Real.cos_abs (2 * y), abs_mul, abs_two]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  linarith

section Strip

variable {F : ℂ → ℂ} {M : ℝ}

theorem differentiableAt_chargeTailC (hF : DifferentiableOn ℂ F modUpperSet) {z : ℂ}
    (hz : |z.im| < π / 4) : DifferentiableAt ℂ (chargeTailC F) z := by
  have hmem : Complex.I * Complex.exp (2 * z) ∈ modUpperSet := im_I_mul_cexp_pos hz
  have hFz : DifferentiableAt ℂ F (Complex.I * Complex.exp (2 * z)) :=
    hF.differentiableAt (isOpen_modUpperSet.mem_nhds hmem)
  have hin : DifferentiableAt ℂ (fun z : ℂ => Complex.I * Complex.exp (2 * z)) z := by fun_prop
  unfold chargeTailC
  exact ((Complex.differentiable_exp.comp (differentiable_id.div_const 2)).differentiableAt.mul
    (hFz.comp z hin)).div_const 2

theorem continuousOn_chargeTailC (hF : DifferentiableOn ℂ F modUpperSet) {β : ℝ}
    (hβ : β < π / 4) : ContinuousOn (chargeTailC F) {z : ℂ | |z.im| ≤ β} := fun _ hz =>
  (differentiableAt_chargeTailC hF (lt_of_le_of_lt hz hβ)).continuousAt.continuousWithinAt

/-- Inversion moves the point `ie^{2z}` to `ie^{-2z}`. -/
theorem neg_one_div_I_mul_cexp (z : ℂ) :
    -1 / (Complex.I * Complex.exp (-2 * z)) = Complex.I * Complex.exp (2 * z) := by
  rw [div_eq_iff (mul_ne_zero Complex.I_ne_zero (Complex.exp_ne_zero _))]
  have h1 : Complex.exp (2 * z) * Complex.exp (-2 * z) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  linear_combination (-Complex.I ^ 2) * h1 - Complex.I_sq

theorem norm_cpow_half_cexp_neg (z : ℂ) :
    ‖(-Complex.I * (Complex.I * Complex.exp (-2 * z))) ^ (1 / 2 : ℂ)‖ = Real.exp (-z.re) := by
  have h : -Complex.I * (Complex.I * Complex.exp (-2 * z)) = Complex.exp (-2 * z) := by
    rw [← mul_assoc, neg_mul, Complex.I_mul_I]; ring
  rw [h, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real,
    Complex.norm_exp, ← Real.exp_mul]
  congr 1; simp; ring

/-- Two-sided cusp bound for the complex tail on a closed substrip. -/
theorem norm_chargeTailC_le_cusp
    (hS : ∀ τ : ℂ, 0 < τ.im → F (-1 / τ) = (-Complex.I * τ) ^ (1 / 2 : ℂ) * F τ)
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ‖ ≤ M * Real.exp (-π * τ.im))
    {β : ℝ} (hβ : β < π / 4) {z : ℂ} (hz : |z.im| ≤ β) :
    (1 ≤ Real.exp (2 * z.re) * Real.cos (2 * β) →
      ‖chargeTailC F z‖ ≤ M / 2 * Real.exp (z.re / 2) *
        Real.exp (-π * (Real.exp (2 * z.re) * Real.cos (2 * β)))) ∧
    (1 ≤ Real.exp (-2 * z.re) * Real.cos (2 * β) →
      ‖chargeTailC F z‖ ≤ M / 2 * Real.exp (-z.re / 2) *
        Real.exp (-π * (Real.exp (-2 * z.re) * Real.cos (2 * β)))) := by
  have hcos := cos_two_le_of_abs_le hβ hz
  have hM : 0 ≤ M := by
    have h := hdec Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-π * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  constructor
  · intro h1
    have him : Real.exp (2 * z.re) * Real.cos (2 * β) ≤ (Complex.I * Complex.exp (2 * z)).im := by
      rw [im_I_mul_cexp_two_mul]
      exact mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le
    have hb := hdec _ (le_trans h1 him)
    have hb' : ‖F (Complex.I * Complex.exp (2 * z))‖ ≤
        M * Real.exp (-π * (Real.exp (2 * z.re) * Real.cos (2 * β))) := by
      refine le_trans hb (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM)
      nlinarith [Real.pi_pos]
    unfold chargeTailC
    rw [norm_div, norm_mul, norm_cexp_half, Complex.norm_ofNat]
    have := mul_le_mul_of_nonneg_left hb' (Real.exp_pos (z.re / 2)).le
    nlinarith [this]
  · intro h1
    have him : Real.exp (-2 * z.re) * Real.cos (2 * β) ≤
        (Complex.I * Complex.exp (-2 * z)).im := by
      rw [show -2 * z = 2 * (-z) by ring, im_I_mul_cexp_two_mul]
      simp only [Complex.neg_re, Complex.neg_im, mul_neg]
      rw [Real.cos_neg, show -(2 * z.re) = -2 * z.re by ring]
      exact mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le
    have hpos : 0 < (Complex.I * Complex.exp (-2 * z)).im :=
      lt_of_lt_of_le one_pos (le_trans h1 him)
    have hrefl := hS _ hpos
    rw [neg_one_div_I_mul_cexp] at hrefl
    have hb := hdec _ (le_trans h1 him)
    have hb' : ‖F (Complex.I * Complex.exp (-2 * z))‖ ≤
        M * Real.exp (-π * (Real.exp (-2 * z.re) * Real.cos (2 * β))) := by
      refine le_trans hb (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM)
      nlinarith [Real.pi_pos]
    unfold chargeTailC
    rw [hrefl, norm_div, norm_mul, norm_mul, norm_cexp_half, norm_cpow_half_cexp_neg,
      Complex.norm_ofNat]
    have hx : Real.exp (z.re / 2) * Real.exp (-z.re) = Real.exp (-z.re / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have := mul_le_mul_of_nonneg_left hb' (Real.exp_pos (-z.re / 2)).le
    calc Real.exp (z.re / 2) * (Real.exp (-z.re) * ‖F (Complex.I * Complex.exp (-2 * z))‖) / 2
        = Real.exp (-z.re / 2) * ‖F (Complex.I * Complex.exp (-2 * z))‖ / 2 := by
          rw [← hx]; ring
      _ ≤ M / 2 * Real.exp (-z.re / 2) *
          Real.exp (-π * (Real.exp (-2 * z.re) * Real.cos (2 * β))) := by nlinarith [this]

/-- A double exponential beats the single exponential it multiplies. -/
theorem exp_half_mul_exp_neg_pi_le {x κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (h1 : 1 ≤ Real.exp (2 * x) * κ) :
    Real.exp (x / 2) * Real.exp (-π * (Real.exp (2 * x) * κ)) ≤ 1 / (π * κ) * Real.exp (-x) := by
  have hx0 : 0 ≤ x := by
    by_contra hneg
    push Not at hneg
    have : Real.exp (2 * x) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
    nlinarith
  have hYpos : 0 < Real.exp (2 * x) * κ := by positivity
  have hle : Real.exp (x / 2) * Real.exp x ≤ Real.exp (2 * x) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hexpY : π * (Real.exp (2 * x) * κ) ≤ Real.exp (π * (Real.exp (2 * x) * κ)) := by
    have := Real.add_one_le_exp (π * (Real.exp (2 * x) * κ)); linarith
  have hkey : Real.exp (x / 2) * Real.exp x * Real.exp (-π * (Real.exp (2 * x) * κ)) ≤
      1 / (π * κ) := by
    rw [show -π * (Real.exp (2 * x) * κ) = -(π * (Real.exp (2 * x) * κ)) by ring, Real.exp_neg]
    rw [mul_inv_le_iff₀ (Real.exp_pos _)]
    calc Real.exp (x / 2) * Real.exp x ≤ Real.exp (2 * x) := hle
      _ = 1 / (π * κ) * (π * (Real.exp (2 * x) * κ)) := by field_simp
      _ ≤ 1 / (π * κ) * Real.exp (π * (Real.exp (2 * x) * κ)) :=
          mul_le_mul_of_nonneg_left hexpY (by positivity)
  have hex : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hm := mul_le_mul_of_nonneg_right hkey (Real.exp_pos (-x)).le
  calc Real.exp (x / 2) * Real.exp (-π * (Real.exp (2 * x) * κ))
      = Real.exp (x / 2) * Real.exp (-π * (Real.exp (2 * x) * κ)) *
          (Real.exp x * Real.exp (-x)) := by rw [hex, mul_one]
    _ = Real.exp (x / 2) * Real.exp x * Real.exp (-π * (Real.exp (2 * x) * κ)) *
          Real.exp (-x) := by ring
    _ ≤ 1 / (π * κ) * Real.exp (-x) := hm

/-- Existential decay of the complex tail on every closed substrip. -/
theorem exists_norm_chargeTailC_le (hF : DifferentiableOn ℂ F modUpperSet)
    (hS : ∀ τ : ℂ, 0 < τ.im → F (-1 / τ) = (-Complex.I * τ) ^ (1 / 2 : ℂ) * F τ)
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ‖ ≤ M * Real.exp (-π * τ.im))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ β → ‖chargeTailC F z‖ ≤ C * Real.exp (-|z.re|) := by
  have hM : 0 ≤ M := by
    have h := hdec Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-π * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  set κ := Real.cos (2 * β) with hκ
  have hκpos : 0 < κ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hκ1 : κ ≤ 1 := Real.cos_le_one _
  set X₀ : ℝ := Real.log (1 / κ) / 2 with hX₀
  set K : Set ℂ := {z : ℂ | |z.re| ≤ X₀ ∧ |z.im| ≤ β} with hK
  have hKc : IsCompact K := by
    have : K = (fun z : ℂ => (z.re, z.im)) ⁻¹' (Set.Icc (-X₀) X₀ ×ˢ Set.Icc (-β) β) := by
      ext z; simp [hK, abs_le]; tauto
    rw [this]
    exact (Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage).mpr
      ((isCompact_Icc).prod isCompact_Icc)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn
    ((continuousOn_chargeTailC hF hβ).mono (fun z hz => hz.2))
  set B' : ℝ := max B 0 with hB'
  refine ⟨max (B' * Real.exp X₀) (M / 2 * (1 / (π * κ))), le_max_of_le_left (by positivity), ?_⟩
  intro z hz
  obtain ⟨hA, hBc⟩ := norm_chargeTailC_le_cusp hS hdec hβ hz
  by_cases h1 : 1 ≤ Real.exp (2 * z.re) * κ
  · have hx0 : 0 ≤ z.re := by
      by_contra hneg; push Not at hneg
      have : Real.exp (2 * z.re) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      nlinarith
    have := hA h1
    have hkey := exp_half_mul_exp_neg_pi_le hκpos hκ1 h1
    rw [abs_of_nonneg hx0]
    calc ‖chargeTailC F z‖ ≤ M / 2 * (Real.exp (z.re / 2) *
          Real.exp (-π * (Real.exp (2 * z.re) * κ))) := by rw [← mul_assoc]; exact this
      _ ≤ M / 2 * (1 / (π * κ) * Real.exp (-z.re)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ max (B' * Real.exp X₀) (M / 2 * (1 / (π * κ))) * Real.exp (-z.re) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  by_cases h2 : 1 ≤ Real.exp (-2 * z.re) * κ
  · have hx0 : z.re ≤ 0 := by
      by_contra hneg; push Not at hneg
      have : Real.exp (-2 * z.re) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      nlinarith
    have := hBc h2
    have hkey := exp_half_mul_exp_neg_pi_le (x := -z.re) hκpos hκ1
      (by rw [show 2 * -z.re = -2 * z.re by ring]; exact h2)
    rw [abs_of_nonpos hx0]
    calc ‖chargeTailC F z‖ ≤ M / 2 * (Real.exp (-z.re / 2) *
          Real.exp (-π * (Real.exp (-2 * z.re) * κ))) := by rw [← mul_assoc]; exact this
      _ = M / 2 * (Real.exp (-z.re / 2) *
          Real.exp (-π * (Real.exp (2 * -z.re) * κ))) := by ring_nf
      _ ≤ M / 2 * (1 / (π * κ) * Real.exp (- -z.re)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ max (B' * Real.exp X₀) (M / 2 * (1 / (π * κ))) * Real.exp (- -z.re) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · push Not at h1 h2
    have hlog : Real.log (1 / κ) = -Real.log κ := by rw [one_div, Real.log_inv]
    have hre : |z.re| ≤ X₀ := by
      rw [abs_le]
      have hl1 : 2 * z.re + Real.log κ < 0 := by
        have := Real.log_lt_log (by positivity) h1
        rw [Real.log_mul (Real.exp_pos _).ne' hκpos.ne', Real.log_exp, Real.log_one] at this
        exact this
      have hl2 : -2 * z.re + Real.log κ < 0 := by
        have := Real.log_lt_log (by positivity) h2
        rw [Real.log_mul (Real.exp_pos _).ne' hκpos.ne', Real.log_exp, Real.log_one] at this
        exact this
      rw [hX₀, hlog]
      constructor <;> linarith
    have hbd := hB z ⟨hre, hz⟩
    have hexp : 1 ≤ Real.exp X₀ * Real.exp (-|z.re|) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    calc ‖chargeTailC F z‖ ≤ B' := le_trans hbd (le_max_left _ _)
      _ ≤ B' * (Real.exp X₀ * Real.exp (-|z.re|)) := le_mul_of_one_le_right (le_max_right _ _) hexp
      _ = B' * Real.exp X₀ * Real.exp (-|z.re|) := by ring
      _ ≤ max (B' * Real.exp X₀) (M / 2 * (1 / (π * κ))) * Real.exp (-|z.re|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- **Contour shift of the tail transform to the line `Im z = -β`.** -/
theorem integral_tail_shift (hF : DifferentiableOn ℂ F modUpperSet)
    (hS : ∀ τ : ℂ, 0 < τ.im → F (-1 / τ) = (-Complex.I * τ) ^ (1 / 2 : ℂ) * F τ)
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ‖ ≤ M * Real.exp (-π * τ.im))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 4) (u : ℝ) :
    (∫ x : ℝ, Complex.exp (-Complex.I * u * x) * modTail F 0 x) =
      Complex.exp (-(u * β : ℝ)) * ∫ s : ℝ, Complex.exp (-Complex.I * u * s) *
        chargeTailC F ((s : ℂ) - (β : ℂ) * Complex.I) := by
  obtain ⟨C, hC, hbd⟩ := exists_norm_chargeTailC_le hF hS hdec hβ0 hβ
  set G : ℂ → ℂ := fun z => Complex.exp (-Complex.I * u * z) * chargeTailC F z with hG
  set G' : ℂ → ℂ := fun z => G (-z) with hG'
  have hdiff : ∀ z : ℂ, |z.im| ≤ β → DifferentiableAt ℂ G' z := by
    intro z hz
    have hz' : |(-z).im| < π / 4 := by rw [Complex.neg_im, abs_neg]; linarith
    have h1 : DifferentiableAt ℂ G (-z) :=
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (-Complex.I * u * z)) (-z)).mul
        (differentiableAt_chargeTailC hF hz')
    exact h1.comp z differentiableAt_id.neg
  have hbound : ∀ z : ℂ, |z.im| ≤ β →
      ‖G' z‖ ≤ (Real.exp (|u| * β) * C) * Real.exp (-(1 * |z.re|)) := by
    intro z hz
    have hz' : |(-z).im| ≤ β := by rw [Complex.neg_im, abs_neg]; exact hz
    have h1 := hbd (-z) hz'
    rw [Complex.neg_re, abs_neg] at h1
    have hexp : ‖Complex.exp (-Complex.I * u * -z)‖ ≤ Real.exp (|u| * β) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have : (-Complex.I * (u : ℂ) * -z).re = -(u * z.im) := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [this]
      have := abs_mul u z.im
      have h3 : |u| * |z.im| ≤ |u| * β := mul_le_mul_of_nonneg_left hz (abs_nonneg u)
      have h4 := neg_abs_le (u * z.im)
      linarith
    simp only [hG', hG, norm_mul]
    rw [one_mul]
    calc ‖Complex.exp (-Complex.I * u * -z)‖ * ‖chargeTailC F (-z)‖
        ≤ Real.exp (|u| * β) * (C * Real.exp (-|z.re|)) :=
          mul_le_mul hexp h1 (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (|u| * β) * C * Real.exp (-|z.re|) := by ring
  have hshift := integral_horizontal_shift_of_decay hβ0 one_pos hdiff hbound
  simp only [hG', hG] at hshift
  have hL : (∫ x : ℝ, Complex.exp (-Complex.I * u * -((x : ℂ) + (β : ℂ) * Complex.I)) *
      chargeTailC F (-((x : ℂ) + (β : ℂ) * Complex.I))) =
      ∫ s : ℝ, Complex.exp (-Complex.I * u * ((s : ℂ) - (β : ℂ) * Complex.I)) *
        chargeTailC F ((s : ℂ) - (β : ℂ) * Complex.I) := by
    rw [← integral_neg_eq_self]
    congr 1; funext s; push_cast; ring_nf
  have hR : (∫ x : ℝ, Complex.exp (-Complex.I * u * -(x : ℂ)) * chargeTailC F (-(x : ℂ))) =
      ∫ x : ℝ, Complex.exp (-Complex.I * u * x) * modTail F 0 x := by
    rw [← integral_neg_eq_self]
    congr 1; funext x; push_cast; rw [neg_neg, chargeTailC_ofReal]
  rw [← hR, ← hshift, hL, ← integral_const_mul]
  congr 1; funext s
  have : Complex.exp (-Complex.I * u * ((s : ℂ) - (β : ℂ) * Complex.I)) =
      Complex.exp (-(u * β : ℝ)) * Complex.exp (-Complex.I * u * s) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [this]; ring

end Strip

end

end RHTower
