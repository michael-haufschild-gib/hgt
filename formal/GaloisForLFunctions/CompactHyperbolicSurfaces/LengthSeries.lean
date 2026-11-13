import GaloisForLFunctions.CompactHyperbolicSurfaces.PrimitiveClasses

/-!
# The length series

`Φ(s) = Σ_{[γ] ≠ 1} ℓ₀ e^{−sℓ}/(1 − e^{−ℓ})` converges absolutely on `Re s > 1` and is holomorphic
there (`differentiableOn_lengthSeries`).  Convergence comes from the trace formula: with
`b = σ + 1`, `g_{σ,b}(ℓ) ≥ (1/(2σ−1) − 1/(2b−1)) e^{−σℓ}/(1 − e^{−ℓ})` (`geomWeight_ge`).

In these terms the trace formula reads, for real `1 < a < b`,
`Σ_j ν_j = |F| D_{a,b}(0) + Φ(a)/(2a−1) − Φ(b)/(2b−1)` (`trace_formula_lengthSeries`).
-/

open MeasureTheory Set Real
open scoped MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

theorem exp_div_two_sinh {a ℓ : ℝ} (hℓ : 0 < ℓ) :
    exp (-((a - 1 / 2) * ℓ)) / (2 * sinh (ℓ / 2)) = exp (-(a * ℓ)) / (1 - exp (-ℓ)) := by
  have h1 : 0 < 1 - exp (-ℓ) := by have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hℓ); linarith
  have hs : 2 * sinh (ℓ / 2) = exp (ℓ / 2) * (1 - exp (-ℓ)) := by
    rw [Real.sinh_eq, mul_sub, mul_one, ← Real.exp_add]; ring_nf
  have he : exp (-((a - 1 / 2) * ℓ)) = exp (-(a * ℓ)) * exp (ℓ / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [hs, he]
  field_simp

theorem geomWeight_eq {a b ℓ : ℝ} (hℓ : 0 < ℓ) :
    geomWeight a b ℓ = (exp (-(a * ℓ)) / (2 * a - 1) - exp (-(b * ℓ)) / (2 * b - 1)) /
      (1 - exp (-ℓ)) := by
  have h1 := exp_div_two_sinh (a := a) hℓ
  have h2 := exp_div_two_sinh (a := b) hℓ
  rw [geomWeight]
  calc (exp (-((a - 1 / 2) * ℓ)) / (2 * a - 1) - exp (-((b - 1 / 2) * ℓ)) / (2 * b - 1)) /
        (2 * sinh (ℓ / 2))
      = exp (-((a - 1 / 2) * ℓ)) / (2 * sinh (ℓ / 2)) / (2 * a - 1) -
          exp (-((b - 1 / 2) * ℓ)) / (2 * sinh (ℓ / 2)) / (2 * b - 1) := by ring
    _ = _ := by rw [h1, h2]; ring

theorem geomWeight_ge {a b ℓ : ℝ} (ha : 1 / 2 < a) (hab : a < b) (hℓ : 0 < ℓ) :
    (1 / (2 * a - 1) - 1 / (2 * b - 1)) * (exp (-(a * ℓ)) / (1 - exp (-ℓ))) ≤
      geomWeight a b ℓ := by
  have h1 : 0 < 1 - exp (-ℓ) := by have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hℓ); linarith
  have hb : 0 < 2 * b - 1 := by linarith
  have he : exp (-(b * ℓ)) ≤ exp (-(a * ℓ)) := Real.exp_le_exp.mpr (by nlinarith)
  rw [geomWeight_eq hℓ, ← mul_div_assoc, div_le_div_iff_of_pos_right h1]
  have : exp (-(b * ℓ)) / (2 * b - 1) ≤ exp (-(a * ℓ)) / (2 * b - 1) :=
    div_le_div_of_nonneg_right he hb.le
  have e : (1 / (2 * a - 1) - 1 / (2 * b - 1)) * exp (-(a * ℓ)) =
      exp (-(a * ℓ)) / (2 * a - 1) - exp (-(a * ℓ)) / (2 * b - 1) := by ring
  linarith

namespace CompactQuotient

variable {X : CompactQuotient} (hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|)

/-- The real weight `ℓ₀ e^{−σℓ}/(1 − e^{−ℓ})` of a class. -/
def realWeight (X : CompactQuotient) (σ : ℝ) (c : X.NClass) : ℝ :=
  X.classPrimLen c * exp (-(σ * X.classLen c)) / (1 - exp (-X.classLen c))

/-- The complex weight `ℓ₀ e^{−sℓ}/(1 − e^{−ℓ})` of a class. -/
def classWeight (X : CompactQuotient) (s : ℂ) (c : X.NClass) : ℂ :=
  (X.classPrimLen c : ℂ) * Complex.exp (-(s * X.classLen c)) / ((1 - exp (-X.classLen c) : ℝ) : ℂ)

/-- **The length series** `Φ(s) = Σ_{[γ] ≠ 1} ℓ₀ e^{−sℓ}/(1 − e^{−ℓ})`. -/
def lengthSeries (X : CompactQuotient) (s : ℂ) : ℂ := ∑' c : X.NClass, X.classWeight s c

include hhyp

theorem one_sub_exp_pos (c : X.NClass) : 0 < 1 - exp (-X.classLen c) := by
  have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (X.classLen_pos hhyp c.2)); linarith

theorem realWeight_nonneg (σ : ℝ) (c : X.NClass) : 0 ≤ X.realWeight σ c :=
  div_nonneg (mul_nonneg (X.classPrimLen_pos hhyp c.2).le (exp_pos _).le)
    (one_sub_exp_pos hhyp c).le

theorem summable_realWeight {σ : ℝ} (hσ : 1 < σ) : Summable (X.realWeight σ) := by
  obtain ⟨hsum, -⟩ := X.trace_formula hhyp hσ (lt_add_one σ)
  have hκ : 0 < 1 / (2 * σ - 1) - 1 / (2 * (σ + 1) - 1) := by
    rw [sub_pos]; exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  refine Summable.of_nonneg_of_le (realWeight_nonneg hhyp σ) (fun c => ?_)
    (hsum.mul_left (1 / (1 / (2 * σ - 1) - 1 / (2 * (σ + 1) - 1))))
  have h := geomWeight_ge (b := σ + 1) (by linarith : 1 / 2 < σ) (lt_add_one σ)
    (X.classLen_pos hhyp c.2)
  have hp := X.classPrimLen_pos hhyp c.2
  rw [realWeight, mul_div_assoc]
  replace h : exp (-(σ * X.classLen c)) / (1 - exp (-X.classLen c)) ≤
      geomWeight σ (σ + 1) (X.classLen c) / (1 / (2 * σ - 1) - 1 / (2 * (σ + 1) - 1)) := by
    rw [le_div_iff₀ hκ]; linarith [h]
  calc X.classPrimLen c * (exp (-(σ * X.classLen c)) / (1 - exp (-X.classLen c)))
      ≤ X.classPrimLen c * (geomWeight σ (σ + 1) (X.classLen c) /
          (1 / (2 * σ - 1) - 1 / (2 * (σ + 1) - 1))) := mul_le_mul_of_nonneg_left h hp.le
    _ = _ := by ring

theorem norm_classWeight (s : ℂ) (c : X.NClass) : ‖X.classWeight s c‖ = X.realWeight s.re c := by
  have hp := X.classPrimLen_pos hhyp c.2
  have h1 := one_sub_exp_pos hhyp c
  rw [classWeight, realWeight, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_exp, Real.norm_of_nonneg hp.le, Real.norm_of_nonneg h1.le]
  congr 3
  simp [Complex.mul_re]

theorem summable_classWeight {s : ℂ} (hs : 1 < s.re) : Summable (X.classWeight s) :=
  Summable.of_norm (by simpa only [norm_classWeight hhyp] using summable_realWeight hhyp hs)

/-- **`Φ` is holomorphic on `Re s > 1`.** -/
theorem differentiableOn_lengthSeries : DifferentiableOn ℂ X.lengthSeries {s | 1 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 1 < s₀.re := hs₀
  set σ := (1 + s₀.re) / 2
  have hσ : 1 < σ := by simp only [σ]; linarith
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ X.lengthSeries {s : ℂ | σ < s.re} := by
    refine Complex.differentiableOn_tsum_of_summable_norm (summable_realWeight hhyp hσ)
      (fun c => ?_) hU (fun c s hs => ?_)
    · intro s _
      unfold classWeight
      fun_prop
    · rw [norm_classWeight hhyp]
      unfold realWeight
      have hp := X.classPrimLen_pos hhyp c.2
      have h1 := one_sub_exp_pos hhyp c
      have hl := X.classLen_pos hhyp c.2
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr ?_) hp.le) h1.le
      have : σ < s.re := hs
      nlinarith
  have hmem : s₀ ∈ {s : ℂ | σ < s.re} := by show σ < s₀.re; simp only [σ]; linarith
  exact ((hdiff s₀ hmem).differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

omit hhyp in
theorem lengthSeries_ofReal (σ : ℝ) :
    X.lengthSeries σ = ((∑' c : X.NClass, X.realWeight σ c : ℝ) : ℂ) := by
  rw [lengthSeries, Complex.ofReal_tsum]
  refine tsum_congr fun c => ?_
  rw [classWeight, realWeight]
  push_cast
  ring_nf

/-- **The trace formula in terms of `Φ`.**  For real `1 < a < b`,
`Σ_j ν_j = |F| D_{a,b}(0) + Φ(a)/(2a−1) − Φ(b)/(2b−1)`. -/
theorem trace_formula_lengthSeries {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    ∑' j, X.nu ha (b := b) j = (volume X.F).toReal * diffKernel a b 0 +
      (∑' c : X.NClass, X.realWeight a c) / (2 * a - 1) -
        (∑' c : X.NClass, X.realWeight b c) / (2 * b - 1) := by
  obtain ⟨-, htr⟩ := X.trace_formula hhyp ha hab
  rw [htr, add_sub_assoc]
  congr 1
  have hb : 1 < b := lt_trans ha hab
  rw [← tsum_div_const, ← tsum_div_const, ← Summable.tsum_sub
    ((summable_realWeight hhyp ha).div_const _) ((summable_realWeight hhyp hb).div_const _)]
  refine tsum_congr fun c => ?_
  rw [geomWeight_eq (X.classLen_pos hhyp c.2), realWeight, realWeight]
  have h1 := one_sub_exp_pos hhyp c
  have ha2 : 2 * a - 1 ≠ 0 := by linarith
  have hb2 : 2 * b - 1 ≠ 0 := by linarith
  field_simp

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
