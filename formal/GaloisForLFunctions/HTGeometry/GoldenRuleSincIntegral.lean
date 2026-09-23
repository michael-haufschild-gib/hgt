import GaloisForLFunctions.RHTower.PaleyWienerNorms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The sinc-square normalization `∫_ℝ sin(a x)² / x² dx = π a`

Fermi's golden rule is the statement that a first-order transition probability grows linearly in
time with slope `2 π` times a density of states.  The constant `2 π` is fixed by a single definite
integral, the total mass of the squared cardinal sine,

```text
∫_ℝ sin(a x)² / x² dx = π a      (a ≥ 0),      equivalently   ∫_ℝ sinc² = π .
```

Mathlib defines `Real.sinc` but proves nothing about its integral, so this identity is a genuine
gap.  The proof here is Plancherel applied to the *flat* compactly supported spectrum: the
synthesis integral of the constant spectrum `1` on `[-k, k]` is `2 sin(w k)/w`, and the corpus
theorem `integral_norm_sq_compactFourier` equates its energy with the window length `2k`.
No oscillatory-integral analysis and no Dirichlet integral are needed.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Closed form of the flat compactly supported synthesis integral.**  At a nonzero real
frequency `w` the constant spectrum `1` on `[-k, k]` synthesises `2 sin(w k) / w`. -/
theorem compactFourier_one_eq (k : ℝ) {w : ℝ} (hw : w ≠ 0) :
    compactFourier (fun _ => (1 : ℂ)) (-k) k ((w : ℝ) : ℂ)
      = ((2 * Real.sin (w * k) / w : ℝ) : ℂ) := by
  have hc : (Complex.I * (w : ℂ)) ≠ 0 := by
    simp [Complex.I_ne_zero, hw]
  have hrw : compactFourier (fun _ => (1 : ℂ)) (-k) k ((w : ℝ) : ℂ)
      = ∫ x in (-k)..k, Complex.exp ((Complex.I * (w : ℂ)) * (x : ℂ)) := by
    rw [compactFourier]
    refine intervalIntegral.integral_congr ?_
    intro x _
    simp [mul_assoc]
  rw [hrw, integral_exp_mul_complex hc]
  have e1 : (Complex.I * (w : ℂ)) * ((k : ℝ) : ℂ) = ((w * k : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have e2 : (Complex.I * (w : ℂ)) * ((-k : ℝ) : ℂ) = (-(w * k : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I]
  have hcos : Complex.cos (-(((w * k : ℝ)) : ℂ)) = Complex.cos (((w * k : ℝ)) : ℂ) :=
    Complex.cos_neg _
  have hsin : Complex.sin (-(((w * k : ℝ)) : ℂ)) = -Complex.sin (((w * k : ℝ)) : ℂ) :=
    Complex.sin_neg _
  rw [show ((-(w * k : ℝ) : ℂ)) = -(((w * k : ℝ)) : ℂ) by push_cast; ring, hcos, hsin]
  rw [← Complex.ofReal_sin]
  field_simp
  push_cast
  ring

/-- **`∫_ℝ sin(a x)² / x² dx = π a`.**  The normalization constant behind Fermi's golden rule. -/
theorem integral_sin_sq_div_sq {a : ℝ} (ha : 0 ≤ a) :
    ∫ x : ℝ, Real.sin (a * x) ^ (2 : ℕ) / x ^ (2 : ℕ) = Real.pi * a := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set k : ℝ := a / (2 * Real.pi) with hkdef
  have hk : 0 ≤ k := div_nonneg ha (by positivity)
  have h2pik : 2 * Real.pi * k = a := by
    rw [hkdef]; field_simp
  have hkey := GaloisForLFunctions.RHTower.integral_norm_sq_compactFourier
    (H := fun _ => (1 : ℂ)) continuous_const hk
  have hrhs : (∫ _v in Icc (-k) k, ‖(1 : ℂ)‖ ^ (2 : ℕ)) = 2 * k := by
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le (by linarith)]
    simp
    ring
  have hlhs : (∫ x : ℝ, ‖compactFourier (fun _ => (1 : ℂ)) (-k) k ((2 * Real.pi * x : ℝ) : ℂ)‖ ^ (2 : ℕ))
      = ∫ x : ℝ, (Real.pi ^ (2 : ℕ))⁻¹ * (Real.sin (a * x) ^ (2 : ℕ) / x ^ (2 : ℕ)) := by
    refine MeasureTheory.integral_congr_ae ?_
    have hnull : (volume : Measure ℝ) {(0 : ℝ)} = 0 := by simp
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hw : (2 * Real.pi * x) ≠ 0 := by positivity
    rw [compactFourier_one_eq k hw, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hwk : (2 * Real.pi * x) * k = a * x := by
      rw [show (2 * Real.pi * x) * k = (2 * Real.pi * k) * x by ring, h2pik]
    rw [hwk]
    field_simp
  rw [hlhs, MeasureTheory.integral_const_mul, hrhs] at hkey
  have hpi2 : (Real.pi ^ (2 : ℕ)) ≠ 0 := by positivity
  field_simp at hkey
  rw [hkdef] at hkey
  field_simp at hkey
  linarith [hkey]

/-- **`∫_ℝ sinc² = π`.**  Mathlib's `Real.sinc` has unit-normalized square mass `π`. -/
theorem integral_sinc_sq : ∫ x : ℝ, Real.sinc x ^ (2 : ℕ) = Real.pi := by
  have h := integral_sin_sq_div_sq (a := 1) zero_le_one
  rw [mul_one] at h
  rw [← h]
  refine MeasureTheory.integral_congr_ae ?_
  have hnull : (volume : Measure ℝ) {(0 : ℝ)} = 0 := by simp
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  rw [Real.sinc_of_ne_zero hx0, one_mul]
  field_simp

end GaloisForLFunctions.HTGeometry
