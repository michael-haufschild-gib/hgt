import GaloisForLFunctions.RHTower.WallEvenAmplitudeBounds
import GaloisForLFunctions.HTGeometry.InverseFamilyThirdDerivative

/-!
# The third frequency jet of the wall generator

The generator's scalar part is `r(x+iσ)/2 − i/(2z)` up to the fixed operator term, and its `j`-th
frequency derivative is the `j`-th symbol jet plus the corresponding branch power.  The third
derivative is therefore

`r₃(z)/2 − 3i/z⁴`,

and the symbol bound `‖r^{(m+1)}(t)‖ ≤ 2(m+1)!(1+π/2)/|t|^{m+1}` makes it `O((1+|t|)^{-3})` on both
frequency rays.

That cubic decay is what the third integration by parts consumes: the amplitude `∂D₂` is `O(w³)`
exactly when the symbol's three derivatives are `O(w)`, `O(w²)`, `O(w³)`.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The third frequency derivative of the scalar part of the generator. -/
def wallScalarD3 (σ t : ℝ) : ℂ :=
  wallSymbolJet σ 3 t / 2 - 3 * Complex.I / ((t : ℂ) + (σ : ℂ) * Complex.I) ^ (4 : ℕ)

/-- The third branch power differentiates to the fourth. -/
theorem hasDerivAt_branchTermD2 {σ : ℝ} (hσ0 : 0 < σ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.I / ((s : ℂ) + (σ : ℂ) * Complex.I) ^ (3 : ℕ))
      (-(3 * Complex.I / ((t : ℂ) + (σ : ℂ) * Complex.I) ^ (4 : ℕ))) t := by
  have hzne : ((t : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := shiftedLine_ne_zero hσ0 t
  have hcube : ((t : ℂ) + (σ : ℂ) * Complex.I) ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 hzne
  have hline := hasDerivAt_shiftedLine σ t
  have hpow : HasDerivAt (fun s : ℝ => ((s : ℂ) + (σ : ℂ) * Complex.I) ^ (3 : ℕ))
      (3 * ((t : ℂ) + (σ : ℂ) * Complex.I) ^ (2 : ℕ)) t := by
    have h := hline.pow 3
    refine h.congr_deriv ?_
    push_cast
    ring
  have hinv := hpow.inv hcube
  have hI0 := hinv.const_mul Complex.I
  have hI1 : HasDerivAt (fun s : ℝ => Complex.I / ((s : ℂ) + (σ : ℂ) * Complex.I) ^ (3 : ℕ))
      (Complex.I * (-(3 * ((t : ℂ) + (σ : ℂ) * Complex.I) ^ (2 : ℕ))
        / (((t : ℂ) + (σ : ℂ) * Complex.I) ^ (3 : ℕ)) ^ (2 : ℕ))) t := by
    simpa [div_eq_mul_inv] using hI0
  refine hI1.congr_deriv ?_
  field_simp

/-- The scalar symbol is three times differentiable. -/
theorem hasDerivAt_wallScalarD2 {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    HasDerivAt (wallScalarD2 σ) (wallScalarD3 σ t) t := by
  have h1 := (hasDerivAt_wallSymbolJet hσ0 hσ1 2 t).div_const 2
  have h2 := hasDerivAt_branchTermD2 hσ0 t
  have hsum0 := h1.add h2
  have hfun : (wallScalarD2 σ) = ((fun x : ℝ => wallSymbolJet σ 2 x / 2)
      + fun s : ℝ => Complex.I / ((s : ℂ) + (σ : ℂ) * Complex.I) ^ (3 : ℕ)) := by
    funext s
    simp only [Pi.add_apply]
    rw [wallScalarD2]
  have hsum1 : HasDerivAt (wallScalarD2 σ)
      (wallSymbolJet σ (2 + 1) t / 2
        + -(3 * Complex.I / ((t : ℂ) + (σ : ℂ) * Complex.I) ^ (4 : ℕ))) t := by
    rw [hfun]
    exact hsum0
  refine hsum1.congr_deriv ?_
  rw [wallScalarD3]
  norm_num
  ring

/-- **The third frequency derivative of the scalar symbol is `O((1+|t|)^{-3})`.** -/
theorem norm_wallScalarD3_le' {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖wallScalarD3 σ t‖ ≤ (72 + 24 * Real.pi) * ((1 + |t|)⁻¹) ^ (3 : ℕ) := by
  have ht0 : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hjet := norm_wallSymbolJet_succ_le hσ0 hσ1 ht 2
  have hz : |t| ≤ ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ := norm_shiftedLine_ge t
  have hz0 : (0 : ℝ) < ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ := lt_of_lt_of_le ht0 hz
  have hj3 : ‖wallSymbolJet σ 3 t‖ ≤ (12 + 6 * Real.pi) / |t| ^ (3 : ℕ) := by
    have hpow : |t| ^ (2 + 1) = |t| ^ (3 : ℕ) := by norm_num
    have hfact : (((2 + 1 : ℕ)).factorial : ℝ) = 6 := by norm_num
    have hj := hjet
    rw [hpow, hfact] at hj
    calc ‖wallSymbolJet σ 3 t‖ ≤ 2 * 6 * (1 + Real.pi / 2) / |t| ^ (3 : ℕ) := by simpa using hj
      _ = (12 + 6 * Real.pi) / |t| ^ (3 : ℕ) := by ring_nf
  have hfirst : ‖wallSymbolJet σ 3 t / 2‖ ≤ (6 + 3 * Real.pi) / |t| ^ (3 : ℕ) := by
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    calc ‖wallSymbolJet σ 3 t‖ / 2 ≤ ((12 + 6 * Real.pi) / |t| ^ (3 : ℕ)) / 2 := by gcongr
      _ = (6 + 3 * Real.pi) / |t| ^ (3 : ℕ) := by ring
  have hbranch : ‖3 * Complex.I / ((t : ℂ) + (σ : ℂ) * Complex.I) ^ (4 : ℕ)‖ ≤ 3 / |t| ^ (3 : ℕ) := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, norm_pow]
    have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    rw [h3]
    have hp4 : |t| ^ (4 : ℕ) ≤ ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ ^ (4 : ℕ) :=
      pow_le_pow_left₀ ht0.le hz 4
    have hcube : |t| ^ (3 : ℕ) ≤ |t| ^ (4 : ℕ) := by nlinarith [pow_pos ht0 3]
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    linarith
  have hsum : ‖wallScalarD3 σ t‖ ≤ (6 + 3 * Real.pi) / |t| ^ (3 : ℕ) + 3 / |t| ^ (3 : ℕ) := by
    rw [wallScalarD3]
    exact le_trans (norm_sub_le _ _) (add_le_add hfirst hbranch)
  refine hsum.trans ?_
  have hinv : 1 / |t| ^ (3 : ℕ) ≤ 8 * ((1 + |t|)⁻¹) ^ (3 : ℕ) := by
    have h1 : (1 : ℝ) + |t| ≤ 2 * |t| := by linarith
    have h2 : (0 : ℝ) < 1 + |t| := by linarith
    rw [inv_pow, ← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos ht0 3, pow_pos h2 3, pow_le_pow_left₀ h2.le h1 3]
  have hkey := mul_le_mul_of_nonneg_left hinv (by linarith : (0 : ℝ) ≤ 9 + 3 * Real.pi)
  calc (6 + 3 * Real.pi) / |t| ^ (3 : ℕ) + 3 / |t| ^ (3 : ℕ) = (9 + 3 * Real.pi) * (1 / |t| ^ (3 : ℕ)) := by ring
    _ ≤ (9 + 3 * Real.pi) * (8 * ((1 + |t|)⁻¹) ^ (3 : ℕ)) := hkey
    _ = (72 + 24 * Real.pi) * ((1 + |t|)⁻¹) ^ (3 : ℕ) := by ring

/-- The third derivative is continuous. -/
theorem continuous_wallScalarD3 {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous (wallScalarD3 σ) := by
  have hjet : Continuous (wallSymbolJet σ 3) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_wallSymbolJet hσ0 hσ1 3 t).continuousAt
  have hline : Continuous fun s : ℝ => (s : ℂ) + (σ : ℂ) * Complex.I := by fun_prop
  have hden : Continuous fun s : ℝ => ((s : ℂ) + (σ : ℂ) * Complex.I) ^ (4 : ℕ) := hline.pow 4
  have hne : ∀ s : ℝ, ((s : ℂ) + (σ : ℂ) * Complex.I) ^ (4 : ℕ) ≠ 0 := fun s =>
    pow_ne_zero 4 (shiftedLine_ne_zero hσ0 s)
  have h : Continuous fun s : ℝ =>
      wallSymbolJet σ 3 s / 2 - 3 * Complex.I / ((s : ℂ) + (σ : ℂ) * Complex.I) ^ (4 : ℕ) :=
    (hjet.div_const 2).sub (continuous_const.div hden hne)
  exact h

section Operator

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- The third frequency derivative of the generator. -/
def wallGeneratorD3 (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (σ : ℝ) (t : ℝ) : X →L[ℂ] X :=
  wallScalarD3 σ t • ContinuousLinearMap.id ℂ X

/-- The operator form of the third derivative. -/
theorem hasDerivAt_wallGeneratorD2 {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    HasDerivAt (wallGeneratorD2 X σ) (wallGeneratorD3 X σ t) t := by
  have h : HasDerivAt (fun s : ℝ => wallScalarD2 σ s • (ContinuousLinearMap.id ℂ X))
      (wallScalarD3 σ t • ContinuousLinearMap.id ℂ X) t :=
    (hasDerivAt_wallScalarD2 hσ0 hσ1 t).smul_const _
  exact h

omit [CompleteSpace X] in
/-- The operator form of the third derivative bound. -/
theorem norm_wallGeneratorD3_le' {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖wallGeneratorD3 X σ t‖ ≤ (72 + 24 * Real.pi) * ((1 + |t|)⁻¹) ^ (3 : ℕ) :=
  (norm_smul_id_le _).trans (norm_wallScalarD3_le' hσ0 hσ1 ht)

omit [CompleteSpace X] in
/-- The operator form is continuous. -/
theorem continuous_wallGeneratorD3 {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous (wallGeneratorD3 X σ) := by
  have h : Continuous fun t : ℝ => wallScalarD3 σ t • (ContinuousLinearMap.id ℂ X) :=
    (continuous_wallScalarD3 hσ0 hσ1).smul continuous_const
  exact h

/-- The constant of the amplitude surviving three integrations by parts. -/
def wallAmplitude3Const (μ₀ : ℝ) : ℝ :=
  ((μ₀⁻¹) ^ (2 : ℕ) * (3 + Real.pi))
      * (3 * (μ₀⁻¹) ^ (4 : ℕ) * (3 + Real.pi) ^ (2 : ℕ) + (μ₀⁻¹) ^ (3 : ℕ) * (4 * (3 + Real.pi)))
    + μ₀⁻¹ * (3 * (2 * (μ₀⁻¹) ^ (3 : ℕ) * (3 + Real.pi) ^ (2 : ℕ) + (μ₀⁻¹) ^ (2 : ℕ) * (4 * (3 + Real.pi)))
        * ((μ₀⁻¹) ^ (2 : ℕ) * (3 + Real.pi))
      + μ₀⁻¹ * (6 * (μ₀⁻¹) ^ (4 : ℕ) * (3 + Real.pi) ^ (3 : ℕ)
        + 6 * (μ₀⁻¹) ^ (3 : ℕ) * (3 + Real.pi) * (4 * (3 + Real.pi))
        + (μ₀⁻¹) ^ (2 : ℕ) * (72 + 24 * Real.pi)))

/-- **The amplitude surviving three integrations by parts decays cubically.** -/
theorem norm_invFamilyProduct2Deriv_wallGeneratorShift_le' {T : X →L[ℂ] X} {σ L μ₀ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀) {t : ℝ} (ht : 1 ≤ |t|)
    (hfloor : μ₀ ≤ wallFloor T σ t + L) :
    ‖invFamilyProduct2Deriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
        (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) t‖
      ≤ wallAmplitude3Const μ₀ * ((1 + |t|)⁻¹) ^ (3 : ℕ) := by
  rw [wallAmplitude3Const]
  exact norm_invFamilyProduct2Deriv_le (by positivity)
    (norm_invFamily_wallGeneratorShift_le' hσ0 hσ1 hμ hfloor)
    (norm_wallGeneratorShiftD1_le' hσ0 hσ1 ht)
    (norm_wallGeneratorShiftD2_le' hσ0 hσ1 ht)
    (norm_wallGeneratorD3_le' hσ0 hσ1 ht)

end Operator

end GaloisForLFunctions.RHTower
