import GaloisForLFunctions.RHTower.WallGeneratorEquation

/-!
# Frequency derivatives of the shifted generator

The shifted generator `C(t,L) = B(t+iσ) + L·I` depends on the frequency only through the scalar
`r(t+iσ)/2 + i/(2z)`, so its frequency derivatives are scalar multiples of the identity.  The symbol
half is differentiated by the polygamma jets, whose vertical order is sharp; the branch half is the
elementary `i/(2z)`, with derivatives `−i/(2z²)` and `i/z³`.  Past unit frequency both halves obey
the same power law, and

`‖C'(t)‖ ≤ (3+π)(1+t)^{-1}`,   `‖C''(t)‖ ≤ 4(3+π)(1+t)^{-2}`,

with the constants coming only from the sharp polygamma bound `(m+1)!(1+π/2)|t|^{-(m+1)}` and from
`1+t ≤ 2t` on the terminal ray.  These are exactly the symbol-decay hypotheses that turn the
algebraic bounds on `[C⁻¹(C⁻¹)']'` into the quadratic decay of the amplitude surviving the two-fold
integration by parts.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The first frequency derivative of the scalar part of the generator. -/
def wallScalarD1 (σ t : ℝ) : ℂ :=
  wallSymbolJet σ 1 t / 2 - Complex.I / (2 * ((t : ℂ) + (σ : ℂ) * Complex.I) ^ 2)

/-- The second frequency derivative of the scalar part of the generator. -/
def wallScalarD2 (σ t : ℝ) : ℂ :=
  wallSymbolJet σ 2 t / 2 + Complex.I / ((t : ℂ) + (σ : ℂ) * Complex.I) ^ 3

theorem hasDerivAt_wallSymbol {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    HasDerivAt (wallSymbol σ) (wallSymbolJet σ 1 t) t := by
  have hbase := (hasDerivAt_wallSymbolJet hσ0 hσ1 0 t).add_const
    (2 * (Real.eulerMascheroniConstant : ℂ))
  have hfun : (fun x : ℝ => wallSymbolJet σ 0 x + 2 * (Real.eulerMascheroniConstant : ℂ))
      = wallSymbol σ := by
    funext x
    exact wallSymbolJet_zero σ x
  rw [hfun] at hbase
  exact hbase

theorem hasDerivAt_branchTerm {σ : ℝ} (hσ0 : 0 < σ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.I / (2 * ((s : ℂ) + (σ : ℂ) * Complex.I)))
      (-(Complex.I / (2 * ((t : ℂ) + (σ : ℂ) * Complex.I) ^ 2))) t := by
  have hzne : ((t : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := shiftedLine_ne_zero hσ0 t
  have h2z : (2 : ℂ) * ((t : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by norm_num) hzne
  have hline := hasDerivAt_shiftedLine σ t
  have hmul : HasDerivAt (fun s : ℝ => (2 : ℂ) * ((s : ℂ) + (σ : ℂ) * Complex.I)) 2 t := by
    simpa using hline.const_mul (2 : ℂ)
  have hinv := hmul.inv h2z
  have hI0 := hinv.const_mul Complex.I
  have hI : HasDerivAt (fun s : ℝ => Complex.I / (2 * ((s : ℂ) + (σ : ℂ) * Complex.I)))
      (Complex.I * (-2 / ((2 : ℂ) * ((t : ℂ) + (σ : ℂ) * Complex.I)) ^ 2)) t := hI0
  refine hI.congr_deriv ?_
  field_simp

theorem hasDerivAt_branchTermD1 {σ : ℝ} (hσ0 : 0 < σ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => -(Complex.I / (2 * ((s : ℂ) + (σ : ℂ) * Complex.I) ^ 2)))
      (Complex.I / ((t : ℂ) + (σ : ℂ) * Complex.I) ^ 3) t := by
  have hzne : ((t : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := shiftedLine_ne_zero hσ0 t
  have hsq : (2 : ℂ) * ((t : ℂ) + (σ : ℂ) * Complex.I) ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hzne)
  have hline := hasDerivAt_shiftedLine σ t
  have hpow : HasDerivAt (fun s : ℝ => (2 : ℂ) * ((s : ℂ) + (σ : ℂ) * Complex.I) ^ 2)
      (2 * (2 * ((t : ℂ) + (σ : ℂ) * Complex.I))) t := by
    have h := (hline.pow 2).const_mul (2 : ℂ)
    refine h.congr_deriv ?_
    push_cast
    ring
  have hinv := hpow.inv hsq
  have hI0 := hinv.const_mul (-Complex.I)
  have hI1 : HasDerivAt (fun s : ℝ => -Complex.I * ((2 : ℂ) * ((s : ℂ) + (σ : ℂ) * Complex.I) ^ 2)⁻¹)
      (-Complex.I * (-(2 * (2 * ((t : ℂ) + (σ : ℂ) * Complex.I)))
        / ((2 : ℂ) * ((t : ℂ) + (σ : ℂ) * Complex.I) ^ 2) ^ 2)) t := hI0
  have hfun : (fun s : ℝ => -Complex.I * ((2 : ℂ) * ((s : ℂ) + (σ : ℂ) * Complex.I) ^ 2)⁻¹)
      = fun s : ℝ => -(Complex.I / (2 * ((s : ℂ) + (σ : ℂ) * Complex.I) ^ 2)) := by
    funext s
    rw [div_eq_mul_inv, neg_mul]
  rw [hfun] at hI1
  refine hI1.congr_deriv ?_
  field_simp

theorem hasDerivAt_wallGeneratorScalar {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    HasDerivAt (wallGeneratorScalar σ) (wallScalarD1 σ t) t := by
  have h1 := (hasDerivAt_wallSymbol hσ0 hσ1 t).div_const 2
  have h2 := hasDerivAt_branchTerm hσ0 t
  have hsum0 := h1.add h2
  have hsum : HasDerivAt (wallGeneratorScalar σ)
      (wallSymbolJet σ 1 t / 2
        + -(Complex.I / (2 * ((t : ℂ) + (σ : ℂ) * Complex.I) ^ 2))) t := hsum0
  refine hsum.congr_deriv ?_
  rw [wallScalarD1]
  ring

theorem hasDerivAt_wallScalarD1 {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    HasDerivAt (wallScalarD1 σ) (wallScalarD2 σ t) t := by
  have h1 := (hasDerivAt_wallSymbolJet hσ0 hσ1 1 t).div_const 2
  have h2 := hasDerivAt_branchTermD1 hσ0 t
  have hsum0 := h1.add h2
  have hfun : (fun s : ℝ => wallSymbolJet σ 1 s / 2
      + -(Complex.I / (2 * ((s : ℂ) + (σ : ℂ) * Complex.I) ^ 2))) = wallScalarD1 σ := by
    funext s
    rw [wallScalarD1]
    ring
  have hsum : HasDerivAt (wallScalarD1 σ)
      (wallSymbolJet σ 2 t / 2 + Complex.I / ((t : ℂ) + (σ : ℂ) * Complex.I) ^ 3) t := by
    rw [← hfun]
    refine hsum0.congr_deriv ?_
    ring
  exact hsum

/-! ## The magnitude of the frequency jets -/

theorem norm_shiftedLine_ge {σ : ℝ} (t : ℝ) : |t| ≤ ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ := by
  have hre : ((t : ℂ) + (σ : ℂ) * Complex.I).re = t := by simp
  have := Complex.abs_re_le_norm ((t : ℂ) + (σ : ℂ) * Complex.I)
  rwa [hre] at this

theorem norm_wallScalarD1_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖wallScalarD1 σ t‖ ≤ (3 + Real.pi) * (1 + t)⁻¹ := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have habs : |t| = t := abs_of_pos ht0
  have hjet := norm_wallSymbolJet_succ_le hσ0 hσ1 (by rw [habs]; exact ht) 0
  have hz : t ≤ ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ := by
    have := norm_shiftedLine_ge (σ := σ) t
    rwa [habs] at this
  have hz0 : (0 : ℝ) < ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ := lt_of_lt_of_le ht0 hz
  have hbranch : ‖Complex.I / (2 * ((t : ℂ) + (σ : ℂ) * Complex.I) ^ 2)‖ ≤ 1 / (2 * t ^ 2) := by
    rw [norm_div, Complex.norm_I, norm_mul, norm_pow]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    have hden : 2 * t ^ 2 ≤ 2 * ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ ^ 2 := by nlinarith [hz, ht0]
    exact one_div_le_one_div_of_le (by positivity) hden
  have hfirst : ‖wallSymbolJet σ 1 t / 2‖ ≤ (2 * 1 * (1 + Real.pi / 2)) / t / 2 := by
    rw [norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    have hpow : |t| ^ (0 + 1) = t := by rw [habs]; ring
    have := hjet
    rw [hpow] at this
    simpa using this
  have hsum : ‖wallScalarD1 σ t‖
      ≤ (2 * 1 * (1 + Real.pi / 2)) / t / 2 + 1 / (2 * t ^ 2) := by
    rw [wallScalarD1]
    exact le_trans (norm_sub_le _ _) (add_le_add hfirst hbranch)
  refine hsum.trans ?_
  have hinv : (1 + t)⁻¹ ≥ 1 / (2 * t) := by
    rw [ge_iff_le, div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [ht]
  have ht2 : 1 / (2 * t ^ 2) ≤ 1 / (2 * t) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [ht, ht0]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hstep : (2 * 1 * (1 + Real.pi / 2)) / t / 2 + 1 / (2 * t ^ 2)
      ≤ (3 + Real.pi) * (1 / (2 * t)) := by
    have hA : (2 * 1 * (1 + Real.pi / 2)) / t / 2 = (2 + Real.pi) * (1 / (2 * t)) := by
      field_simp
    have hB : 1 / (2 * t ^ 2) ≤ 1 * (1 / (2 * t)) := by rw [one_mul]; exact ht2
    rw [hA]
    nlinarith [hB, hA]
  refine hstep.trans ?_
  have hnn : (0 : ℝ) ≤ 3 + Real.pi := by linarith
  exact mul_le_mul_of_nonneg_left hinv hnn

theorem norm_wallScalarD2_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖wallScalarD2 σ t‖ ≤ (4 * (3 + Real.pi)) * ((1 + t)⁻¹) ^ 2 := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have habs : |t| = t := abs_of_pos ht0
  have hjet := norm_wallSymbolJet_succ_le hσ0 hσ1 (by rw [habs]; exact ht) 1
  have hz : t ≤ ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ := by
    have := norm_shiftedLine_ge (σ := σ) t
    rwa [habs] at this
  have hz0 : (0 : ℝ) < ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ := lt_of_lt_of_le ht0 hz
  have hbranch : ‖Complex.I / ((t : ℂ) + (σ : ℂ) * Complex.I) ^ 3‖ ≤ 1 / t ^ 3 := by
    rw [norm_div, Complex.norm_I, norm_pow]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ ht0.le hz 3)
  have hfirst : ‖wallSymbolJet σ 2 t / 2‖ ≤ (2 * 2 * (1 + Real.pi / 2)) / t ^ 2 / 2 := by
    rw [norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    have hpow : |t| ^ (1 + 1) = t ^ 2 := by rw [habs]
    have hfact : ((1 + 1 : ℕ).factorial : ℝ) = 2 := by norm_num
    have := hjet
    rw [hpow, hfact] at this
    simpa using this
  have hsum : ‖wallScalarD2 σ t‖
      ≤ (2 * 2 * (1 + Real.pi / 2)) / t ^ 2 / 2 + 1 / t ^ 3 := by
    rw [wallScalarD2]
    exact le_trans (norm_add_le _ _) (add_le_add hfirst hbranch)
  refine hsum.trans ?_
  have hcube : 1 / t ^ 3 ≤ 1 / t ^ 2 := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [ht, ht0]
  have hstep : (2 * 2 * (1 + Real.pi / 2)) / t ^ 2 / 2 + 1 / t ^ 3
      ≤ (3 + Real.pi) * (1 / t ^ 2) := by
    have hA : (2 * 2 * (1 + Real.pi / 2)) / t ^ 2 / 2 = (2 + Real.pi) * (1 / t ^ 2) := by
      field_simp
    rw [hA]
    nlinarith [hcube]
  refine hstep.trans ?_
  have hinvsq : 1 / t ^ 2 ≤ 4 * ((1 + t)⁻¹) ^ 2 := by
    have h1t : (0 : ℝ) < (1 + t) ^ 2 := by positivity
    have ht2 : (0 : ℝ) < t ^ 2 := by positivity
    rw [inv_pow, ← one_div, mul_one_div, div_le_div_iff₀ ht2 h1t]
    nlinarith [ht, ht0]
  calc (3 + Real.pi) * (1 / t ^ 2)
      ≤ (3 + Real.pi) * (4 * ((1 + t)⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left hinvsq (by positivity [Real.pi_pos])
    _ = (4 * (3 + Real.pi)) * ((1 + t)⁻¹) ^ 2 := by ring

/-! ## The operator form -/

section Operator

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- **The shifted generator is differentiable in the frequency, with scalar derivative.** -/
theorem hasDerivAt_wallGeneratorShift (T : X →L[ℂ] X) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (L t : ℝ) :
    HasDerivAt (wallGeneratorShift T σ L)
      (wallScalarD1 σ t • ContinuousLinearMap.id ℂ X) t := by
  have hbase := (hasDerivAt_wallGeneratorScalar hσ0 hσ1 t).smul_const
    (ContinuousLinearMap.id ℂ X)
  have h1 := hbase.sub_const ((1 / 2 : ℂ) • T)
  have h2 := h1.add_const ((L : ℂ) • ContinuousLinearMap.id ℂ X)
  exact h2

/-- **The second frequency derivative.** -/
theorem hasDerivAt_wallGeneratorShiftD1 {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    HasDerivAt (fun s : ℝ => wallScalarD1 σ s • (ContinuousLinearMap.id ℂ X))
      (wallScalarD2 σ t • ContinuousLinearMap.id ℂ X) t :=
  (hasDerivAt_wallScalarD1 hσ0 hσ1 t).smul_const _

omit [CompleteSpace X] in
theorem norm_smul_id_le (c : ℂ) : ‖c • (ContinuousLinearMap.id ℂ X)‖ ≤ ‖c‖ := by
  refine (norm_smul_le c (ContinuousLinearMap.id ℂ X)).trans ?_
  exact mul_le_of_le_one_right (norm_nonneg c) (ContinuousLinearMap.norm_id_le)

omit [CompleteSpace X] in
/-- **`(4)` for the generator: the first frequency derivative is `O((1+t)^{-1})`.** -/
theorem norm_wallGeneratorShiftD1_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖wallScalarD1 σ t • (ContinuousLinearMap.id ℂ X)‖ ≤ (3 + Real.pi) * (1 + t)⁻¹ :=
  (norm_smul_id_le _).trans (norm_wallScalarD1_le hσ0 hσ1 ht)

omit [CompleteSpace X] in
/-- **`(4)` for the generator: the second frequency derivative is `O((1+t)^{-2})`.** -/
theorem norm_wallGeneratorShiftD2_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖wallScalarD2 σ t • (ContinuousLinearMap.id ℂ X)‖
      ≤ (4 * (3 + Real.pi)) * ((1 + t)⁻¹) ^ 2 :=
  (norm_smul_id_le _).trans (norm_wallScalarD2_le hσ0 hσ1 ht)

end Operator

end GaloisForLFunctions.RHTower
