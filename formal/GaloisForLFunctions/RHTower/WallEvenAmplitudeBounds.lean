import GaloisForLFunctions.RHTower.WallTailIntegrationByParts

/-!
# The amplitude bounds in the modulus of the frequency

Every decay estimate for the generator's frequency jets rests on the symbol bound
`‖r^{(m+1)}(t)‖ ≤ 2(m+1)!(1+π/2)/|t|^{m+1}`, which is already stated in `|t|`.  The estimates
recorded here carry that modulus through to the amplitudes, so they hold on both frequency rays:

`‖(C⁻¹C')(t)‖ = O((1+|t|)^{-1})`,  `‖[C⁻¹(C⁻¹)']'(t)‖ = O((1+|t|)^{-2})`.

Nothing is reflected but the estimate.  The generator itself has no symmetry in the frequency — its
two digamma abscissas `1−σ` and `1+σ` are genuinely different — so only the bounds are even, and
they are even because the symbol bound is.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- **The first frequency derivative of the scalar symbol is `O((1+|t|)^{-1})`.** -/
theorem norm_wallScalarD1_le' {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖wallScalarD1 σ t‖ ≤ (3 + Real.pi) * (1 + |t|)⁻¹ := by
  have ht0 : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
  have hjet := norm_wallSymbolJet_succ_le hσ0 hσ1 ht 0
  have hz : |t| ≤ ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ := norm_shiftedLine_ge (σ := σ) t
  have hz0 : (0 : ℝ) < ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ := lt_of_lt_of_le ht0 hz
  have hbranch : ‖Complex.I / (2 * ((t : ℂ) + (σ : ℂ) * Complex.I) ^ 2)‖ ≤ 1 / (2 * |t| ^ 2) := by
    rw [norm_div, Complex.norm_I, norm_mul, norm_pow]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    have hden : 2 * |t| ^ 2 ≤ 2 * ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ ^ 2 := by nlinarith [hz, ht0]
    exact one_div_le_one_div_of_le (by positivity) hden
  have hfirst : ‖wallSymbolJet σ 1 t / 2‖ ≤ (2 * 1 * (1 + Real.pi / 2)) / |t| / 2 := by
    rw [norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    have hpow : |t| ^ (0 + 1) = |t| := by ring
    have hj := hjet
    rw [hpow] at hj
    simpa using hj
  have hsum : ‖wallScalarD1 σ t‖
      ≤ (2 * 1 * (1 + Real.pi / 2)) / |t| / 2 + 1 / (2 * |t| ^ 2) := by
    rw [wallScalarD1]
    exact le_trans (norm_sub_le _ _) (add_le_add hfirst hbranch)
  refine hsum.trans ?_
  have hinv : (1 + |t|)⁻¹ ≥ 1 / (2 * |t|) := by
    rw [ge_iff_le, div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [ht]
  have ht2 : 1 / (2 * |t| ^ 2) ≤ 1 / (2 * |t|) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [ht, ht0]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hstep : (2 * 1 * (1 + Real.pi / 2)) / |t| / 2 + 1 / (2 * |t| ^ 2)
      ≤ (3 + Real.pi) * (1 / (2 * |t|)) := by
    have hA : (2 * 1 * (1 + Real.pi / 2)) / |t| / 2 = (2 + Real.pi) * (1 / (2 * |t|)) := by
      field_simp
    have hB : 1 / (2 * |t| ^ 2) ≤ 1 * (1 / (2 * |t|)) := by rw [one_mul]; exact ht2
    rw [hA]
    nlinarith [hB, hA]
  refine hstep.trans ?_
  have hnn : (0 : ℝ) ≤ 3 + Real.pi := by linarith
  exact mul_le_mul_of_nonneg_left hinv hnn

/-- **The second frequency derivative of the scalar symbol is `O((1+|t|)^{-2})`.** -/
theorem norm_wallScalarD2_le' {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖wallScalarD2 σ t‖ ≤ (4 * (3 + Real.pi)) * ((1 + |t|)⁻¹) ^ 2 := by
  have ht0 : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
  have hjet := norm_wallSymbolJet_succ_le hσ0 hσ1 ht 1
  have hz : |t| ≤ ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ := norm_shiftedLine_ge (σ := σ) t
  have hz0 : (0 : ℝ) < ‖(t : ℂ) + (σ : ℂ) * Complex.I‖ := lt_of_lt_of_le ht0 hz
  have hbranch : ‖Complex.I / ((t : ℂ) + (σ : ℂ) * Complex.I) ^ 3‖ ≤ 1 / |t| ^ 3 := by
    rw [norm_div, Complex.norm_I, norm_pow]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ ht0.le hz 3)
  have hfirst : ‖wallSymbolJet σ 2 t / 2‖ ≤ (2 * 2 * (1 + Real.pi / 2)) / |t| ^ 2 / 2 := by
    rw [norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    have hpow : |t| ^ (1 + 1) = |t| ^ 2 := by ring
    have hfact : ((1 + 1 : ℕ).factorial : ℝ) = 2 := by norm_num
    have hj := hjet
    rw [hpow, hfact] at hj
    simpa using hj
  have hsum : ‖wallScalarD2 σ t‖
      ≤ (2 * 2 * (1 + Real.pi / 2)) / |t| ^ 2 / 2 + 1 / |t| ^ 3 := by
    rw [wallScalarD2]
    exact le_trans (norm_add_le _ _) (add_le_add hfirst hbranch)
  refine hsum.trans ?_
  have hcube : 1 / |t| ^ 3 ≤ 1 / |t| ^ 2 := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [ht, ht0]
  have hstep : (2 * 2 * (1 + Real.pi / 2)) / |t| ^ 2 / 2 + 1 / |t| ^ 3
      ≤ (3 + Real.pi) * (1 / |t| ^ 2) := by
    have hA : (2 * 2 * (1 + Real.pi / 2)) / |t| ^ 2 / 2 = (2 + Real.pi) * (1 / |t| ^ 2) := by
      field_simp
    rw [hA]
    nlinarith [hcube]
  refine hstep.trans ?_
  have hinvsq : 1 / |t| ^ 2 ≤ 4 * ((1 + |t|)⁻¹) ^ 2 := by
    have h1t : (0 : ℝ) < (1 + |t|) ^ 2 := by positivity
    have ht2 : (0 : ℝ) < |t| ^ 2 := by positivity
    rw [inv_pow, ← one_div, mul_one_div, div_le_div_iff₀ ht2 h1t]
    nlinarith [ht, ht0]
  calc (3 + Real.pi) * (1 / |t| ^ 2)
      ≤ (3 + Real.pi) * (4 * ((1 + |t|)⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left hinvsq (by positivity [Real.pi_pos])
    _ = (4 * (3 + Real.pi)) * ((1 + |t|)⁻¹) ^ 2 := by ring

section Operator

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- The operator form of the first derivative bound. -/
theorem norm_wallGeneratorShiftD1_le' {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ}
    (ht : 1 ≤ |t|) :
    ‖wallScalarD1 σ t • (ContinuousLinearMap.id ℂ X)‖ ≤ (3 + Real.pi) * (1 + |t|)⁻¹ :=
  (norm_smul_id_le _).trans (norm_wallScalarD1_le' hσ0 hσ1 ht)

omit [CompleteSpace X] in
/-- The operator form of the second derivative bound. -/
theorem norm_wallGeneratorShiftD2_le' {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ}
    (ht : 1 ≤ |t|) :
    ‖wallScalarD2 σ t • (ContinuousLinearMap.id ℂ X)‖
      ≤ (4 * (3 + Real.pi)) * ((1 + |t|)⁻¹) ^ 2 :=
  (norm_smul_id_le _).trans (norm_wallScalarD2_le' hσ0 hσ1 ht)

/-- **The second boundary amplitude decays linearly in `|t|`.** -/
theorem norm_invFamilyProduct_wallGeneratorShift_le' {T : X →L[ℂ] X} {σ L μ₀ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀) {t : ℝ} (ht : 1 ≤ |t|)
    (hfloor : μ₀ ≤ wallFloor T σ t + L) :
    ‖invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) t‖
      ≤ ((μ₀⁻¹) ^ 3 * (3 + Real.pi)) * (1 + |t|)⁻¹ :=
  norm_invFamilyProduct_le_of_symbolDecay_weight
    (norm_invFamily_wallGeneratorShift_le' hσ0 hσ1 hμ hfloor)
    (norm_wallGeneratorShiftD1_le' hσ0 hσ1 ht)

/-- **The surviving amplitude decays quadratically in `|t|`.** -/
theorem norm_invFamilyProductDeriv_wallGeneratorShift_le' {T : X →L[ℂ] X} {σ L μ₀ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀) {t : ℝ} (ht : 1 ≤ |t|)
    (hfloor : μ₀ ≤ wallFloor T σ t + L) :
    ‖invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
        (wallGeneratorD2 X σ) t‖
      ≤ wallAmplitudeConst μ₀ * ((1 + |t|)⁻¹) ^ 2 :=
  norm_invFamilyProductDeriv_le_of_symbolDecay_weight (by positivity)
    (norm_invFamily_wallGeneratorShift_le' hσ0 hσ1 hμ hfloor)
    (norm_wallGeneratorShiftD1_le' hσ0 hσ1 ht)
    (norm_wallGeneratorShiftD2_le' hσ0 hσ1 ht)

end Operator

end GaloisForLFunctions.RHTower
