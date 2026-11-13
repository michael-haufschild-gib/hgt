/-
Cube averages and normalized Gauss sums adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.CubeCorrespondences

/-!
# Cube averages and normalized Gauss sums

Averages of cube branches separate the height weight from the cubic multiplier; the
intermediate valuation strata cancel. The normalized cubic Gauss sum
`normalizedCubicUnitGauss` has norm one on primes, coprime products and squarefree moduli.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix

/-- The intermediate valuation strata cancel; only the unit and zero strata remain. -/
theorem actualCubeCuspPhaseSum_coprime (A : rationalExtension) (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (hA : lambda ^ 2 ∣ (A : SL(2, O)) 0 0 - 1)
    (hC : IsCoprime ((A : SL(2, O)) 1 0) p) (w : Fin 4 → ℂ) :
    actualCubeCuspPhaseSum A p hp hprimary w =
      w 0 * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 2 * ((Ideal.absNorm (Ideal.span {p}) : ℂ) - 1) + w 3 := by
  let e := cubeResidueStrataEquiv p hp
  let a := cubeCuspAffineEquiv p ((A : SL(2, O)) 0 0) ((A : SL(2, O)) 1 0) hprimary hC
  let d (r : CubeResidues p) := actualCubeCuspData (A : SL(2, O)) p (cubeResidueRepresentative p r) hp hprimary
  let phi (s : CubeResidueStrata p) := w s.1 * cubeStratumSymbol p ((A : SL(2, O)) 1 0) s.1 s.2
  have hpoint (r : CubeResidues p) :
      w (d r).exponent * complexCharacter ⟨(d r).matrix * (A : SL(2, O))⁻¹, (d r).congruent⟩ = phi (e.symm (a r)) := by
    rw [(d r).comparison_phase A hp hprimary hA hC]
    change phi ((d r).stratum hp.ne_zero) = phi (e.symm (a r))
    apply congrArg phi
    apply e.injective
    rw [e.apply_symm_apply]
    change cubeResidueStratumMap p ((d r).stratum hp.ne_zero) = a r
    rw [(d r).stratum_map hp.ne_zero]
    rw [← cubeCuspAffineEquiv_mk p ((A : SL(2, O)) 0 0) ((A : SL(2, O)) 1 0)
      (cubeResidueRepresentative p r) hprimary hC, cubeResidueRepresentative_spec]
  letI : ∀ j : Fin 4, Finite (O ⧸ Ideal.span {p ^ (3 - j.val)}) := fun j =>
    (Ideal.span {p ^ (3 - j.val)}).finiteQuotientOfFreeOfNeBot
      (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ hp.ne_zero))
  have hphi : Summable phi := Summable.of_finite
  calc
    actualCubeCuspPhaseSum A p hp hprimary w = ∑' r, phi (e.symm (a r)) := tsum_congr hpoint
    _ = ∑' r, phi (e.symm r) := a.tsum_eq (fun r => phi (e.symm r))
    _ = ∑' s, phi s := e.symm.tsum_eq phi
    _ = ∑ j : Fin 4, w j * ∑' b : CubicUnitResidue (p ^ (3 - j.val)), cubeStratumSymbol p ((A : SL(2, O)) 1 0) j b := by
      rw [hphi.tsum_sigma, tsum_fintype]
      apply Finset.sum_congr rfl
      intro j _
      exact tsum_mul_left
        (f := fun b : CubicUnitResidue (p ^ (3 - j.val)) => cubeStratumSymbol p ((A : SL(2, O)) 1 0) j b)
        (a := w j)
    _ = _ := cubeStrata_weighted_sum p ((A : SL(2, O)) 1 0) hp hprimary hC w

lemma cube_exponent_zero_of_lower_divisible (A N : SL(2, O)) (p q : O) (j : ℕ)
    (hp : Prime p) (hC : p ∣ A 1 0) (hx : A 0 0 + 3 * q * A 1 0 = p ^ j * N 0 0) : j = 0 := by
  by_contra hj
  have hpx : p ∣ A 0 0 + 3 * q * A 1 0 := by
    rw [hx]
    exact dvd_mul_of_dvd_left (dvd_pow_self p hj) (N 0 0)
  have hpa : p ∣ A 0 0 := by
    simpa only [add_sub_cancel_right] using dvd_sub hpx (dvd_mul_of_dvd_right hC (3 * q))
  have hone : p ∣ (1 : O) := by
    have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by simpa only [Matrix.det_fin_two] using A.property
    rw [← hd]
    exact dvd_sub (dvd_mul_of_dvd_left hpa _) (dvd_mul_of_dvd_right hC _)
  exact hp.2.1 (isUnit_of_dvd_one hone)

lemma rationalCusp_cube_zero_phase (A N : rationalExtension) (p q : O)
    (hp : lambda ^ 2 ∣ p - 1)
    (hA : lambda ^ 2 ∣ (A : SL(2, O)) 0 0 - 1) (hN : lambda ^ 2 ∣ (N : SL(2, O)) 0 0 - 1)
    (hx : (A : SL(2, O)) 0 0 + 3 * q * (A : SL(2, O)) 1 0 = (N : SL(2, O)) 0 0)
    (hc : (N : SL(2, O)) 1 0 = p ^ 3 * (A : SL(2, O)) 1 0)
    (hNA : (N : SL(2, O)) * (A : SL(2, O))⁻¹ ∈ levelThree) :
    complexCharacter ⟨(N : SL(2, O)) * (A : SL(2, O))⁻¹, hNA⟩ = 1 := by
  have hcop : IsCoprime ((N : SL(2, O)) 0 0) p := by
    refine ⟨(N : SL(2, O)) 1 1, -(N : SL(2, O)) 0 1 * p ^ 2 * (A : SL(2, O)) 1 0, ?_⟩
    have hd : (N : SL(2, O)) 0 0 * (N : SL(2, O)) 1 1 - (N : SL(2, O)) 0 1 * (N : SL(2, O)) 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using (N : SL(2, O)).property
    rw [hc] at hd
    linear_combination hd
  have hcube : ringComplex (symbol ((N : SL(2, O)) 0 0) p) ^ 3 = 1 := by
    rw [← map_pow, symbol_cube_of_isCoprime _ _ hp hcop, map_one]
  have hb := rationalCusp_cube_phase_balance A N p q 0 hp hA hN (by simpa only [pow_zero, one_mul] using hx)
    (by simpa only [Nat.sub_zero] using hc)
  simp only [pow_zero, mul_one, Nat.sub_zero, hcube] at hb
  have hbase : extendedComplexCharacter A ≠ 0 := by
    intro he
    have hh := extendedComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  apply mul_right_cancel₀ hbase
  rw [one_mul, rationalCusp_comparison_character A N hNA, hb]

theorem actualCubeCuspPhaseSum_dvd (A : rationalExtension) (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (hA : lambda ^ 2 ∣ (A : SL(2, O)) 0 0 - 1)
    (hC : p ∣ (A : SL(2, O)) 1 0) (w : Fin 4 → ℂ) :
    actualCubeCuspPhaseSum A p hp hprimary w = w 0 * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 := by
  let d (r : CubeResidues p) := actualCubeCuspData (A : SL(2, O)) p (cubeResidueRepresentative p r) hp hprimary
  have hpoint (r : CubeResidues p) :
      w (d r).exponent * complexCharacter ⟨(d r).matrix * (A : SL(2, O))⁻¹, (d r).congruent⟩ = w 0 := by
    have hj : ((d r).exponent : ℕ) = 0 := cube_exponent_zero_of_lower_divisible
      (A : SL(2, O)) (d r).matrix p _ _ hp hC (d r).first
    have hj' : (d r).exponent = 0 := Fin.ext hj
    let N : rationalExtension := ⟨(d r).matrix, (d r).rational_mem⟩
    have hphase := rationalCusp_cube_zero_phase A N p (cubeResidueRepresentative p r) hprimary hA
      (integralMatrix_comparison_primary _ _ (d r).congruent hA)
      (by simpa only [hj, pow_zero, one_mul] using (d r).first)
      (by simpa only [hj, Nat.sub_zero] using (d r).lower_eq hp.ne_zero) (d r).congruent
    change w (d r).exponent * complexCharacter ⟨(N : SL(2, O)) * (A : SL(2, O))⁻¹, (d r).congruent⟩ = w 0
    rw [hphase, hj', mul_one]
  calc
    actualCubeCuspPhaseSum A p hp hprimary w = ∑' r : CubeResidues p, w 0 := tsum_congr hpoint
    _ = (Nat.card (CubeResidues p) : ℂ) * w 0 := by rw [tsum_const, nsmul_eq_mul]
    _ = _ := by
      change (Ideal.absNorm (Ideal.span {p ^ 3}) : ℂ) * w 0 = _
      rw [← Ideal.span_singleton_pow, map_pow, Nat.cast_pow]
      ring

lemma complexUpper_lowerRight_ne_zero (T : SL(2, ℂ)) (hT : T 1 0 = 0) : T 1 1 ≠ 0 := by
  intro hd
  have hdet := T.property
  simp only [Matrix.det_fin_two, hT, hd, mul_zero, sub_zero] at hdet
  exact zero_ne_one hdet

/-- Upper triangular hyperbolic isometries act affinely on each horizontal plane. -/
lemma complexUpper_action (T : SL(2, ℂ)) (hT : T 1 0 = 0) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    T • upperPoint z v hv = upperPoint ((T 0 0 * z + T 0 1) / T 1 1)
      (v / ‖T 1 1‖ ^ 2) (div_pos hv (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (complexUpper_lowerRight_ne_zero T hT)))) := by
  have hdet : T 0 0 * T 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hT, mul_zero, sub_zero] using T.property
  have ha : T 0 0 ≠ 0 := by intro h; rw [h, zero_mul] at hdet; exact zero_ne_one hdet
  have hd : T 1 1 = (T 0 0)⁻¹ := by
    apply mul_left_cancel₀ ha
    rw [hdet, mul_inv_cancel₀ ha]
  have hfactor : T = complexTranslation (T 0 1 / T 1 1) * complexDiagonal (T 0 0) ha := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, complexTranslation, complexDiagonal, hT, hd, ha]
  conv_lhs => rw [hfactor, mul_smul, complexDiagonal_action, complexTranslation_action]
  apply upperPoint_congr
  · rw [hd]
    field_simp
  · rw [hd, norm_inv, inv_pow, div_inv_eq_mul, Complex.normSq_eq_norm_sq]
    ring

lemma cubeAverageMatrix_entries (p : O) (hp : p ≠ 0) (q : O) :
    (cubeAverageMatrix p hp q : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(cubeDilationRoot p)⁻¹, (cubeDilationRoot p)⁻¹ * (3 * ringComplex q); 0, cubeDilationRoot p] := by
  have hentry (M : SL(2, O)) (i j : Fin 2) : integralComplexMatrix M i j = ringComplex (M i j) := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubeAverageMatrix, cubeDilationMatrix, complexDiagonal,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, hentry, integralTranslation, map_mul, map_ofNat]

def cubeCuspTriangular {A : SL(2, O)} {p q : O} (d : CubeCuspData A p q) (hp : p ≠ 0) : SL(2, ℂ) :=
  (integralComplexMatrix d.matrix)⁻¹ * cubeAverageMatrix p hp q * integralComplexMatrix A

lemma cubeCuspTriangular_factor {A : SL(2, O)} {p q : O} (d : CubeCuspData A p q) (hp : p ≠ 0) :
    cubeAverageMatrix p hp q * integralComplexMatrix A = integralComplexMatrix d.matrix * cubeCuspTriangular d hp := by
  unfold cubeCuspTriangular
  group

lemma cubeCuspTriangular_entries {A : SL(2, O)} {p q : O} (d : CubeCuspData A p q) (hp : p ≠ 0) :
    cubeCuspTriangular d hp 0 0 = (cubeDilationRoot p)⁻¹ * ringComplex p ^ d.exponent.val ∧
    cubeCuspTriangular d hp 1 0 = 0 ∧
    cubeCuspTriangular d hp 1 1 = (cubeDilationRoot p)⁻¹ * ringComplex p ^ (3 - d.exponent.val) := by
  let B := cubeAverageMatrix p hp q * integralComplexMatrix A
  have hz := cubeDilationRoot_ne_zero p hp
  have he : cubeDilationRoot p ^ 2 = ringComplex p ^ 3 := by rw [cubeDilationRoot_sq, map_pow]
  have hentry (M : SL(2, O)) (i j : Fin 2) : integralComplexMatrix M i j = ringComplex (M i j) := rfl
  have hx : ringComplex (A 0 0) + 3 * ringComplex q * ringComplex (A 1 0) =
      ringComplex p ^ d.exponent.val * ringComplex (d.matrix 0 0) := by
    simpa only [map_add, map_mul, map_pow, map_ofNat] using congrArg ringComplex d.first
  have hy : ringComplex p ^ 3 * ringComplex (A 1 0) =
      ringComplex p ^ d.exponent.val * ringComplex (d.matrix 1 0) := by
    simpa only [map_mul, map_pow] using congrArg ringComplex d.second
  have hB0 : B 0 0 = (cubeDilationRoot p)⁻¹ * ringComplex p ^ d.exponent.val * ringComplex (d.matrix 0 0) := by
    change (∑ k : Fin 2, cubeAverageMatrix p hp q 0 k * integralComplexMatrix A k 0) = _
    simp only [cubeAverageMatrix_entries, hentry, Matrix.of_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination (cubeDilationRoot p)⁻¹ * hx
  have hB1 : B 1 0 = (cubeDilationRoot p)⁻¹ * ringComplex p ^ d.exponent.val * ringComplex (d.matrix 1 0) := by
    change (∑ k : Fin 2, cubeAverageMatrix p hp q 1 k * integralComplexMatrix A k 0) = _
    simp only [cubeAverageMatrix_entries, hentry, Matrix.of_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, zero_add]
    rw [mul_assoc, ← hy, ← he]
    field_simp
  have hT : cubeCuspTriangular d hp = (integralComplexMatrix d.matrix)⁻¹ * B := by
    dsimp only [cubeCuspTriangular, B]
    group
  have hdet : ringComplex (d.matrix 0 0) * ringComplex (d.matrix 1 1) -
      ringComplex (d.matrix 0 1) * ringComplex (d.matrix 1 0) = 1 := by
    have hd : d.matrix 0 0 * d.matrix 1 1 - d.matrix 0 1 * d.matrix 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using d.matrix.property
    simpa only [map_sub, map_mul, map_one] using congrArg ringComplex hd
  have h00 : cubeCuspTriangular d hp 0 0 = (cubeDilationRoot p)⁻¹ * ringComplex p ^ d.exponent.val := by
    rw [hT]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, hentry, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hB0, hB1]
    linear_combination (cubeDilationRoot p)⁻¹ * ringComplex p ^ d.exponent.val * hdet
  have h10 : cubeCuspTriangular d hp 1 0 = 0 := by
    rw [hT]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, hentry, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hB0, hB1]
    ring
  refine ⟨h00, h10, ?_⟩
  have hd : cubeCuspTriangular d hp 0 0 * cubeCuspTriangular d hp 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, h10, mul_zero, sub_zero] using (cubeCuspTriangular d hp).property
  rw [h00] at hd
  apply mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hz) (pow_ne_zero _ (ringComplex_ne_zero hp)))
  rw [hd]
  have hpow : ringComplex p ^ d.exponent.val * ringComplex p ^ (3 - d.exponent.val) = ringComplex p ^ 3 := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : d.exponent.val ≤ 3)]
  calc
    1 = (cubeDilationRoot p)⁻¹ ^ 2 * ringComplex p ^ 3 := by rw [← he, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hz)]
    _ = _ := by rw [← hpow]; ring

lemma cubeCuspTriangular_integral_scale {A : SL(2, O)} {p q : O} (d : CubeCuspData A p q) (hp : p ≠ 0) :
    (cubeCuspTriangular d hp 0 0 / cubeCuspTriangular d hp 1 1) * ringComplex (p ^ 3) =
      ringComplex (p ^ (2 * d.exponent.val)) := by
  obtain ⟨h00, _, h11⟩ := cubeCuspTriangular_entries d hp
  rw [h00, h11, map_pow, map_pow]
  have hz := cubeDilationRoot_ne_zero p hp
  have he := ringComplex_ne_zero hp
  have hpow : ringComplex p ^ 3 = ringComplex p ^ d.exponent.val * ringComplex p ^ (3 - d.exponent.val) := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : d.exponent.val ≤ 3)]
  rw [hpow, show ringComplex p ^ (2 * d.exponent.val) = (ringComplex p ^ d.exponent.val) ^ 2 by
    rw [mul_comm 2 d.exponent.val, pow_mul]]
  field_simp

lemma cubeDilationRoot_norm_sq (p : O) : ‖cubeDilationRoot p‖ ^ 2 = ‖ringComplex p‖ ^ 3 := by
  rw [← norm_pow, cubeDilationRoot_sq, map_pow, norm_pow]

def cubeCuspHeightDenominator (p : O) (j : Fin 4) : ℝ :=
  (‖cubeDilationRoot p‖ ^ 2)⁻¹ * (‖ringComplex p‖ ^ (3 - j.val)) ^ 2

def cubeCuspHeightWeight (p : O) (j : Fin 4) : ℂ :=
  (cubeCuspHeightDenominator p j ^ (-2 / 3 : ℝ) : ℝ)

lemma cubeCuspHeightDenominator_pos (p : O) (hp : p ≠ 0) (j : Fin 4) : 0 < cubeCuspHeightDenominator p j := by
  have hz : 0 < ‖cubeDilationRoot p‖ := norm_pos_iff.mpr (cubeDilationRoot_ne_zero p hp)
  have hr : 0 < ‖ringComplex p‖ := norm_pos_iff.mpr (ringComplex_ne_zero hp)
  unfold cubeCuspHeightDenominator
  positivity

lemma cubeCuspTriangular_norm_sq {A : SL(2, O)} {p q : O} (d : CubeCuspData A p q) (hp : p ≠ 0) :
    ‖cubeCuspTriangular d hp 1 1‖ ^ 2 = cubeCuspHeightDenominator p d.exponent := by
  rw [(cubeCuspTriangular_entries d hp).2.2, norm_mul, norm_inv, norm_pow, mul_pow, inv_pow]
  rfl

lemma cubeCuspTriangular_height {A : SL(2, O)} {p q : O} (d : CubeCuspData A p q) (hp : p ≠ 0)
    (v : ℝ) (hv : 0 < v) :
    ((v / ‖cubeCuspTriangular d hp 1 1‖ ^ 2 : ℝ) : ℂ) ^ (2 / 3 : ℂ) =
      (v : ℂ) ^ (2 / 3 : ℂ) * cubeCuspHeightWeight p d.exponent := by
  have hD := cubeCuspHeightDenominator_pos p hp d.exponent
  rw [cubeCuspTriangular_norm_sq]
  have hc : ((2 / 3 : ℝ) : ℂ) = (2 / 3 : ℂ) := by norm_num
  rw [← hc, ← Complex.ofReal_cpow (div_pos hv hD).le, ← Complex.ofReal_cpow hv.le,
    cubeCuspHeightWeight, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [Real.div_rpow hv.le hD.le, div_eq_mul_inv, ← Real.rpow_neg hD.le]
  congr 2 <;> ring

lemma cubeCuspHeightDenominator_zero (p : O) (hp : p ≠ 0) :
    cubeCuspHeightDenominator p 0 = ‖ringComplex p‖ ^ 3 := by
  unfold cubeCuspHeightDenominator
  rw [cubeDilationRoot_norm_sq]
  norm_num only [Fin.val_zero, Nat.sub_zero]
  have hr := norm_ne_zero_iff.mpr (ringComplex_ne_zero hp)
  field_simp <;> ring

lemma cubeCuspHeightDenominator_three (p : O) :
    cubeCuspHeightDenominator p 3 = (‖ringComplex p‖ ^ 3)⁻¹ := by
  unfold cubeCuspHeightDenominator
  rw [cubeDilationRoot_norm_sq]
  norm_num

lemma cubeCuspHeightWeight_zero (p : O) (hp : p ≠ 0) :
    cubeCuspHeightWeight p 0 = (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ := by
  have hr : 0 < ‖ringComplex p‖ := norm_pos_iff.mpr (ringComplex_ne_zero hp)
  have he : (‖ringComplex p‖ ^ 3) ^ (-2 / 3 : ℝ) = (‖ringComplex p‖ ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast_mul hr.le 3, Nat.cast_ofNat]
    rw [show (3 : ℝ) * (-2 / 3) = -(2 : ℝ) by ring, Real.rpow_neg hr.le, Real.rpow_ofNat]
  rw [cubeCuspHeightWeight, cubeCuspHeightDenominator_zero p hp, he,
    ringComplex_norm_sq_eq_absNorm_span, Complex.ofReal_inv, Complex.ofReal_natCast]

lemma cubeCuspHeightWeight_three (p : O) (hp : p ≠ 0) :
    cubeCuspHeightWeight p 3 = (Ideal.absNorm (Ideal.span {p}) : ℂ) := by
  have hr : 0 < ‖ringComplex p‖ := norm_pos_iff.mpr (ringComplex_ne_zero hp)
  have he : ((‖ringComplex p‖ ^ 3)⁻¹) ^ (-2 / 3 : ℝ) = ‖ringComplex p‖ ^ 2 := by
    rw [Real.inv_rpow (pow_nonneg hr.le 3), ← Real.rpow_natCast_mul hr.le 3, Nat.cast_ofNat,
      show (3 : ℝ) * (-2 / 3) = -(2 : ℝ) by ring, Real.rpow_neg hr.le, Real.rpow_ofNat, inv_inv]
  rw [cubeCuspHeightWeight, cubeCuspHeightDenominator_three, he,
    ringComplex_norm_sq_eq_absNorm_span, Complex.ofReal_natCast]

lemma rationalSourceCuspConstant_congruent (A N : rationalExtension)
    (hNA : (N : SL(2, O)) * (A : SL(2, O))⁻¹ ∈ levelThree) :
    rationalSourceCuspConstant N = complexCharacter ⟨(N : SL(2, O)) * (A : SL(2, O))⁻¹, hNA⟩ * rationalSourceCuspConstant A := by
  unfold rationalSourceCuspConstant
  rw [← rationalCusp_comparison_character A N hNA]
  ring

/-- The average of one cube branch separates its exact height weight from its cubic multiplier. -/
theorem rationalSourceCubeBranch_average (A : rationalExtension) {p q : O}
    (d : CubeCuspData (A : SL(2, O)) p q) (hp : p ≠ 0) (v : ℝ) (hv : 0 < v) :
    (∫ z in periodDomain, cubicSourceResidualFunction
      (cubeAverageMatrix p hp q • (integralComplexMatrix (A : SL(2, O)) • upperPoint (ringComplex (p ^ 3) * z) v hv))) =
      rationalSourceCuspConstant A * (v : ℂ) ^ (2 / 3 : ℂ) *
        (cubeCuspHeightWeight p d.exponent * complexCharacter ⟨d.matrix * (A : SL(2, O))⁻¹, d.congruent⟩) := by
  let N : rationalExtension := ⟨d.matrix, d.rational_mem⟩
  let T := cubeCuspTriangular d hp
  have hT : T 1 0 = 0 := (cubeCuspTriangular_entries d hp).2.1
  have hcoord (z : ℂ) : (T 0 0 * (ringComplex (p ^ 3) * z) + T 0 1) / T 1 1 =
      ringComplex (p ^ (2 * d.exponent.val)) * z + T 0 1 / T 1 1 := by
    calc
      _ = ((T 0 0 / T 1 1) * ringComplex (p ^ 3)) * z + T 0 1 / T 1 1 := by ring
      _ = _ := by rw [cubeCuspTriangular_integral_scale d hp]
  have hact (z : ℂ) :
      cubeAverageMatrix p hp q • (integralComplexMatrix (A : SL(2, O)) •
        upperPoint (ringComplex (p ^ 3) * z) v hv) =
      integralComplexMatrix (N : SL(2, O)) • upperPoint
        (ringComplex (p ^ (2 * d.exponent.val)) * z + T 0 1 / T 1 1)
        (v / ‖T 1 1‖ ^ 2)
        (div_pos hv (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (complexUpper_lowerRight_ne_zero T hT)))) := by
    rw [← mul_smul, cubeCuspTriangular_factor d hp, mul_smul]
    change integralComplexMatrix (N : SL(2, O)) • (T • upperPoint (ringComplex (p ^ 3) * z) v hv) = _
    rw [complexUpper_action T hT, hcoord]
  simp_rw [hact]
  rw [rationalSourceCusp_average_enlarged_affine N (p ^ (2 * d.exponent.val))
    (pow_ne_zero _ hp) (T 0 1 / T 1 1) _ _,
    rationalSourceCuspConstant_congruent A N d.congruent, cubeCuspTriangular_height d hp v hv]
  ring

/-- Normalized average of the actual translated inverse cube dilations. -/
def cubeAverage (p : O) (hp : p ≠ 0) (F : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ ^ 3 *
    ∑' r : CubeResidues p, F (cubeAverageMatrix p hp (cubeResidueRepresentative p r) • w)

lemma cubeAverage_continuous (p : O) (hp : p ≠ 0) (F : HyperbolicSpace → ℂ) (hF : Continuous F) :
    Continuous (cubeAverage p hp F) := by
  letI : Finite (CubeResidues p) := (Ideal.span {p ^ 3}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero 3 hp))
  letI : Fintype (CubeResidues p) := Fintype.ofFinite _
  unfold cubeAverage
  simp only [tsum_fintype]
  exact continuous_const.mul (continuous_finsetSum Finset.univ (fun r _ => hF.comp (continuous_hyperbolic_action _)))

lemma cubeAverage_cusp_integral (p : O) (hp : p ≠ 0) (F : HyperbolicSpace → ℂ) (hF : Continuous F)
    (M : SL(2, O)) (b : O) (v : ℝ) (hv : 0 < v) :
    (∫ z in periodDomain, cubeAverage p hp F (integralComplexMatrix M • upperPoint (ringComplex b * z) v hv)) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ ^ 3 *
        ∑' r : CubeResidues p, ∫ z in periodDomain,
          F (cubeAverageMatrix p hp (cubeResidueRepresentative p r) •
            (integralComplexMatrix M • upperPoint (ringComplex b * z) v hv)) := by
  letI : Finite (CubeResidues p) := (Ideal.span {p ^ 3}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero 3 hp))
  letI : Fintype (CubeResidues p) := Fintype.ofFinite _
  letI := periodDomain_finiteMeasure
  have hi (r : CubeResidues p) : IntegrableOn
      (fun z : ℂ => F (cubeAverageMatrix p hp (cubeResidueRepresentative p r) •
        (integralComplexMatrix M • upperPoint (ringComplex b * z) v hv))) periodDomain := by
    apply (periodDomain_continuous_memLp _ ?_).integrable (by norm_num)
    exact (((hF.comp (continuous_hyperbolic_action _)).comp (continuous_hyperbolic_action _)).comp
      (upperCoordinatesHomeomorph.continuous.comp
        (show Continuous (fun z : ℂ => (⟨(ringComplex b * z, v), hv⟩ : UpperCoordinates)) by fun_prop)))
  unfold cubeAverage
  simp only [tsum_fintype]
  rw [integral_const_mul]
  congr 1
  exact integral_finsetSum Finset.univ (fun r _ => hi r)

lemma principalNorm_complex_ne_zero (p : O) (hp : p ≠ 0) : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := by
  have hr : (Ideal.absNorm (Ideal.span {p}) : ℝ) ≠ 0 := by
    rw [← ringComplex_norm_sq_eq_absNorm_span]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (ringComplex_ne_zero hp))
  exact_mod_cast hr

/-- The exact height weights turn the surviving phase strata into the square of the prime norm. -/
theorem actualCubeCuspPhaseSum_height (A : rationalExtension) (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (hA : lambda ^ 2 ∣ (A : SL(2, O)) 0 0 - 1) :
    actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 2 := by
  have hn := principalNorm_complex_ne_zero p hp.ne_zero
  by_cases hC : p ∣ (A : SL(2, O)) 1 0
  · rw [actualCubeCuspPhaseSum_dvd A p hp hprimary hA hC, cubeCuspHeightWeight_zero p hp.ne_zero]
    field_simp
  · rw [actualCubeCuspPhaseSum_coprime A p hp hprimary hA (hp.coprime_iff_not_dvd.mpr hC).symm,
      cubeCuspHeightWeight_zero p hp.ne_zero, cubeCuspHeightWeight_three p hp.ne_zero]
    field_simp <;> ring

/-- Every primary rational cusp has the expected cube-average constant term. -/
theorem cubeSource_average_primary (A : rationalExtension) (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (hA : lambda ^ 2 ∣ (A : SL(2, O)) 0 0 - 1)
    (v : ℝ) (hv : 0 < v) :
    (∫ z in periodDomain, cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix (A : SL(2, O)) • upperPoint (ringComplex (p ^ 3) * z) v hv)) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ * rationalSourceCuspConstant A * (v : ℂ) ^ (2 / 3 : ℂ) := by
  rw [cubeAverage_cusp_integral p hp.ne_zero cubicSourceResidualFunction cubicSourceResidualFunction_continuous]
  have hterm (r : CubeResidues p) := rationalSourceCubeBranch_average A
    (actualCubeCuspData (A : SL(2, O)) p (cubeResidueRepresentative p r) hp hprimary) hp.ne_zero v hv
  simp_rw [hterm]
  rw [tsum_mul_left]
  change (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ ^ 3 *
    ((rationalSourceCuspConstant A * (v : ℂ) ^ (2 / 3 : ℂ)) *
      actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p)) = _
  rw [actualCubeCuspPhaseSum_height A p hp hprimary hA]
  have hn := principalNorm_complex_ne_zero p hp.ne_zero
  field_simp <;> ring

def cubeSourceDifference (p : O) (hp : p ≠ 0) (w : HyperbolicSpace) : ℂ :=
  cubeAverage p hp cubicSourceResidualFunction w -
    (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ * cubicSourceResidualFunction w

lemma cubeSourceDifference_continuous (p : O) (hp : p ≠ 0) : Continuous (cubeSourceDifference p hp) :=
  (cubeAverage_continuous p hp cubicSourceResidualFunction cubicSourceResidualFunction_continuous).sub
    (continuous_const.mul cubicSourceResidualFunction_continuous)

lemma cubeAverageMatrix_period (p : O) (hp : p ≠ 0) (q n : O) :
    cubeAverageMatrix p hp (q + p ^ 3 * n) = complexTranslation (3 * ringComplex n) * cubeAverageMatrix p hp q := by
  have hz := cubeDilationRoot_ne_zero p hp
  have he : cubeDilationRoot p ^ 2 = ringComplex p ^ 3 := by rw [cubeDilationRoot_sq, map_pow]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubeAverageMatrix_entries, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, complexTranslation, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_add, map_mul, map_pow,
      zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
  field_simp
  linear_combination -(ringComplex n) * he

lemma cubeSummand_congr (p : O) (hp : p ≠ 0) (F : HyperbolicSpace → ℂ)
    (hper : ∀ n : O, ∀ w, F (complexTranslation (3 * ringComplex n) • w) = F w)
    (q r : O) (hqr : p ^ 3 ∣ q - r) (w : HyperbolicSpace) :
    F (cubeAverageMatrix p hp q • w) = F (cubeAverageMatrix p hp r • w) := by
  obtain ⟨n, hn⟩ := hqr
  have hq : q = r + p ^ 3 * n := by linear_combination hn
  rw [hq, cubeAverageMatrix_period, mul_smul, hper]

lemma cubeAverageMatrix_shift_one (p : O) (hp : p ≠ 0) (q t : O) (ht : p ^ 3 - 1 = 3 * t) :
    cubeAverageMatrix p hp q * complexTranslation 1 = complexTranslation 1 * cubeAverageMatrix p hp (q - t) := by
  have hz := cubeDilationRoot_ne_zero p hp
  have he : cubeDilationRoot p ^ 2 = ringComplex p ^ 3 := by rw [cubeDilationRoot_sq, map_pow]
  have ht' : ringComplex p ^ 3 - 1 = 3 * ringComplex t := by
    simpa only [map_sub, map_pow, map_one, map_mul, map_ofNat] using congrArg ringComplex ht
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      cubeAverageMatrix_entries, complexTranslation, Matrix.of_apply, map_sub,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
  field_simp
  linear_combination -he - ht'

/-- Primary cube averages retain the source's rational translation symmetry. -/
theorem cubeAverage_period_one (p : O) (hp : p ≠ 0) (hprimary : lambda ^ 2 ∣ p - 1)
    (F : HyperbolicSpace → ℂ)
    (hper : ∀ n : O, ∀ w, F (complexTranslation (3 * ringComplex n) • w) = F w)
    (hone : ∀ w, F (complexTranslation 1 • w) = F w) (w : HyperbolicSpace) :
    cubeAverage p hp F (complexTranslation 1 • w) = cubeAverage p hp F w := by
  obtain ⟨t, ht⟩ := primary_pow_mod_three p hprimary 3
  let c := Ideal.Quotient.mk (Ideal.span {p ^ 3}) t
  let e : CubeResidues p ≃ CubeResidues p := {
    toFun := fun r => r - c
    invFun := fun r => r + c
    left_inv := fun r => sub_add_cancel r c
    right_inv := fun r => add_sub_cancel_right r c }
  have hterm (r : CubeResidues p) : F (cubeAverageMatrix p hp (cubeResidueRepresentative p r) •
      (complexTranslation 1 • w)) = F (cubeAverageMatrix p hp (cubeResidueRepresentative p (e r)) • w) := by
    rw [← mul_smul, cubeAverageMatrix_shift_one p hp _ t ht, mul_smul, hone]
    apply cubeSummand_congr p hp F hper _ _ _ w
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    simp only [map_sub, cubeResidueRepresentative_spec]
    rfl
  unfold cubeAverage
  congr 1
  calc
    _ = ∑' r : CubeResidues p, F (cubeAverageMatrix p hp (cubeResidueRepresentative p (e r)) • w) := tsum_congr hterm
    _ = _ := e.tsum_eq (fun r : CubeResidues p => F (cubeAverageMatrix p hp (cubeResidueRepresentative p r) • w))

lemma cubicSourceResidualFunction_period_one_action (w : HyperbolicSpace) :
    cubicSourceResidualFunction (complexTranslation 1 • w) = cubicSourceResidualFunction w := by
  obtain ⟨z, v, hv, rfl⟩ := upperPoint_surjective w
  rw [complexTranslation_action]
  have h := cubicSourceResidualFunction_rational (rationalUnipotent 1) (upperPoint z v hv)
  change cubicSourceResidualFunction (rationalComplex (rationalUnipotent 1) • upperPoint z v hv) = _ at h
  rw [rationalUnipotent_action] at h
  simpa only [Int.cast_one] using h

lemma cubeSourceDifference_period_one (p : O) (hp : p ≠ 0) (hprimary : lambda ^ 2 ∣ p - 1)
    (w : HyperbolicSpace) : cubeSourceDifference p hp (complexTranslation 1 • w) = cubeSourceDifference p hp w := by
  have hper (n : O) (u : HyperbolicSpace) :
      cubicSourceResidualFunction (complexTranslation (3 * ringComplex n) • u) = cubicSourceResidualFunction u := by
    obtain ⟨z, v, hv, rfl⟩ := upperPoint_surjective u
    rw [complexTranslation_action]
    exact cubicSourceResidualFunction_period v hv z n
  unfold cubeSourceDifference
  rw [cubeAverage_period_one p hp hprimary _ hper cubicSourceResidualFunction_period_one_action,
    cubicSourceResidualFunction_period_one_action]

/-- A rational cusp becomes primary after at most one integral translation and a sign. -/
lemma rationalCusp_primary_cases (A : rationalExtension) :
    (lambda ^ 2 ∣ (A : SL(2, O)) 0 0 - 1 ∨ lambda ^ 2 ∣ -(A : SL(2, O)) 0 0 - 1) ∨
    (lambda ^ 2 ∣ (A : SL(2, O)) 0 0 + (A : SL(2, O)) 1 0 - 1 ∨
      lambda ^ 2 ∣ -((A : SL(2, O)) 0 0 + (A : SL(2, O)) 1 0) - 1) := by
  obtain ⟨a, ha⟩ := rationalExtension_entry_integer A 0 0
  obtain ⟨c, hc⟩ := rationalExtension_entry_integer A 1 0
  rcases integer_congruence_primary_cases _ a ha with h0 | h1 | h1
  · right
    have hlambda : lambda ^ 2 ∣ (A : SL(2, O)) 0 0 := lambda_sq_dvd_three.trans h0
    rcases integer_congruence_primary_cases _ c hc with hC | hC | hC
    · have hd : (3 : O) ∣ (1 : O) := by
        have hdet : (A : SL(2, O)) 0 0 * (A : SL(2, O)) 1 1 -
            (A : SL(2, O)) 0 1 * (A : SL(2, O)) 1 0 = 1 := by
          simpa only [Matrix.det_fin_two] using (A : SL(2, O)).property
        rw [← hdet]
        exact dvd_sub (h0.mul_right _) (hC.mul_left _)
      have hl : lambda ∣ lambda ^ 2 := ⟨lambda, by ring⟩
      exact (lambda_not_dvd_two (hl.trans (lambda_sq_dvd_three.trans (hd.trans (one_dvd 2))))).elim
    · exact Or.inl (by convert dvd_add hlambda hC using 1 <;> ring)
    · exact Or.inr (by convert dvd_add (dvd_neg.mpr hlambda) hC using 1 <;> ring)
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr h1)

def rationalCentralSign : SL(2, ℤ) := ⟨!![-1, 0; 0, -1], by simp [Matrix.det_fin_two]⟩

lemma rationalCentralSign_action (w : HyperbolicSpace) :
    integralComplexMatrix (rationalEmbedding rationalCentralSign) • w = w := by
  have he : integralComplexMatrix (rationalEmbedding rationalCentralSign) = complexDiagonal (-1) (by norm_num) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [rationalCentralSign, rationalEmbedding, integralComplexMatrix, complexDiagonal]
  obtain ⟨z, v, hv, rfl⟩ := upperPoint_surjective w
  rw [he, complexDiagonal_action]
  apply upperPoint_congr <;> simp

lemma rationalCentralSign_mul_entry (A : rationalExtension) :
    ((rationalSourceLift rationalCentralSign * A : rationalExtension) : SL(2, O)) 0 0 =
      -(A : SL(2, O)) 0 0 := by
  simp [rationalSourceLift, rationalCentralSign, rationalEmbedding,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma rationalUnipotent_one_mul_entry (A : rationalExtension) :
    ((rationalSourceLift (rationalUnipotent 1) * A : rationalExtension) : SL(2, O)) 0 0 =
      (A : SL(2, O)) 0 0 + (A : SL(2, O)) 1 0 := by
  simp [rationalSourceLift, rationalUnipotent, rationalEmbedding,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma rationalUnipotent_one_complex :
    integralComplexMatrix (rationalEmbedding (rationalUnipotent 1)) = complexTranslation 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalEmbedding, rationalUnipotent, integralComplexMatrix, complexTranslation]

lemma rationalCusp_primary_normalization (A : rationalExtension) (F : HyperbolicSpace → ℂ)
    (hF : ∀ w, F (complexTranslation 1 • w) = F w) :
    ∃ B : rationalExtension, lambda ^ 2 ∣ (B : SL(2, O)) 0 0 - 1 ∧
      ∀ w, F (integralComplexMatrix (B : SL(2, O)) • w) = F (integralComplexMatrix (A : SL(2, O)) • w) := by
  have hsign (B : rationalExtension) (hB : lambda ^ 2 ∣ -(B : SL(2, O)) 0 0 - 1) :
      ∃ C : rationalExtension, lambda ^ 2 ∣ (C : SL(2, O)) 0 0 - 1 ∧
        ∀ w, F (integralComplexMatrix (C : SL(2, O)) • w) = F (integralComplexMatrix (B : SL(2, O)) • w) := by
    refine ⟨rationalSourceLift rationalCentralSign * B, ?_, ?_⟩
    · rwa [rationalCentralSign_mul_entry]
    · intro w
      change F (integralComplexMatrix (rationalEmbedding rationalCentralSign * (B : SL(2, O))) • w) = _
      rw [map_mul, mul_smul, rationalCentralSign_action]
  rcases rationalCusp_primary_cases A with (h | h) | h
  · exact ⟨A, h, fun _ => rfl⟩
  · exact hsign A h
  · let B := rationalSourceLift (rationalUnipotent 1) * A
    have hBA (w : HyperbolicSpace) : F (integralComplexMatrix (B : SL(2, O)) • w) =
        F (integralComplexMatrix (A : SL(2, O)) • w) := by
      change F (integralComplexMatrix (rationalEmbedding (rationalUnipotent 1) * (A : SL(2, O))) • w) = _
      rw [map_mul, mul_smul, rationalUnipotent_one_complex, hF]
    have hb : (B : SL(2, O)) 0 0 = (A : SL(2, O)) 0 0 + (A : SL(2, O)) 1 0 :=
      rationalUnipotent_one_mul_entry A
    rcases h with h | h
    · exact ⟨B, by rwa [hb], hBA⟩
    · obtain ⟨C, hC, hCB⟩ := hsign B (by rwa [hb])
      exact ⟨C, hC, fun w => (hCB w).trans (hBA w)⟩

lemma continuous_rationalCusp_affine (F : HyperbolicSpace → ℂ) (hF : Continuous F)
    (M : SL(2, O)) (b c : ℂ) (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => F (integralComplexMatrix M • upperPoint (b * z + c) v hv)) :=
  (hF.comp (continuous_hyperbolic_action _)).comp
    (upperCoordinatesHomeomorph.continuous.comp
      (show Continuous (fun z : ℂ => (⟨(b * z + c, v), hv⟩ : UpperCoordinates)) by fun_prop))

lemma integrable_rationalCusp_scaled (F : HyperbolicSpace → ℂ) (hF : Continuous F)
    (M : SL(2, O)) (b : ℂ) (v : ℝ) (hv : 0 < v) :
    IntegrableOn (fun z : ℂ => F (integralComplexMatrix M • upperPoint (b * z) v hv)) periodDomain := by
  letI := periodDomain_finiteMeasure
  apply (periodDomain_continuous_memLp _ ?_).integrable (by norm_num)
  simpa only [add_zero] using continuous_rationalCusp_affine F hF M b 0 v hv

lemma cubeSourceDifference_primary_average_zero (A : rationalExtension) (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (hA : lambda ^ 2 ∣ (A : SL(2, O)) 0 0 - 1)
    (v : ℝ) (hv : 0 < v) :
    (∫ z in periodDomain, cubeSourceDifference p hp.ne_zero
      (integralComplexMatrix (A : SL(2, O)) • upperPoint (ringComplex (p ^ 3) * z) v hv)) = 0 := by
  have hU := integrable_rationalCusp_scaled _
    (cubeAverage_continuous p hp.ne_zero _ cubicSourceResidualFunction_continuous)
    (A : SL(2, O)) (ringComplex (p ^ 3)) v hv
  have hS := integrable_rationalCusp_scaled _ cubicSourceResidualFunction_continuous
    (A : SL(2, O)) (ringComplex (p ^ 3)) v hv
  have hav := rationalSourceCusp_average_enlarged_affine A (p ^ 3) (pow_ne_zero 3 hp.ne_zero) 0 v hv
  simp only [add_zero] at hav
  unfold cubeSourceDifference
  rw [integral_sub hU (hS.const_mul _), integral_const_mul,
    cubeSource_average_primary A p hp hprimary hA, hav]
  ring

/-- Every rational cusp of the cube difference has zero mean on the same enlarged cell. -/
theorem cubeSourceDifference_rational_average_zero (A : rationalExtension) (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (v : ℝ) (hv : 0 < v) :
    (∫ z in periodDomain, cubeSourceDifference p hp.ne_zero
      (integralComplexMatrix (A : SL(2, O)) • upperPoint (ringComplex (p ^ 3) * z) v hv)) = 0 := by
  obtain ⟨B, hB, he⟩ := rationalCusp_primary_normalization A (cubeSourceDifference p hp.ne_zero)
    (cubeSourceDifference_period_one p hp.ne_zero hprimary)
  simp_rw [← he]
  exact cubeSourceDifference_primary_average_zero B p hp hprimary hB v hv

lemma cubicSourceResidualFunction_rationalCusp_period (A : rationalExtension)
    (z : ℂ) (v : ℝ) (hv : 0 < v) (n : O) :
    cubicSourceResidualFunction (integralComplexMatrix (A : SL(2, O)) • upperPoint (z + 3 * ringComplex n) v hv) =
      cubicSourceResidualFunction (integralComplexMatrix (A : SL(2, O)) • upperPoint z v hv) := by
  rw [cubicSourceResidualFunction_automorphy, cubicSourceResidualFunction_automorphy,
    cubicSourceResidualFunction_period]

lemma cubeSource_summand_rationalCusp_period {A : rationalExtension} {p q : O}
    (d : CubeCuspData (A : SL(2, O)) p q) (hp : p ≠ 0) (z : ℂ) (v : ℝ) (hv : 0 < v) (n : O) :
    cubicSourceResidualFunction (cubeAverageMatrix p hp q •
      (integralComplexMatrix (A : SL(2, O)) • upperPoint (z + 3 * ringComplex (p ^ 3 * n)) v hv)) =
    cubicSourceResidualFunction (cubeAverageMatrix p hp q •
      (integralComplexMatrix (A : SL(2, O)) • upperPoint z v hv)) := by
  let T := cubeCuspTriangular d hp
  have hT : T 1 0 = 0 := (cubeCuspTriangular_entries d hp).2.1
  let V := v / ‖T 1 1‖ ^ 2
  have hV : 0 < V := div_pos hv (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (complexUpper_lowerRight_ne_zero T hT)))
  have he (x : ℂ) : cubicSourceResidualFunction (cubeAverageMatrix p hp q •
      (integralComplexMatrix (A : SL(2, O)) • upperPoint x v hv)) =
      cubicSourceResidualFunction (integralComplexMatrix d.matrix •
        upperPoint ((T 0 0 * x + T 0 1) / T 1 1) V hV) := by
    rw [← mul_smul, cubeCuspTriangular_factor d hp, mul_smul]
    change cubicSourceResidualFunction (integralComplexMatrix d.matrix • (T • upperPoint x v hv)) = _
    rw [complexUpper_action T hT]
  have hx : (T 0 0 * (z + 3 * ringComplex (p ^ 3 * n)) + T 0 1) / T 1 1 =
      (T 0 0 * z + T 0 1) / T 1 1 + 3 * ringComplex (p ^ (2 * d.exponent.val) * n) := by
    calc
      _ = (T 0 0 * z + T 0 1) / T 1 1 + 3 * ((T 0 0 / T 1 1) * ringComplex (p ^ 3)) * ringComplex n := by
        rw [map_mul]
        ring
      _ = _ := by rw [cubeCuspTriangular_integral_scale d hp, map_mul]; ring
  rw [he, he, hx]
  exact cubicSourceResidualFunction_rationalCusp_period ⟨d.matrix, d.rational_mem⟩ _ V hV _

lemma cubeSourceDifference_rationalCusp_period (A : rationalExtension) (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (z : ℂ) (v : ℝ) (hv : 0 < v) (n : O) :
    cubeSourceDifference p hp.ne_zero
      (integralComplexMatrix (A : SL(2, O)) • upperPoint (z + 3 * ringComplex (p ^ 3 * n)) v hv) =
    cubeSourceDifference p hp.ne_zero (integralComplexMatrix (A : SL(2, O)) • upperPoint z v hv) := by
  have hU : cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix (A : SL(2, O)) • upperPoint (z + 3 * ringComplex (p ^ 3 * n)) v hv) =
      cubeAverage p hp.ne_zero cubicSourceResidualFunction
        (integralComplexMatrix (A : SL(2, O)) • upperPoint z v hv) := by
    exact congrArg (fun t : ℂ => (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ ^ 3 * t)
      (tsum_congr (fun r : CubeResidues p => cubeSource_summand_rationalCusp_period (A := A)
        (actualCubeCuspData (A : SL(2, O)) p (cubeResidueRepresentative p r) hp hprimary) hp.ne_zero z v hv n))
  exact congrArg₂ (fun a b : ℂ => a - (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ * b)
    hU (cubicSourceResidualFunction_rationalCusp_period A z v hv (p ^ 3 * n))

/-- Integral dilation and arbitrary translation preserve the cube difference's zero mean. -/
theorem cubeSourceDifference_rational_average_affine_zero (A : rationalExtension) (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (b : O) (hb : b ≠ 0) (c : ℂ) (v : ℝ) (hv : 0 < v) :
    (∫ z in periodDomain, cubeSourceDifference p hp.ne_zero
      (integralComplexMatrix (A : SL(2, O)) • upperPoint (ringComplex (p ^ 3) * (ringComplex b * z + c)) v hv)) = 0 := by
  let f := fun z : ℂ => cubeSourceDifference p hp.ne_zero
    (integralComplexMatrix (A : SL(2, O)) • upperPoint (ringComplex (p ^ 3) * z) v hv)
  have hf : Continuous f := by
    simpa only [add_zero] using continuous_rationalCusp_affine _ (cubeSourceDifference_continuous p hp.ne_zero)
      (A : SL(2, O)) (ringComplex (p ^ 3)) 0 v hv
  have hper (n : O) (z : ℂ) : f (z + 3 * ringComplex n) = f z := by
    have he : ringComplex (p ^ 3) * (z + 3 * ringComplex n) =
        ringComplex (p ^ 3) * z + 3 * ringComplex (p ^ 3 * n) := by rw [map_mul]; ring
    dsimp only [f]
    rw [he, cubeSourceDifference_rationalCusp_period A p hp hprimary]
  exact (period_integral_eisenstein_affine f hf.measurable hper b hb c).trans
    (cubeSourceDifference_rational_average_zero A p hp hprimary v hv)

/-- Primitive first-column normalization is exactly an upper triangular factorization. -/
lemma complexFirstColumnTriangular_entries (B N : SL(2, ℂ)) (s : ℂ) (hs : s ≠ 0)
    (h0 : B 0 0 = s * N 0 0) (h1 : B 1 0 = s * N 1 0) :
    (N⁻¹ * B) 0 0 = s ∧ (N⁻¹ * B) 1 0 = 0 ∧ (N⁻¹ * B) 1 1 = s⁻¹ := by
  have hd : N 0 0 * N 1 1 - N 0 1 * N 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using N.property
  have h00 : (N⁻¹ * B) 0 0 = s := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, h0, h1]
    linear_combination s * hd
  have h10 : (N⁻¹ * B) 1 0 = 0 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, h0, h1]
    ring
  refine ⟨h00, h10, ?_⟩
  have ht : s * (N⁻¹ * B) 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, h00, h10, mul_zero, sub_zero] using (N⁻¹ * B).property
  apply mul_left_cancel₀ hs
  rw [ht, mul_inv_cancel₀ hs]

/-- Every inverse branch maps a common `p^6` cell into an integral dilation of a `p^3` cell. -/
theorem cubeSourceDifference_inverse_rational_average_zero (A : rationalExtension) (p q : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (v : ℝ) (hv : 0 < v) :
    (∫ z in periodDomain, cubeSourceDifference p hp.ne_zero
      ((cubeAverageMatrix p hp.ne_zero q)⁻¹ •
        (integralComplexMatrix (A : SL(2, O)) • upperPoint (ringComplex (p ^ 6) * z) v hv))) = 0 := by
  obtain ⟨j, _, N, hx, hy, hNA⟩ := primePowerCusp_inverse_reduction (A : SL(2, O)) p q 3 hp hprimary
  let N' : rationalExtension := ⟨N, rationalExtension_of_congruent A N hNA⟩
  let B := (cubeAverageMatrix p hp.ne_zero q)⁻¹ * integralComplexMatrix (A : SL(2, O))
  let T := (integralComplexMatrix N)⁻¹ * B
  let s := (cubeDilationRoot p)⁻¹ * ringComplex p ^ j
  have hz := cubeDilationRoot_ne_zero p hp.ne_zero
  have hpC := ringComplex_ne_zero hp.ne_zero
  have hs : s ≠ 0 := mul_ne_zero (inv_ne_zero hz) (pow_ne_zero j hpC)
  have he : cubeDilationRoot p ^ 2 = ringComplex p ^ 3 := by rw [cubeDilationRoot_sq, map_pow]
  have hx' : ringComplex p ^ 3 * ringComplex ((A : SL(2, O)) 0 0) -
      3 * ringComplex q * ringComplex ((A : SL(2, O)) 1 0) = ringComplex p ^ j * ringComplex (N 0 0) := by
    simpa only [map_sub, map_mul, map_pow, map_ofNat] using congrArg ringComplex hx
  have hy' : ringComplex ((A : SL(2, O)) 1 0) = ringComplex p ^ j * ringComplex (N 1 0) := by
    simpa only [map_mul, map_pow] using congrArg ringComplex hy
  have hentry (M : SL(2, O)) (i k : Fin 2) : integralComplexMatrix M i k = ringComplex (M i k) := rfl
  have h0 : B 0 0 = s * integralComplexMatrix N 0 0 := by
    dsimp only [B]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      cubeAverageMatrix_entries, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hentry]
    change cubeDilationRoot p * ringComplex ((A : SL(2, O)) 0 0) +
      (-((cubeDilationRoot p)⁻¹ * (3 * ringComplex q))) * ringComplex ((A : SL(2, O)) 1 0) = _
    calc
      _ = (cubeDilationRoot p)⁻¹ * (ringComplex p ^ 3 * ringComplex ((A : SL(2, O)) 0 0) -
          3 * ringComplex q * ringComplex ((A : SL(2, O)) 1 0)) := by
        rw [← he]
        field_simp
        ring
      _ = _ := by rw [hx']; exact (mul_assoc _ _ _).symm
  have h1 : B 1 0 = s * integralComplexMatrix N 1 0 := by
    dsimp only [B, s]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      cubeAverageMatrix_entries, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hentry,
      neg_zero, zero_mul, zero_add, hy', mul_assoc]
  obtain ⟨h00, h10, h11⟩ := complexFirstColumnTriangular_entries B (integralComplexMatrix N) s hs h0 h1
  change T 0 0 = s at h00
  change T 1 0 = 0 at h10
  change T 1 1 = s⁻¹ at h11
  have hscale : (T 0 0 / T 1 1) * ringComplex (p ^ 3) = ringComplex (p ^ (2 * j)) := by
    rw [h00, h11, div_inv_eq_mul, map_pow, map_pow,
      show ringComplex p ^ (2 * j) = (ringComplex p ^ j) ^ 2 by rw [mul_comm 2 j, pow_mul]]
    dsimp only [s]
    rw [← he]
    field_simp
  let c := (T 0 1 / T 1 1) / ringComplex (p ^ 3)
  let V := v / ‖T 1 1‖ ^ 2
  have hV : 0 < V := div_pos hv (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (complexUpper_lowerRight_ne_zero T h10)))
  have hcoord (z : ℂ) : (T 0 0 * (ringComplex (p ^ 6) * z) + T 0 1) / T 1 1 =
      ringComplex (p ^ 3) * (ringComplex (p ^ (2 * j)) * z + c) := by
    have hpow : ringComplex (p ^ 6) = ringComplex (p ^ 3) * ringComplex (p ^ 3) := by
      rw [← map_mul, ← pow_add]
    calc
      _ = ringComplex (p ^ 3) * (((T 0 0 / T 1 1) * ringComplex (p ^ 3)) * z + c) := by
        rw [hpow]
        dsimp only [c]
        field_simp
        <;> ring
      _ = _ := by rw [hscale]
  have hact (z : ℂ) : (cubeAverageMatrix p hp.ne_zero q)⁻¹ •
      (integralComplexMatrix (A : SL(2, O)) • upperPoint (ringComplex (p ^ 6) * z) v hv) =
      integralComplexMatrix N • upperPoint (ringComplex (p ^ 3) * (ringComplex (p ^ (2 * j)) * z + c)) V hV := by
    have hfactor : B = integralComplexMatrix N * T := by dsimp only [T]; group
    rw [← mul_smul]
    change B • upperPoint (ringComplex (p ^ 6) * z) v hv = _
    rw [hfactor, mul_smul]
    change integralComplexMatrix N • (T • upperPoint (ringComplex (p ^ 6) * z) v hv) = _
    rw [complexUpper_action T h10, hcoord]
  simp_rw [hact]
  exact cubeSourceDifference_rational_average_affine_zero N' p hp hprimary (p ^ (2 * j))
    (pow_ne_zero _ hp.ne_zero) c V hV

lemma kernelCoverLegAdjointFunction_continuous {H J : Subgroup (SL(2, O))}
    [J.IsFiniteRelIndex globalKubotaKernel] (e : H ≃* J) (g : SL(2, ℂ))
    (he : IntegralCoverIntertwines e g) (f : IntegralOrbitQuotient H → ℂ) (hf : Continuous f) :
    Continuous (kernelCoverLegAdjointFunction e g he f) :=
  integralCoverTraceFunction_continuous J globalKubotaKernel _
    (hf.comp (integralConjugateMap_continuous _ _ _))

/-- A common zero-mean cell passes through every finite fiber of the actual adjoint trace. -/
theorem kernelCoverLegAdjointFunction_rational_average_zero {H J : Subgroup (SL(2, O))}
    [J.IsFiniteRelIndex globalKubotaKernel] (e : H ≃* J) (g : SL(2, ℂ))
    (he : IntegralCoverIntertwines e g) (f : IntegralOrbitQuotient H → ℂ) (hf : Continuous f)
    (b : O) (v : ℝ) (hv : 0 < v)
    (havg : ∀ M : rationalExtension, (∫ z in periodDomain,
      f (integralOrbitProjection H (g⁻¹ •
        (integralComplexMatrix (M : SL(2, O)) • upperPoint (ringComplex b * z) v hv)))) = 0)
    (A : rationalExtension) :
    (∫ z in periodDomain, kernelCoverLegAdjointFunction e g he f
      (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix (A : SL(2, O)) • upperPoint (ringComplex b * z) v hv))) = 0 := by
  letI := periodDomain_finiteMeasure
  letI : Fintype (IntegralCoverCosets J globalKubotaKernel) := Fintype.ofFinite _
  let M (r : IntegralCoverCosets J globalKubotaKernel) : rationalExtension :=
    ⟨(((integralCoverRep J globalKubotaKernel r)⁻¹ : globalKubotaKernel) : SL(2, O)) * (A : SL(2, O)),
      rationalExtension.mul_mem (levelThree_le_rationalExtension
        (globalKubotaKernel_le_levelThree ((integralCoverRep J globalKubotaKernel r)⁻¹).property)) A.property⟩
  let F (r : IntegralCoverCosets J globalKubotaKernel) (z : ℂ) :=
    f (integralOrbitProjection H (g⁻¹ • (integralComplexMatrix (M r : SL(2, O)) • upperPoint (ringComplex b * z) v hv)))
  have hi (r : IntegralCoverCosets J globalKubotaKernel) : IntegrableOn (F r) periodDomain :=
    integrable_rationalCusp_scaled _ ((hf.comp (continuous_integralOrbitProjection H)).comp
      (continuous_hyperbolic_action g⁻¹)) (M r : SL(2, O)) (ringComplex b) v hv
  have hterm (r : IntegralCoverCosets J globalKubotaKernel) (z : ℂ) :
      f (integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
        (integralCoverFiberPoint J globalKubotaKernel r
          (integralComplexMatrix (A : SL(2, O)) • upperPoint (ringComplex b * z) v hv))) = F r z := by
    rw [integralCoverFiberPoint_rep, integralSubgroup_smul, integralConjugateMap_projection]
    dsimp only [F, M]
    rw [map_mul, mul_smul]
  change (∫ z in periodDomain, ∑ r : IntegralCoverCosets J globalKubotaKernel,
    f (integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
      (integralCoverFiberPoint J globalKubotaKernel r
        (integralComplexMatrix (A : SL(2, O)) • upperPoint (ringComplex b * z) v hv)))) = 0
  simp_rw [hterm]
  rw [integral_finsetSum Finset.univ (fun r _ => hi r)]
  exact Finset.sum_eq_zero (fun r _ => havg (M r))

lemma cubicSourceResidualFunction_kernel_invariant (k : globalKubotaKernel) (w : HyperbolicSpace) :
    cubicSourceResidualFunction (k • w) = cubicSourceResidualFunction w := by
  obtain ⟨hk, hchar⟩ := (globalKubotaKernel_mem (k : SL(2, O))).mp k.property
  change cubicSourceResidualFunction (integralComplexMatrix (k : SL(2, O)) • w) = _
  rw [cubicSourceResidualFunction_automorphy ⟨(k : SL(2, O)), levelThree_le_rationalExtension hk⟩,
    extendedComplexCharacter_restrict ⟨(k : SL(2, O)), hk⟩, hchar, one_mul]

def cubicSourceQuotientFunction : KernelQuotient → ℂ :=
  Quotient.lift cubicSourceResidualFunction (by
    rintro w u ⟨k, rfl⟩
    exact (cubicSourceResidualFunction_kernel_invariant k w).symm)

lemma cubicSourceQuotientFunction_projection (w : HyperbolicSpace) :
    cubicSourceQuotientFunction (integralOrbitProjection globalKubotaKernel w) = cubicSourceResidualFunction w := rfl

lemma cubicSourceQuotientFunction_continuous : Continuous cubicSourceQuotientFunction :=
  cubicSourceResidualFunction_continuous.quotient_lift _

lemma cubicSourceQuotientFunction_represents :
    kernelRationalSourceProjection cubicEisensteinResidue =ᵐ[integralQuotientVolume globalKubotaKernel]
      cubicSourceQuotientFunction := by
  change _ =ᵐ[Measure.map (integralOrbitProjection globalKubotaKernel)
    (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel))] _
  apply (ae_map_iff (measurable_integralOrbitProjection _).aemeasurable
    (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable cubicSourceQuotientFunction_continuous.measurable)).mpr
  exact ae_restrict_of_ae cubicSourceResidualFunction_represents_projection

/-- The identity branch and the translated cube branches share one finite cover. -/
def cubeLegTarget (p : O) (hp : p ≠ 0) : Option (CubeResidues p) → Subgroup (SL(2, O))
  | none => cubeCommonCover p
  | some r => cubeCommonTarget p hp r

lemma cubeLegTarget_le (p : O) (hp : p ≠ 0) (i : Option (CubeResidues p)) :
    cubeLegTarget p hp i ≤ globalKubotaKernel := by
  cases i with
  | none => exact cubeCommonCover_le p
  | some r => exact cubeCommonTarget_le p hp r

lemma cubeLegTarget_finiteIndex (p : O) (hp : p ≠ 0) (i : Option (CubeResidues p)) :
    (cubeLegTarget p hp i).FiniteIndex := by
  cases i with
  | none => exact cubeCommonCover_finiteIndex p hp
  | some r => exact cubeCommonTarget_finiteIndex p hp r

def cubeLegEquiv (p : O) (hp : p ≠ 0) : ∀ i : Option (CubeResidues p), cubeCommonCover p ≃* cubeLegTarget p hp i
  | none => MulEquiv.refl _
  | some r => cubeCommonEquiv p hp r

def cubeLegMatrix (p : O) (hp : p ≠ 0) : Option (CubeResidues p) → SL(2, ℂ)
  | none => 1
  | some r => cubeAverageMatrix p hp (cubeResidueRepresentative p r)

lemma cubeLeg_intertwines (p : O) (hp : p ≠ 0) (i : Option (CubeResidues p)) :
    IntegralCoverIntertwines (cubeLegEquiv p hp i) (cubeLegMatrix p hp i) := by
  cases i with
  | none => intro h; change 1 * integralComplexMatrix (h : SL(2, O)) = integralComplexMatrix (h : SL(2, O)) * 1; simp only [one_mul, mul_one]
  | some r => exact cubeCommon_intertwines p hp r

def cubeLegCoefficient (p : O) : Option (CubeResidues p) → ℂ
  | none => -(Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹
  | some _ => (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ ^ 3

def cubeLegFunction (p : O) (hp : p ≠ 0) (i : Option (CubeResidues p)) :
    IntegralOrbitQuotient (cubeCommonCover p) → ℂ :=
  fun q => cubicSourceQuotientFunction (integralCoverMap (cubeLegTarget_le p hp i)
    (integralConjugateMap (cubeLegEquiv p hp i) (cubeLegMatrix p hp i) (cubeLeg_intertwines p hp i) q))

lemma cubeLegFunction_continuous (p : O) (hp : p ≠ 0) (i : Option (CubeResidues p)) :
    Continuous (cubeLegFunction p hp i) :=
  (cubicSourceQuotientFunction_continuous.comp (integralCoverMap_continuous _)).comp
    (integralConjugateMap_continuous _ _ _)

lemma cubeLegFunction_projection (p : O) (hp : p ≠ 0) (i : Option (CubeResidues p)) (w : HyperbolicSpace) :
    cubeLegFunction p hp i (integralOrbitProjection (cubeCommonCover p) w) =
      cubicSourceResidualFunction (cubeLegMatrix p hp i • w) := rfl

def cubeCommonDifferenceFunction (p : O) (hp : p ≠ 0) : IntegralOrbitQuotient (cubeCommonCover p) → ℂ :=
  fun q => ∑' i : Option (CubeResidues p), cubeLegCoefficient p i * cubeLegFunction p hp i q

lemma cubeCommonDifferenceFunction_continuous (p : O) (hp : p ≠ 0) :
    Continuous (cubeCommonDifferenceFunction p hp) := by
  letI : Finite (CubeResidues p) := (Ideal.span {p ^ 3}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero 3 hp))
  letI : Fintype (CubeResidues p) := Fintype.ofFinite _
  unfold cubeCommonDifferenceFunction
  simp only [tsum_fintype]
  exact continuous_finsetSum Finset.univ (fun i _ => continuous_const.mul (cubeLegFunction_continuous p hp i))

lemma cubeCommonDifferenceFunction_projection (p : O) (hp : p ≠ 0) (w : HyperbolicSpace) :
    cubeCommonDifferenceFunction p hp (integralOrbitProjection (cubeCommonCover p) w) =
      cubeSourceDifference p hp w := by
  letI : Finite (CubeResidues p) := (Ideal.span {p ^ 3}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero 3 hp))
  letI : Fintype (CubeResidues p) := Fintype.ofFinite _
  unfold cubeCommonDifferenceFunction cubeSourceDifference cubeAverage
  simp only [tsum_fintype, Fintype.sum_option, cubeLegFunction_projection,
    cubeLegCoefficient, cubeLegMatrix, one_smul, ← Finset.mul_sum]
  ring

lemma integralProjection_quasiMeasurePreserving (H : Subgroup (SL(2, O))) (hH : H ≤ levelThree) :
    Measure.QuasiMeasurePreserving (integralOrbitProjection H) hyperbolicVolume (integralQuotientVolume H) := by
  let proj := integralOrbitProjection H
  have hp : Measurable proj := measurable_integralOrbitProjection _
  refine ⟨hp, Measure.AbsolutelyContinuous.mk fun S hS hzero => ?_⟩
  rw [Measure.map_apply hp hS]
  have hd : hyperbolicVolume ((proj ⁻¹' S) ∩ hyperbolicFundamentalSet H) = 0 := by
    simpa only [integralQuotientVolume, proj,
      Measure.map_apply (measurable_integralOrbitProjection _) hS,
      Measure.restrict_apply ((measurable_integralOrbitProjection _) hS)] using hzero
  have hinv : ∀ M : H, M • (proj ⁻¹' S) = proj ⁻¹' S := by
    intro M
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      change proj (M • u) ∈ S
      change proj u ∈ S at hu
      rwa [show proj (M • u) = proj u from integralOrbitProjection_eq _ M u]
    · intro hw
      refine ⟨M⁻¹ • w, ?_, smul_inv_smul M w⟩
      change proj (M⁻¹ • w) ∈ S
      rwa [show proj (M⁻¹ • w) = proj w from integralOrbitProjection_eq _ M⁻¹ w]
  exact (hyperbolicFundamentalSet_isFundamentalDomain H hH hyperbolicVolume).measure_zero_of_invariant _ hinv hd

/-- The actual common-cover difference vanishes: every adjoint trace has zero rational cusp mean. -/
theorem cubeSourceDifference_eq_zero (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) :
    cubeSourceDifference p hp.ne_zero = 0 := by
  letI : Finite (CubeResidues p) := (Ideal.span {p ^ 3}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero 3 hp.ne_zero))
  letI : Fintype (CubeResidues p) := Fintype.ofFinite _
  letI : ∀ i : Option (CubeResidues p), (cubeLegTarget p hp.ne_zero i).IsFiniteRelIndex globalKubotaKernel := fun i => by
    letI := cubeLegTarget_finiteIndex p hp.ne_zero i
    exact Subgroup.isFiniteRelIndex_of_finiteIndex
  let leg (i : Option (CubeResidues p)) := kernelCoverLeg (cubeCommonCover_le p) (cubeLegTarget_le p hp.ne_zero i)
    (cubeLegEquiv p hp.ne_zero i) (cubeLegMatrix p hp.ne_zero i) (cubeLeg_intertwines p hp.ne_zero i)
  let S := kernelRationalSourceProjection cubicEisensteinResidue
  let D := ∑ i : Option (CubeResidues p), cubeLegCoefficient p i • leg i S
  let f := cubeCommonDifferenceFunction p hp.ne_zero
  have hf : Continuous f := cubeCommonDifferenceFunction_continuous p hp.ne_zero
  have hleg (i : Option (CubeResidues p)) : leg i S =ᵐ[integralQuotientVolume (cubeCommonCover p)]
      cubeLegFunction p hp.ne_zero i :=
    kernelCoverLeg_representative (cubeCommonCover_le p) (cubeLegTarget_le p hp.ne_zero i)
      (cubeLegEquiv p hp.ne_zero i) (cubeLegMatrix p hp.ne_zero i) (cubeLeg_intertwines p hp.ne_zero i)
      S cubicSourceQuotientFunction cubicSourceQuotientFunction_represents
  have hrep : D =ᵐ[integralQuotientVolume (cubeCommonCover p)] f := by
    have hs := Lp.coeFn_fun_finsetSum Finset.univ
      (fun i : Option (CubeResidues p) => cubeLegCoefficient p i • leg i S)
    have hc := ae_all_iff.mpr (fun i : Option (CubeResidues p) => Lp.coeFn_smul (cubeLegCoefficient p i) (leg i S))
    have hr := ae_all_iff.mpr hleg
    filter_upwards [hs, hc, hr] with q hsum hscale hvalue
    change (∑ i : Option (CubeResidues p), cubeLegCoefficient p i • leg i S) q =
      ∑' i : Option (CubeResidues p), cubeLegCoefficient p i * cubeLegFunction p hp.ne_zero i q
    rw [hsum, tsum_fintype]
    change (∑ i : Option (CubeResidues p), (cubeLegCoefficient p i • leg i S) q) = _
    apply Finset.sum_congr rfl
    intro i _
    rw [hscale i, Pi.smul_apply, smul_eq_mul, hvalue i]
  have hD : D = 0 := by
    apply kernelCoverLeg_source_sum_vanish_of_zero_enlarged_averages
      (cubeLegTarget p hp.ne_zero) (cubeCommonCover_le p) (cubeLegTarget_le p hp.ne_zero)
      (cubeLegEquiv p hp.ne_zero) (cubeLegMatrix p hp.ne_zero) (cubeLeg_intertwines p hp.ne_zero)
      (cubeLegCoefficient p)
      (fun i => kernelCoverLegAdjointFunction (cubeLegEquiv p hp.ne_zero i) (cubeLegMatrix p hp.ne_zero i)
        (cubeLeg_intertwines p hp.ne_zero i) f)
    · intro i
      exact kernelCoverLegAdjointFunction_continuous _ _ _ f hf
    · intro i
      exact kernelCoverLegAdjointFunction_represents (cubeCommonCover_le p) (cubeLegTarget_le p hp.ne_zero i)
        (cubeLegEquiv p hp.ne_zero i) (cubeLegMatrix p hp.ne_zero i) (cubeLeg_intertwines p hp.ne_zero i)
        D f hf.measurable hrep
    · intro i A v hv _
      refine ⟨p ^ 6, pow_ne_zero 6 hp.ne_zero, ?_⟩
      apply kernelCoverLegAdjointFunction_rational_average_zero _ _ _ f hf (p ^ 6) v hv _ A
      intro M
      simp only [f, cubeCommonDifferenceFunction_projection]
      cases i with
      | none =>
        simp only [cubeLegMatrix, inv_one, one_smul]
        have hc (z : ℂ) : ringComplex (p ^ 3) * (ringComplex (p ^ 3) * z + 0) = ringComplex (p ^ 6) * z := by
          rw [add_zero, ← mul_assoc, ← map_mul, ← pow_add]
        simpa only [hc] using cubeSourceDifference_rational_average_affine_zero M p hp hprimary
          (p ^ 3) (pow_ne_zero 3 hp.ne_zero) 0 v hv
      | some r =>
        exact cubeSourceDifference_inverse_rational_average_zero M p (cubeResidueRepresentative p r) hp hprimary v hv
  have hzero : f =ᵐ[integralQuotientVolume (cubeCommonCover p)] fun _ => (0 : ℂ) := by
    rw [hD] at hrep
    exact hrep.symm.trans (Lp.coeFn_zero ℂ 2 (integralQuotientVolume (cubeCommonCover p)))
  have hglobal := (integralProjection_quasiMeasurePreserving (cubeCommonCover p)
    ((cubeCommonCover_le p).trans globalKubotaKernel_le_levelThree)).ae_eq_comp hzero
  have he : cubeSourceDifference p hp.ne_zero =ᵐ[hyperbolicVolume] fun _ => (0 : ℂ) := by
    simpa only [Function.comp_def, f, cubeCommonDifferenceFunction_projection] using hglobal
  exact Measure.eq_of_ae_eq he (cubeSourceDifference_continuous p hp.ne_zero) continuous_const

/-- Primary prime cubes act on the residual source by the inverse prime norm. -/
theorem cubicSourceResidualFunction_cube_eigenrelation (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (w : HyperbolicSpace) :
    cubeAverage p hp.ne_zero cubicSourceResidualFunction w =
      (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ * cubicSourceResidualFunction w := by
  have h := congrFun (cubeSourceDifference_eq_zero p hp hprimary) w
  exact sub_eq_zero.mp h

lemma cuspFrequency_mul_right (h c : O) : cuspFrequency (h * c) = cuspFrequency h * ringComplex c := by
  unfold cuspFrequency
  rw [map_mul]
  ring

lemma cuspFourierCharacter_continuous (h : O) : Continuous (fun z : ℂ => tracePhase (-cuspFrequency h * z)) := by
  change Continuous (fun z : ℂ => Complex.exp
    (2 * Real.pi * Complex.I * ((-cuspFrequency h * z) + starRingEnd ℂ (-cuspFrequency h * z))))
  fun_prop

lemma cuspFourierCharacter_fractional_period (c : O) (hc : c ≠ 0) (h q : O) (z : ℂ) :
    tracePhase (-cuspFrequency (h * c) * (z + 3 * ringComplex q / ringComplex c)) =
      tracePhase (-cuspFrequency (h * c) * z) := by
  have he : -cuspFrequency (h * c) * (z + 3 * ringComplex q / ringComplex c) =
      -cuspFrequency (h * c) * z + -(cuspFrequency h * (3 * ringComplex q)) := by
    rw [cuspFrequency_mul_right]
    field_simp [ringComplex_ne_zero hc]
    <;> ring
  rw [he, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, cuspFrequency_period, inv_one, mul_one]

lemma period_fourier_fractional_translation (f : ℂ → ℂ)
    (hper : ∀ n : O, ∀ z : ℂ, f (z + 3 * ringComplex n) = f z)
    (c : O) (hc : c ≠ 0) (h q : O) :
    (∫ z in periodDomain, f (z + 3 * ringComplex q / ringComplex c) * tracePhase (-cuspFrequency (h * c) * z)) =
      ∫ z in periodDomain, f z * tracePhase (-cuspFrequency (h * c) * z) := by
  let g := fun z : ℂ => f z * tracePhase (-cuspFrequency (h * c) * z)
  have hg (n : O) (z : ℂ) : g (z + 3 * ringComplex n) = g z := by
    dsimp only [g]
    rw [hper, cuspFrequency_negative_period]
  have hi := period_integral_translation g hg (3 * ringComplex q / ringComplex c)
  have he (z : ℂ) : g (3 * ringComplex q / ringComplex c + z) =
      f (z + 3 * ringComplex q / ringComplex c) * tracePhase (-cuspFrequency (h * c) * z) := by
    dsimp only [g]
    rw [add_comm (3 * ringComplex q / ringComplex c) z, cuspFourierCharacter_fractional_period c hc]
  simpa only [he, g] using hi

lemma cubeAverageMatrix_scaled_action (p : O) (hp : p ≠ 0) (q : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    cubeAverageMatrix p hp q • upperPoint (ringComplex (p ^ 3) * z) v hv =
      upperPoint (z + 3 * ringComplex q / ringComplex (p ^ 3)) (v / ‖ringComplex p‖ ^ 3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (ringComplex_ne_zero hp)) 3)) := by
  have h10 : cubeAverageMatrix p hp q 1 0 = 0 := by rw [cubeAverageMatrix_entries]; rfl
  have hz := cubeDilationRoot_ne_zero p hp
  rw [complexUpper_action _ h10]
  apply upperPoint_congr
  · simp only [cubeAverageMatrix_entries, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [← cubeDilationRoot_sq]
    field_simp
  · simp only [cubeAverageMatrix_entries, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, cubeDilationRoot_norm_sq]

/-- The cube eigenrelation transports Fourier frequency by `p^3` and height by `|p|^-3`. -/
theorem cubicSourceResidualFunction_fourier_cube (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (v : ℝ) (hv : 0 < v) :
    (∫ z in periodDomain, cubicSourceResidualFunction
      (upperPoint z (v / ‖ringComplex p‖ ^ 3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (ringComplex_ne_zero hp.ne_zero)) 3))) *
        tracePhase (-cuspFrequency (h * p ^ 3) * z)) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ *
        ∫ z in periodDomain, cubicSourceResidualFunction (upperPoint z v hv) * tracePhase (-cuspFrequency h * z) := by
  letI : Finite (CubeResidues p) := (Ideal.span {p ^ 3}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero 3 hp.ne_zero))
  letI : Fintype (CubeResidues p) := Fintype.ofFinite _
  let V := v / ‖ringComplex p‖ ^ 3
  have hV : 0 < V := div_pos hv (pow_pos (norm_pos_iff.mpr (ringComplex_ne_zero hp.ne_zero)) 3)
  let f := fun z : ℂ => cubicSourceResidualFunction (upperPoint z V hV)
  let g := fun z : ℂ => cubicSourceResidualFunction (upperPoint z v hv) * tracePhase (-cuspFrequency h * z)
  have hf : Continuous f := cubicSourceResidualFunction_continuous.comp
    (upperCoordinatesHomeomorph.continuous.comp
      (show Continuous (fun z : ℂ => (⟨(z, V), hV⟩ : UpperCoordinates)) by fun_prop))
  have hg : Continuous g := (cubicSourceResidualFunction_continuous.comp
    (upperCoordinatesHomeomorph.continuous.comp
      (show Continuous (fun z : ℂ => (⟨(z, v), hv⟩ : UpperCoordinates)) by fun_prop))).mul
      (cuspFourierCharacter_continuous h)
  have hper (n : O) (z : ℂ) : g (z + 3 * ringComplex n) = g z := by
    dsimp only [g]
    rw [cubicSourceResidualFunction_period, cuspFrequency_negative_period]
  let term (r : CubeResidues p) (z : ℂ) :=
    f (z + 3 * ringComplex (cubeResidueRepresentative p r) / ringComplex (p ^ 3)) *
      tracePhase (-cuspFrequency (h * p ^ 3) * z)
  have hi (r : CubeResidues p) : IntegrableOn (term r) periodDomain :=
    periodDomain_continuous_integrable _ ((hf.comp (continuous_id.add continuous_const)).mul
      (cuspFourierCharacter_continuous (h * p ^ 3)))
  have hterm (r : CubeResidues p) : (∫ z in periodDomain, term r z) =
      ∫ z in periodDomain, f z * tracePhase (-cuspFrequency (h * p ^ 3) * z) :=
    period_fourier_fractional_translation f (fun n z => cubicSourceResidualFunction_period V hV z n)
      (p ^ 3) (pow_ne_zero 3 hp.ne_zero) h (cubeResidueRepresentative p r)
  have hphase (z : ℂ) : tracePhase (-cuspFrequency h * (ringComplex (p ^ 3) * z)) =
      tracePhase (-cuspFrequency (h * p ^ 3) * z) := by rw [cuspFrequency_mul_right]; congr 1; ring
  have he (z : ℂ) : (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ ^ 3 * (∑ r : CubeResidues p, term r z) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ * g (ringComplex (p ^ 3) * z) := by
    have hh := congrArg (fun t : ℂ => t * tracePhase (-cuspFrequency (h * p ^ 3) * z))
      (cubicSourceResidualFunction_cube_eigenrelation p hp hprimary (upperPoint (ringComplex (p ^ 3) * z) v hv))
    simp only [cubeAverage, tsum_fintype, cubeAverageMatrix_scaled_action] at hh
    simpa only [term, f, g, hphase, Finset.sum_mul, mul_assoc] using hh
  have heint := congrArg (fun k : ℂ → ℂ => ∫ z in periodDomain, k z) (funext he)
  simp only [integral_const_mul] at heint
  rw [integral_finsetSum Finset.univ (fun r _ => hi r)] at heint
  simp_rw [hterm] at heint
  rw [period_integral_eisenstein_mul g hg.measurable hper (p ^ 3) (pow_ne_zero 3 hp.ne_zero)] at heint
  have hcard : (Fintype.card (CubeResidues p) : ℂ) = (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 := by
    rw [← Nat.card_eq_fintype_card]
    change (Ideal.absNorm (Ideal.span {p ^ 3}) : ℂ) = _
    rw [← Ideal.span_singleton_pow, map_pow, Nat.cast_pow]
  have hn := principalNorm_complex_ne_zero p hp.ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at heint
  have hfactor : (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ ^ 3 * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hn, one_pow]
  rw [← mul_assoc, hfactor, one_mul] at heint
  exact heint

/-- Removing a primary prime cube leaves the actual source arithmetic residue unchanged. -/
theorem rationalSourceScatteringResidue_mul_prime_cube (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) :
    rationalSourceScatteringResidue (h * p ^ 3) = rationalSourceScatteringResidue h := by
  by_cases hh : h = 0
  · subst h
    simp only [zero_mul]
  have hr : 0 < ‖ringComplex p‖ := norm_pos_iff.mpr (ringComplex_ne_zero hp.ne_zero)
  let V : ℝ := 1 / ‖ringComplex p‖ ^ 3
  have hV : 0 < V := div_pos zero_lt_one (pow_pos hr 3)
  have hfreq : ‖cuspFrequency (h * p ^ 3) * (V : ℂ)‖ = ‖cuspFrequency h‖ := by
    rw [cuspFrequency_mul_right, norm_mul, norm_mul, map_pow, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV]
    dsimp only [V]
    field_simp
  have hfreq0 : cuspFrequency (h * p ^ 3) * (V : ℂ) ≠ 0 := by
    intro he
    rw [he, norm_zero] at hfreq
    exact (norm_ne_zero_iff.mpr (cuspFrequency_ne_zero h hh)) hfreq.symm
  have hkernel : sourceFourierKernel (4 / 3) (cuspFrequency (h * p ^ 3) * (V : ℂ)) =
      sourceFourierKernel (4 / 3) (cuspFrequency h) := by
    rw [sourceFourierKernel_four_thirds _ hfreq0,
      sourceFourierKernel_four_thirds _ (cuspFrequency_ne_zero h hh), hfreq]
  have hK : sourceFourierKernel (4 / 3) (cuspFrequency h) ≠ 0 := by
    have hk : 0 < (sourceFourierKernel (4 / 3) (cuspFrequency h)).re := by
      convert sourceFourierKernel_real_re_pos (4 / 3) (by norm_num) (cuspFrequency h) using 1 <;> norm_num
    intro he
    rw [he, Complex.zero_re] at hk
    exact (lt_irrefl 0) hk
  have hheight : (V : ℂ) ^ (2 / 3 : ℂ) = (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ := by
    have he : V ^ (2 / 3 : ℝ) = (‖ringComplex p‖ ^ 3) ^ (-2 / 3 : ℝ) := by
      dsimp only [V]
      rw [one_div, Real.inv_rpow (pow_nonneg hr.le 3), ← Real.rpow_neg (pow_nonneg hr.le 3)]
      congr 1 <;> ring
    have hc : ((2 / 3 : ℝ) : ℂ) = (2 / 3 : ℂ) := by norm_num
    rw [← hc, ← Complex.ofReal_cpow hV.le, he]
    have hw := cubeCuspHeightWeight_zero p hp.ne_zero
    rw [cubeCuspHeightWeight, cubeCuspHeightDenominator_zero p hp.ne_zero] at hw
    exact hw
  have he := cubicSourceResidualFunction_fourier_cube p hp hprimary h 1 zero_lt_one
  rw [cubicSourceResidualFunction_fourier, cubicSourceResidualFunction_fourier] at he
  change ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * rationalSourceScatteringResidue (h * p ^ 3) *
      ((V : ℂ) ^ (2 / 3 : ℂ) * sourceFourierKernel (4 / 3) (cuspFrequency (h * p ^ 3) * (V : ℂ))) = _ at he
  rw [hheight, hkernel] at he
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one, one_mul] at he
  have hn := principalNorm_complex_ne_zero p hp.ne_zero
  have harea : ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero harea (inv_ne_zero hn)) hK)
  linear_combination he

/-- A square but no further prime factor annihilates the source residue. -/
theorem rationalSourceScatteringResidue_prime_square_zero (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    rationalSourceScatteringResidue (h * p ^ 2) = 0 := by
  have hc := rationalSourceScatteringResidue_mul_prime_cube p hp hprimary (h * p ^ 2)
  have he : (h * p ^ 2) * p ^ 3 = h * p ^ 5 := by rw [mul_assoc, ← pow_add]
  rw [he, rationalSourceScatteringResidue_square_cube p hp hprimary h hph] at hc
  have hn := principalNorm_complex_ne_zero p hp.ne_zero
  apply (mul_eq_zero.mp (show (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ *
    rationalSourceScatteringResidue (h * p ^ 2) = 0 by linear_combination hc)).resolve_left (inv_ne_zero hn)

/-- The surviving first-power residue is fixed by the actual cubic Gauss factor. -/
theorem rationalSourceScatteringResidue_prime_relation (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-(4 / 3 : ℂ)) * cubicUnitGaussSum (9 * h) p *
      rationalSourceScatteringResidue (h * p) =
        (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ * rationalSourceScatteringResidue h := by
  have he := rationalSourceScatteringResidue_prime_recurrence p hp hprimary h hph
  rw [rationalSourceScatteringResidue_mul_prime_cube p hp hprimary h] at he
  linear_combination he

lemma rationalSourceScatteringResidue_prime_pow_mod (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (n : ℕ) :
    rationalSourceScatteringResidue (h * p ^ n) = rationalSourceScatteringResidue (h * p ^ (n % 3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 3
    · rw [Nat.mod_eq_of_lt hn]
    have h3 : 3 ≤ n := by omega
    calc
      _ = rationalSourceScatteringResidue ((h * p ^ (n - 3)) * p ^ 3) := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h3]
      _ = rationalSourceScatteringResidue (h * p ^ (n - 3)) :=
        rationalSourceScatteringResidue_mul_prime_cube p hp hprimary _
      _ = rationalSourceScatteringResidue (h * p ^ ((n - 3) % 3)) := ih (n - 3) (by omega)
      _ = _ := by rw [show (n - 3) % 3 = n % 3 by omega]

/-- Cube removal extends to every primary element, without a coprimality restriction. -/
theorem rationalSourceScatteringResidue_mul_primary_cube (b : O) (hb : b ≠ 0)
    (hprimary : lambda ^ 2 ∣ b - 1) (h : O) :
    rationalSourceScatteringResidue (h * b ^ 3) = rationalSourceScatteringResidue h := by
  obtain ⟨s, hs, hpr⟩ := exists_primary_prime_factorization b hb hprimary
  rw [← hs]
  clear hs hb hprimary b
  induction s using Multiset.induction_on generalizing h with
  | empty => simp only [Multiset.prod_zero, one_pow, mul_one]
  | @cons p s ih =>
    obtain ⟨hp, hprimary⟩ := hpr p (Multiset.mem_cons_self _ _)
    rw [Multiset.prod_cons, mul_pow, ← mul_assoc,
      ih (h * p ^ 3) (fun q hq => hpr q (Multiset.mem_cons_of_mem hq)),
      rationalSourceScatteringResidue_mul_prime_cube p hp hprimary h]

/-- The first-power coefficient is the second cubic Gauss sum with its exact norm weight. -/
theorem rationalSourceScatteringResidue_prime_explicit (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    rationalSourceScatteringResidue (h * p) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-2 / 3 : ℂ) *
        primeCubicGauss p hp hprimary 2 (9 * h) * rationalSourceScatteringResidue h := by
  have hn := principalNorm_complex_ne_zero p hp.ne_zero
  have hgg := primeCubicGauss_one_mul_two p hp hprimary (9 * h)
    (primary_prime_not_dvd_nine_frequency p hp hprimary h hph)
  rw [primeCubicGauss_one_eq] at hgg
  have hG : cubicUnitGaussSum (9 * h) p ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hgg
    exact hn hgg.symm
  have hweight : (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-(4 / 3 : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hn)
  have hfactor : (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-(4 / 3 : ℂ)) *
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-2 / 3 : ℂ) * (Ideal.absNorm (Ideal.span {p}) : ℂ)) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ := by
    calc
      _ = (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-(4 / 3 : ℂ)) *
          ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-2 / 3 : ℂ) * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (1 : ℂ)) := by
        rw [Complex.cpow_one]
      _ = _ := by
        rw [← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
        convert Complex.cpow_neg_one (Ideal.absNorm (Ideal.span {p}) : ℂ) using 1
        congr 1
        norm_num
  apply mul_left_cancel₀ (mul_ne_zero hweight hG)
  calc
    _ = (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ * rationalSourceScatteringResidue h :=
      rationalSourceScatteringResidue_prime_relation p hp hprimary h hph
    _ = ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-(4 / 3 : ℂ)) *
        ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-2 / 3 : ℂ) *
          (cubicUnitGaussSum (9 * h) p * primeCubicGauss p hp hprimary 2 (9 * h)))) * rationalSourceScatteringResidue h := by
      rw [hgg, hfactor]
    _ = _ := by ring

/-- The full unramified prime-power table: only exponents zero and one modulo three survive. -/
theorem rationalSourceScatteringResidue_prime_power_table (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) (n : ℕ) :
    rationalSourceScatteringResidue (h * p ^ n) =
      if n % 3 = 0 then rationalSourceScatteringResidue h
      else if n % 3 = 1 then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-2 / 3 : ℂ) *
        primeCubicGauss p hp hprimary 2 (9 * h) * rationalSourceScatteringResidue h
      else 0 := by
  rw [rationalSourceScatteringResidue_prime_pow_mod p hp hprimary h n]
  by_cases h0 : n % 3 = 0
  · simp only [h0, pow_zero, mul_one, if_true]
  by_cases h1 : n % 3 = 1
  · simp only [h1, pow_one, if_true, Nat.one_ne_zero, if_false]
    exact rationalSourceScatteringResidue_prime_explicit p hp hprimary h hph
  have h2 : n % 3 = 2 := by omega
  rw [if_neg h0, if_neg h1, h2]
  exact rationalSourceScatteringResidue_prime_square_zero p hp hprimary h hph

lemma primeCubicGauss_two_eq_star (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (h : O) (hph : ¬ p ∣ h) :
    primeCubicGauss p hp hprimary 2 h = star (cubicUnitGaussSum h p) := by
  have hn := cubicUnitGaussSum_prime_norm p hp hprimary h hph
  have hG : cubicUnitGaussSum h p ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hn]
    exact norm_ne_zero_iff.mpr (ringComplex_ne_zero hp.ne_zero)
  have he := primeCubicGauss_one_mul_two p hp hprimary h hph
  rw [primeCubicGauss_one_eq] at he
  apply mul_left_cancel₀ hG
  rw [he, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn,
    ringComplex_norm_sq_eq_absNorm_span, Complex.ofReal_natCast]

lemma cubicSymbol_star_mul (a b : O) (hb : lambda ^ 2 ∣ b - 1) (hab : IsCoprime a b) :
    star (ringComplex (symbol a b)) * ringComplex (symbol a b) = 1 := by
  rw [mul_comm]
  simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, symbol_norm_one a b hb hab,
    one_pow, Complex.ofReal_one] using Complex.mul_conj (ringComplex (symbol a b))

lemma primeCubicGauss_two_twist (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (h : O) (hph : ¬ p ∣ h) :
    primeCubicGauss p hp hprimary 2 h = ringComplex (symbol h p) * primeCubicGauss p hp hprimary 2 1 := by
  have hc := hp.coprime_iff_not_dvd.mpr hph
  have hp1 : ¬ p ∣ (1 : O) := fun hd => hp.2.1 (isUnit_of_dvd_one hd)
  have he := cubicUnitGaussSum_frequency_twist 1 p h hp.ne_zero hc
  simp only [one_mul] at he
  have hs := congrArg star he
  simp only [star_mul] at hs
  rw [primeCubicGauss_two_eq_star p hp hprimary h hph, primeCubicGauss_two_eq_star p hp hprimary 1 hp1]
  calc
    _ = (star (ringComplex (symbol h p)) * ringComplex (symbol h p)) * star (cubicUnitGaussSum h p) := by
      rw [cubicSymbol_star_mul h p hprimary hc.symm, one_mul]
    _ = ringComplex (symbol h p) * (star (ringComplex (symbol h p)) * star (cubicUnitGaussSum h p)) := by ring
    _ = _ := by rw [mul_comm (star (ringComplex (symbol h p))), hs]

def sourceBesselNormalizer (h : O) : ℂ :=
  (2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) * (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ)

lemma sourceBesselNormalizer_mul (h p : O) :
    sourceBesselNormalizer (h * p) = (‖ringComplex p‖ : ℂ) ^ (1 / 3 : ℂ) * sourceBesselNormalizer h := by
  have hf : ‖cuspFrequency (h * p)‖ = ‖cuspFrequency h‖ * ‖ringComplex p‖ := by
    rw [cuspFrequency_mul_right, norm_mul]
  have he : (2 * Real.pi * ‖cuspFrequency (h * p)‖ : ℂ) =
      (‖ringComplex p‖ : ℂ) * ((2 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) := by
    rw [hf]
    push_cast
    ring
  unfold sourceBesselNormalizer
  rw [he, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (by positivity)]
  push_cast
  ring

lemma sourcePrimeNormalizer_powers (p : O) (hp : p ≠ 0) :
    (‖ringComplex p‖ : ℂ) ^ (1 / 3 : ℂ) * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-2 / 3 : ℂ) =
      (‖ringComplex p‖ : ℂ)⁻¹ := by
  have hr : (‖ringComplex p‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (ringComplex_ne_zero hp))
  rw [← Complex.ofReal_natCast, ← ringComplex_norm_sq_eq_absNorm_span, pow_two,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
    ← mul_assoc, ← Complex.cpow_add _ _ hr, ← Complex.cpow_add _ _ hr]
  convert Complex.cpow_neg_one (‖ringComplex p‖ : ℂ) using 1
  congr 1
  norm_num

/-- Fourier normalization converts the arithmetic prime factor to a unit-sized Gauss factor. -/
theorem rationalSourceResidualFourierCoefficient_prime_factor (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    rationalSourceResidualFourierCoefficient (h * p) =
      (primeCubicGauss p hp hprimary 2 (9 * h) / (‖ringComplex p‖ : ℂ)) * rationalSourceResidualFourierCoefficient h := by
  have hh : h ≠ 0 := fun hz => hph (hz ▸ dvd_zero p)
  rw [rationalSourceResidualFourierCoefficient_eq _ (mul_ne_zero hh hp.ne_zero),
    rationalSourceResidualFourierCoefficient_eq h hh]
  change rationalSourceScatteringResidue (h * p) * sourceBesselNormalizer (h * p) =
    (primeCubicGauss p hp hprimary 2 (9 * h) / (‖ringComplex p‖ : ℂ)) *
      (rationalSourceScatteringResidue h * sourceBesselNormalizer h)
  rw [rationalSourceScatteringResidue_prime_explicit p hp hprimary h hph, sourceBesselNormalizer_mul]
  calc
    _ = ((‖ringComplex p‖ : ℂ) ^ (1 / 3 : ℂ) * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-2 / 3 : ℂ)) *
        primeCubicGauss p hp hprimary 2 (9 * h) * (rationalSourceScatteringResidue h * sourceBesselNormalizer h) := by ring
    _ = _ := by rw [sourcePrimeNormalizer_powers p hp.ne_zero]; ring

def normalizedCubicUnitGauss (n : O) : ℂ := cubicUnitGaussSum 1 n / (‖ringComplex n‖ : ℂ)

lemma normalizedCubicUnitGauss_one : normalizedCubicUnitGauss 1 = 1 := by
  simp [normalizedCubicUnitGauss, cubicUnitGaussSum_one]

theorem rationalSourceResidualFourierCoefficient_prime_normalized (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    rationalSourceResidualFourierCoefficient (h * p) = ringComplex (symbol (9 * h) p) *
      star (normalizedCubicUnitGauss p) * rationalSourceResidualFourierCoefficient h := by
  have hp9 := primary_prime_not_dvd_nine_frequency p hp hprimary h hph
  have hp1 : ¬ p ∣ (1 : O) := fun hd => hp.2.1 (isUnit_of_dvd_one hd)
  rw [rationalSourceResidualFourierCoefficient_prime_factor p hp hprimary h hph,
    primeCubicGauss_two_twist p hp hprimary (9 * h) hp9, primeCubicGauss_two_eq_star p hp hprimary 1 hp1,
    normalizedCubicUnitGauss, star_div₀, Complex.star_def, Complex.conj_ofReal]
  ring

lemma normalizedCubicUnitGauss_coprime_product (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hap : lambda ^ 2 ∣ a - 1) (hbp : lambda ^ 2 ∣ b - 1) (hab : IsCoprime a b) :
    star (normalizedCubicUnitGauss (a * b)) = ringComplex (symbol a b) *
      star (normalizedCubicUnitGauss a) * star (normalizedCubicUnitGauss b) := by
  have hG := cubicUnitGaussSum_primary_product 1 a b ha hb hap hbp hab
  have ht := cubicUnitGaussSum_frequency_twist 1 b a hb hab.symm
  simp only [one_mul] at hG ht
  have hN : ringComplex (symbol a b) * normalizedCubicUnitGauss (a * b) =
      normalizedCubicUnitGauss a * normalizedCubicUnitGauss b := by
    unfold normalizedCubicUnitGauss
    rw [hG, map_mul, norm_mul, Complex.ofReal_mul]
    calc
      _ = cubicUnitGaussSum 1 a * (ringComplex (symbol a b) * cubicUnitGaussSum a b) /
          ((‖ringComplex a‖ : ℂ) * (‖ringComplex b‖ : ℂ)) := by ring
      _ = _ := by rw [ht]; ring
  have hs := congrArg star hN
  simp only [star_mul] at hs
  calc
    _ = (star (ringComplex (symbol a b)) * ringComplex (symbol a b)) * star (normalizedCubicUnitGauss (a * b)) := by
      rw [cubicSymbol_star_mul a b hbp hab, one_mul]
    _ = ringComplex (symbol a b) * (star (normalizedCubicUnitGauss (a * b)) * star (ringComplex (symbol a b))) := by ring
    _ = _ := by rw [hs]; ring

lemma primary_finset_product {ι : Type*} (s : Finset ι) (p : ι → O)
    (hp : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1) : lambda ^ 2 ∣ (∏ i ∈ s, p i) - 1 := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, sub_self, dvd_zero]
  | @insert i s hi ih =>
    have h1 := hp i (Finset.mem_insert_self _ _)
    have h2 := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi]
    convert dvd_add (h1.mul_right (∏ j ∈ s, p j)) h2 using 1 <;> ring

/-- Pairwise coprime primary primes recover the composite normalized Gauss coefficient. -/
theorem rationalSourceResidualFourierCoefficient_prime_product {ι : Type*}
    (s : Finset ι) (p : ι → O) (hp : ∀ i ∈ s, Prime (p i))
    (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (p i) (p j))
    (h : O) (hph : ∀ i ∈ s, ¬ p i ∣ h) :
    rationalSourceResidualFourierCoefficient (h * (∏ i ∈ s, p i)) =
      ringComplex (symbol (9 * h) (∏ i ∈ s, p i)) * star (normalizedCubicUnitGauss (∏ i ∈ s, p i)) *
        rationalSourceResidualFourierCoefficient h := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, mul_one, symbol_one, map_one, normalizedCubicUnitGauss_one, star_one, one_mul]
  | @insert i s hi ih =>
    have hpi := hp i (Finset.mem_insert_self _ _)
    have hpri := hprimary i (Finset.mem_insert_self _ _)
    have hps : ∀ j ∈ s, Prime (p j) := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    have hprs : ∀ j ∈ s, lambda ^ 2 ∣ p j - 1 := fun j hj => hprimary j (Finset.mem_insert_of_mem hj)
    have hcpi : IsCoprime (p i) (∏ j ∈ s, p j) := IsCoprime.prod_right (fun j hj =>
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro he; subst j; exact hi hj))
    have hbs : (∏ j ∈ s, p j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j hj => (hps j hj).ne_zero)
    have hpb : ¬ p i ∣ h * (∏ j ∈ s, p j) := by
      intro hd
      rcases hpi.dvd_mul.mp hd with hd | hd
      · exact hph i (Finset.mem_insert_self _ _) hd
      · exact hpi.2.1 (hcpi.isUnit_of_dvd hd)
    have hih := ih hps hprs
      (fun j hj k hk hjk => hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj => hph j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi, show h * (p i * (∏ j ∈ s, p j)) = (h * (∏ j ∈ s, p j)) * p i by ring,
      rationalSourceResidualFourierCoefficient_prime_normalized (p i) hpi hpri _ hpb, hih]
    rw [mul_comm (p i) (∏ j ∈ s, p j), normalizedCubicUnitGauss_coprime_product _ _ hbs hpi.ne_zero
      (primary_finset_product s p hprs) hpri hcpi.symm, symbol_mul_denominator, map_mul,
      show (9 : O) * (h * (∏ j ∈ s, p j)) = (9 * h) * (∏ j ∈ s, p j) by ring,
      symbol_mul_numerator, map_mul]
    ring

/-- The actual residual coefficient on a squarefree primary product has a single scalar normalization. -/
theorem rationalSourceResidualFourierCoefficient_primary_product {ι : Type*}
    (s : Finset ι) (p : ι → O) (hp : ∀ i ∈ s, Prime (p i))
    (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (p i) (p j)) :
    star (rationalSourceResidualFourierCoefficient (∏ i ∈ s, p i)) =
      star (rationalSourceResidualFourierCoefficient 1) *
        star (ringComplex (symbol 9 (∏ i ∈ s, p i))) * normalizedCubicUnitGauss (∏ i ∈ s, p i) := by
  have he := rationalSourceResidualFourierCoefficient_prime_product s p hp hprimary hpair 1
    (fun i hi hd => (hp i hi).2.1 (isUnit_of_dvd_one hd))
  simp only [one_mul, mul_one] at he
  rw [he, star_mul, star_mul, star_star]
  ring

lemma sourceBesselNormalizer_mul_cube (h b : O) (hb : b ≠ 0) :
    sourceBesselNormalizer (h * b ^ 3) = (‖ringComplex b‖ : ℂ) * sourceBesselNormalizer h := by
  have hr : 0 < ‖ringComplex b‖ := norm_pos_iff.mpr (ringComplex_ne_zero hb)
  have hc : (((‖ringComplex b‖ ^ 3 : ℝ) : ℂ) ^ (1 / 3 : ℂ)) = (‖ringComplex b‖ : ℂ) := by
    have he : ((1 / 3 : ℝ) : ℂ) = (1 / 3 : ℂ) := by norm_num
    rw [← he, ← Complex.ofReal_cpow (pow_nonneg hr.le 3), ← Real.rpow_natCast_mul hr.le 3, Nat.cast_ofNat,
      show (3 : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one]
  rw [sourceBesselNormalizer_mul, map_pow, norm_pow, hc]

theorem rationalSourceResidualFourierCoefficient_primary_cube (b : O) (hb : b ≠ 0)
    (hprimary : lambda ^ 2 ∣ b - 1) (h : O) (hh : h ≠ 0) :
    rationalSourceResidualFourierCoefficient (h * b ^ 3) =
      (‖ringComplex b‖ : ℂ) * rationalSourceResidualFourierCoefficient h := by
  rw [rationalSourceResidualFourierCoefficient_eq _ (mul_ne_zero hh (pow_ne_zero 3 hb)),
    rationalSourceResidualFourierCoefficient_eq h hh]
  change rationalSourceScatteringResidue (h * b ^ 3) * sourceBesselNormalizer (h * b ^ 3) =
    (‖ringComplex b‖ : ℂ) * (rationalSourceScatteringResidue h * sourceBesselNormalizer h)
  rw [rationalSourceScatteringResidue_mul_primary_cube b hb hprimary h, sourceBesselNormalizer_mul_cube h b hb]
  ring

lemma primaryIdealGenerator_squarefree_support (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0)
    (hsq : Squarefree I) : primaryIdealGenerator I = ∏ P ∈ primeSupport I, primaryIdealPrime P := by
  have hI0 := primaryIdealGenerator_ne_zero_ideal I hI
  have hn := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  have hv : (primeSupport I).val = UniqueFactorizationMonoid.normalizedFactors I := by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  rw [primaryIdealGenerator, if_neg hI0]
  change _ = ((primeSupport I).val.map primaryIdealPrime).prod
  rw [hv]

lemma primaryIdealPrime_isPrime_of_mem (I P : Ideal O) (hI : primaryIdealGenerator I ≠ 0)
    (hP : P ∈ primeSupport I) : Prime (primaryIdealPrime P) := by
  have hp0 := primaryIdealPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP)
  have hs := primaryIdealPrime_spec P hp0
  letI : P.IsMaximal := hs.1
  apply (Ideal.span_singleton_prime hp0).mp
  rw [hs.2.2.1]
  infer_instance

lemma primaryIdealPrime_support_coprime (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0)
    (P : Ideal O) (hP : P ∈ primeSupport I) (Q : Ideal O) (hQ : Q ∈ primeSupport I) (hne : P ≠ Q) :
    IsCoprime (primaryIdealPrime P) (primaryIdealPrime Q) := by
  have hp := primaryIdealPrime_spec P (primaryIdealPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))
  have hq := primaryIdealPrime_spec Q (primaryIdealPrime_factor_ne_zero I Q hI (Multiset.mem_toFinset.mp hQ))
  letI : P.IsMaximal := hp.1
  letI : Q.IsMaximal := hq.1
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [hp.2.2.1, hq.2.2.1]
  exact Ideal.isCoprime_of_isMaximal hne

/-- The scalar shared by all unramified squarefree Fourier coefficients. -/
def rationalSourceThetaScalar : ℂ := star (rationalSourceResidualFourierCoefficient 1)

theorem rationalSourceResidualFourierCoefficient_squarefree (I : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hsq : Squarefree I) :
    star (rationalSourceResidualFourierCoefficient (primaryIdealGenerator I)) =
      rationalSourceThetaScalar * star (ringComplex (symbol 9 (primaryIdealGenerator I))) *
        normalizedCubicUnitGauss (primaryIdealGenerator I) := by
  have he := rationalSourceResidualFourierCoefficient_primary_product (primeSupport I) primaryIdealPrime
    (fun P hP => primaryIdealPrime_isPrime_of_mem I P hI hP)
    (fun P hP => (primaryIdealPrime_spec P
      (primaryIdealPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2)
    (primaryIdealPrime_support_coprime I hI)
  rwa [← primaryIdealGenerator_squarefree_support I hI hsq] at he

/-- Cube multiplication changes only the absolute-value factor in the theta coefficient. -/
theorem rationalSourceResidualFourierCoefficient_squarefree_cube (I J : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0) (hsq : Squarefree I) :
    star (rationalSourceResidualFourierCoefficient (primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3)) =
      rationalSourceThetaScalar * (‖ringComplex (primaryIdealGenerator J)‖ : ℂ) *
        star (ringComplex (symbol 9 (primaryIdealGenerator I))) * normalizedCubicUnitGauss (primaryIdealGenerator I) := by
  rw [rationalSourceResidualFourierCoefficient_primary_cube _ hJ (primaryIdealGenerator_spec J hJ).2 _ hI,
    star_mul, rationalSourceResidualFourierCoefficient_squarefree I hI hsq]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

open UniqueFactorizationMonoid

/-- A nonzero unramified residue has no prime valuation congruent to two modulo three. -/
theorem rationalSourceScatteringResidue_valuation_ne_two (I P : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hP : P ∈ normalizedFactors I)
    (hR : rationalSourceScatteringResidue (primaryIdealGenerator I) ≠ 0) :
    (normalizedFactors I).count P % 3 ≠ 2 := by
  have hI0 := primaryIdealGenerator_ne_zero_ideal I hI
  have hprime := prime_of_normalized_factor P hP
  let p := primaryIdealPrime P
  have hp0 : p ≠ 0 := primaryIdealPrime_factor_ne_zero I P hI hP
  have hps := primaryIdealPrime_spec P hp0
  have hp : Prime p := primaryIdealPrime_isPrime_of_mem I P hI (Multiset.mem_toFinset.mpr hP)
  obtain ⟨J, hJ, hnot⟩ := (FiniteMultiplicity.of_prime_left hprime hI0).exists_eq_pow_mul_and_not_dvd
  have hgen : primaryIdealGenerator I = p ^ (multiplicity P I) * primaryIdealGenerator J := by
    calc
      _ = primaryIdealGenerator (P ^ (multiplicity P I) * J) := congrArg primaryIdealGenerator hJ
      _ = _ := by
        rw [primaryIdealGenerator_mul, primaryIdealGenerator_pow]
        have hPgen : primaryIdealGenerator P = p := by
          rw [← hps.2.2.1, primaryIdealGenerator_span p hp0 hps.2.2.2]
        rw [hPgen]
  have hgJ : primaryIdealGenerator J ≠ 0 := by
    intro hz
    exact hI (by rw [hgen, hz, mul_zero])
  have hpd : ¬ p ∣ primaryIdealGenerator J := by
    intro hd
    apply hnot
    rw [Ideal.dvd_iff_le, ← hps.2.2.1, ← (primaryIdealGenerator_spec J hgJ).1,
      Ideal.span_singleton_le_span_singleton]
    exact hd
  have hcount := multiplicity_eq_count_normalizedFactors hprime.irreducible hI0
  rw [normalize_normalized_factor P hP] at hcount
  intro hc
  have hm : (multiplicity P I) % 3 = 2 := by rwa [hcount]
  apply hR
  rw [hgen, mul_comm, rationalSourceScatteringResidue_prime_power_table p hp hps.2.2.2 _ hpd, hm]
  norm_num

/-- The squarefree factor selected by prime valuations congruent to one modulo three. -/
def thetaSquarefreePart (I : Ideal O) : Ideal O :=
  ∏ P ∈ (primeSupport I).filter (fun P => (normalizedFactors I).count P % 3 = 1), P

/-- The cube root of the maximal cubical ideal factor. -/
def thetaCubePart (I : Ideal O) : Ideal O :=
  ∏ P ∈ primeSupport I, P ^ ((normalizedFactors I).count P / 3)

lemma thetaSquarefreePart_squarefree (I : Ideal O) : Squarefree (thetaSquarefreePart I) :=
  squarefree_support_product (Finset.filter_subset _ _)

lemma thetaParts_mul_cube (I : Ideal O) (hI : I ≠ 0)
    (he : ∀ P ∈ normalizedFactors I, (normalizedFactors I).count P % 3 ≠ 2) :
    thetaSquarefreePart I * thetaCubePart I ^ 3 = I := by
  rw [thetaSquarefreePart, Finset.prod_filter, thetaCubePart, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  calc
    _ = ∏ P ∈ primeSupport I, P ^ ((normalizedFactors I).count P) := by
      apply Finset.prod_congr rfl
      intro P hP
      have hp := he P (Multiset.mem_toFinset.mp hP)
      have hm : (normalizedFactors I).count P % 3 = 0 ∨ (normalizedFactors I).count P % 3 = 1 := by omega
      rcases hm with hm | hm
      · rw [if_neg (by omega), one_mul, ← pow_mul]
        congr 1
        omega
      · rw [if_pos hm, ← pow_mul, ← pow_succ']
        congr 1
        omega
    _ = (normalizedFactors I).prod := (Finset.prod_multiset_count (normalizedFactors I)).symm
    _ = I := Ideal.prod_normalizedFactors_eq_self hI

/-- Every nonzero unramified arithmetic residue lies on squarefree times cube support. -/
theorem rationalSourceScatteringResidue_squarefree_cube_support (I : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hR : rationalSourceScatteringResidue (primaryIdealGenerator I) ≠ 0) :
    Squarefree (thetaSquarefreePart I) ∧ primaryIdealGenerator (thetaSquarefreePart I) ≠ 0 ∧
      primaryIdealGenerator (thetaCubePart I) ≠ 0 ∧ thetaSquarefreePart I * thetaCubePart I ^ 3 = I := by
  have he := thetaParts_mul_cube I (primaryIdealGenerator_ne_zero_ideal I hI)
    (fun P hP => rationalSourceScatteringResidue_valuation_ne_two I P hI hP hR)
  have hgen : primaryIdealGenerator I =
      primaryIdealGenerator (thetaSquarefreePart I) * (primaryIdealGenerator (thetaCubePart I)) ^ 3 := by
    calc
      _ = primaryIdealGenerator (thetaSquarefreePart I * thetaCubePart I ^ 3) := congrArg primaryIdealGenerator he.symm
      _ = _ := by rw [primaryIdealGenerator_mul, primaryIdealGenerator_pow]
  have hA : primaryIdealGenerator (thetaSquarefreePart I) ≠ 0 := by
    intro hz
    exact hI (by rw [hgen, hz, zero_mul])
  have hB : primaryIdealGenerator (thetaCubePart I) ≠ 0 := by
    intro hz
    exact hI (by rw [hgen, hz, zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero])
  exact ⟨thetaSquarefreePart_squarefree I, hA, hB, he⟩

theorem rationalSourceFourier_squarefree_cube_support (I : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hT : rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ≠ 0) :
    ∃ A B : Ideal O, Squarefree A ∧ primaryIdealGenerator A ≠ 0 ∧ primaryIdealGenerator B ≠ 0 ∧ A * B ^ 3 = I := by
  have hR : rationalSourceScatteringResidue (primaryIdealGenerator I) ≠ 0 := by
    intro hz
    exact hT (by rw [rationalSourceResidualFourierCoefficient_eq _ hI, hz, zero_mul])
  exact ⟨thetaSquarefreePart I, thetaCubePart I, rationalSourceScatteringResidue_squarefree_cube_support I hI hR⟩

theorem rationalSourceFourier_primary_zero_of_base_zero (hC : rationalSourceThetaScalar = 0)
    (n : O) (hprimary : lambda ^ 2 ∣ n - 1) : rationalSourceResidualFourierCoefficient n = 0 := by
  have hn : n ≠ 0 := primary_ne_zero n hprimary
  let I : Ideal O := Ideal.span {n}
  have hgen : primaryIdealGenerator I = n := primaryIdealGenerator_span n hn hprimary
  have hI : primaryIdealGenerator I ≠ 0 := by rwa [hgen]
  by_contra hT
  have hTI : rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ≠ 0 := by rwa [hgen]
  obtain ⟨A, B, hA, hAg, hBg, hAB⟩ := rationalSourceFourier_squarefree_cube_support I hI hTI
  have harg : primaryIdealGenerator A * (primaryIdealGenerator B) ^ 3 = n := by
    have he := congrArg primaryIdealGenerator hAB
    simpa only [primaryIdealGenerator_mul, primaryIdealGenerator_pow, hgen] using he
  have he := rationalSourceResidualFourierCoefficient_squarefree_cube A B hAg hBg hA
  rw [harg, hC, zero_mul, zero_mul, zero_mul] at he
  exact hT (star_eq_zero.mp he)

lemma cubicUnitGaussSum_neg_frequency (h c : O) (hc : c ≠ 0) (hprimary : lambda ^ 2 ∣ c - 1) :
    cubicUnitGaussSum (-h) c = cubicUnitGaussSum h c := by
  have he := cubicUnitGaussSum_frequency_twist h c (-1) hc ⟨0, -1, by ring⟩
  simpa only [symbol_neg_one c hprimary, map_one, one_mul, mul_neg_one] using he

lemma unramifiedCubicGaussSeries_neg (s : ℂ) (h : O) :
    unramifiedCubicGaussSeries s (-h) = unramifiedCubicGaussSeries s h := by
  apply tsum_congr
  intro I
  rw [cubicUnitGaussSum_neg_frequency h _ I.2 (primaryIdealGenerator_spec I.1 I.2).2]

lemma unramifiedGaussResidue_neg (h : O) : unramifiedGaussResidue (-h) = unramifiedGaussResidue h := by
  have he := unramifiedGaussResidue_of_initial_relation (-h) h 0 (fun _ => 1) (fun _ => 0)
    (fun _ _ => analyticAt_const) (fun _ _ => analyticAt_const) continuousAt_const continuousAt_const
    (fun s _ _ => by simpa only [one_mul, zero_mul, add_zero] using unramifiedCubicGaussSeries_neg s h)
  simpa only [one_mul, zero_mul, add_zero] using he

lemma ramifiedFrequencyChar_neg_unit (k : O) (u : Oˣ) (n : ℕ) :
    ramifiedFrequencyChar k (-u) n = ramifiedFrequencyChar k u n := by
  ext x
  rw [ramifiedFrequencyChar_rep, ramifiedFrequencyChar_rep]
  simp only [Units.val_neg, neg_mul]
  rw [symbol_neg_numerator _ _ (lambda_sq_dvd_three.trans ⟨_, by ring⟩)]

lemma arithmeticResidueSum_neg_unit (h : O) (u : Oˣ) (n : ℕ) (hn : 2 ≤ n) :
    arithmeticResidueSum (-h) ((u : O) * lambda ^ n) =
      arithmeticResidueSum h (((-u : Oˣ) : O) * lambda ^ n) := by
  by_cases hd : (u : O) * lambda ^ n ∣ 3 * (-h)
  · obtain ⟨k, hk⟩ := hd
    have hk' : 3 * h = (((-u : Oˣ) : O) * lambda ^ n) * k := by
      simp only [Units.val_neg]
      linear_combination -hk
    rw [ramified_arithmetic_character_test (-h) k u n hn hk,
      ramified_arithmetic_character_test h k (-u) n hn hk', ramifiedFrequencyChar_neg_unit]
  · have hl : arithmeticResidueSum (-h) ((u : O) * lambda ^ n) = 0 := by
      by_contra he
      exact hd (ramified_arithmetic_support (-h) u n hn he)
    have hr : arithmeticResidueSum h (((-u : Oˣ) : O) * lambda ^ n) = 0 := by
      by_contra he
      obtain ⟨k, hk⟩ := ramified_arithmetic_support h (-u) n hn he
      apply hd
      refine ⟨k, ?_⟩
      simp only [Units.val_neg] at hk
      linear_combination -hk
    rw [hl, hr]

/-- Negating the frequency is absorbed by negating the ramified unit. -/
lemma arithmeticDirichletSeries_neg (s : ℂ) (hs : 2 < s.re) (h : O) (hh : h ≠ 0) :
    arithmeticDirichletSeries s (-h) = arithmeticDirichletSeries s h := by
  let N := max (ramifiedFrequencyBound (-h) + 1) (ramifiedFrequencyBound h + 1)
  rw [arithmeticDirichletSeries_finite_gauss_of_bound s hs (-h) (neg_ne_zero.mpr hh) N (le_max_left _ _),
    arithmeticDirichletSeries_finite_gauss_of_bound s hs h hh N (le_max_right _ _)]
  have he (u : Oˣ) (n : ℕ) : ramifiedGaussTerm s (-h) u n = ramifiedGaussTerm s h (-u) n := by
    unfold ramifiedGaussTerm
    rw [arithmeticResidueSum_neg_unit h u (n + 2) (by omega)]
    congr 2
    simp only [Units.val_neg]
    ring
  change (∑' u : Oˣ, ∑ n ∈ Finset.range N, ramifiedGaussTerm s (-h) u n) =
    ∑' u : Oˣ, ∑ n ∈ Finset.range N, ramifiedGaussTerm s h u n
  simp_rw [he]
  exact (Equiv.neg Oˣ).tsum_eq (fun u : Oˣ => ∑ n ∈ Finset.range N, ramifiedGaussTerm s h u n)

lemma nonzeroScatteringResidue_neg (h : O) (hh : h ≠ 0) :
    nonzeroScatteringResidue (-h) = nonzeroScatteringResidue h := by
  have he := nonzeroScatteringResidue_of_initial_relation (-h) h h (neg_ne_zero.mpr hh) hh hh
    (fun _ => 1) (fun _ => 0) (fun _ _ => analyticAt_const) (fun _ _ => analyticAt_const)
    continuousAt_const continuousAt_const (fun s hs _ => by
      simp only [one_mul, zero_mul, add_zero, scatteringCoefficient,
        arithmeticDirichletSeries_neg s (by linarith) h hh])
  simpa only [one_mul, zero_mul, add_zero] using he

lemma cuspFrequency_neg (h : O) : cuspFrequency (-h) = -cuspFrequency h := by
  simp only [cuspFrequency, map_neg, neg_div]

lemma rationalCuspPhaseSum_neg (h : O) : rationalCuspPhaseSum (-h) = rationalCuspPhaseSum h := by
  have h3 : tracePhase (3 * cuspFrequency h) = 1 := by
    simpa only [map_one, mul_one, one_mul, mul_comm] using cuspFrequency_period h 1
  have h1 : tracePhase (-cuspFrequency h) = tracePhase (cuspFrequency h * 2) := by
    have he := AddChar.map_add_eq_mul tracePhase (-cuspFrequency h) (3 * cuspFrequency h)
    rw [h3, mul_one] at he
    convert he.symm using 1 <;> congr 1 <;> ring
  have h2 : tracePhase (-cuspFrequency h * 2) = tracePhase (cuspFrequency h) := by
    have he := AddChar.map_add_eq_mul tracePhase (-cuspFrequency h * 2) (3 * cuspFrequency h)
    rw [h3, mul_one] at he
    convert he.symm using 1 <;> congr 1 <;> ring
  rw [rationalCuspPhaseSum, rationalCuspPhaseSum, cuspFrequency_neg, h1, h2]
  ring

lemma rationalSourceScatteringResidue_neg (h : O) :
    rationalSourceScatteringResidue (-h) = rationalSourceScatteringResidue h := by
  by_cases hh : h = 0
  · simp only [hh, neg_zero]
  rw [rationalSourceScatteringResidue, rationalSourceScatteringResidue, if_neg hh, if_neg (neg_ne_zero.mpr hh),
    nonzeroScatteringResidue_neg h hh, rationalCuspPhaseSum_neg,
    oppositeCuspResidue_eq_unramified, oppositeCuspResidue_eq_unramified,
    mul_neg, unramifiedGaussResidue_neg]

theorem rationalSourceResidualFourierCoefficient_neg (h : O) :
    rationalSourceResidualFourierCoefficient (-h) = rationalSourceResidualFourierCoefficient h := by
  by_cases hh : h = 0
  · simp only [hh, neg_zero]
  rw [rationalSourceResidualFourierCoefficient_eq _ (neg_ne_zero.mpr hh),
    rationalSourceResidualFourierCoefficient_eq h hh, rationalSourceScatteringResidue_neg,
    cuspFrequency_neg, norm_neg]

/-- Full Eisenstein translation symmetry conflicts with the lower cusp's nontrivial cubic character. -/
theorem cubicSource_not_eisenstein_periodic :
    ¬ (∀ a : O, ∀ w : HyperbolicSpace,
      cubicSourceResidualFunction (complexTranslation (ringComplex a) • w) = cubicSourceResidualFunction w) := by
  intro hperiod
  have hfactor : integralComplexMatrix (lowerCuspMatrix omega) =
      integralComplexMatrix (rationalEmbedding ModularGroup.S) * complexTranslation (-ringComplex omega) *
        integralComplexMatrix (rationalEmbedding ModularGroup.S⁻¹) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerCuspMatrix, integralComplexMatrix, rationalEmbedding, complexTranslation,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S,
        Matrix.adjugate_fin_two]
  have hlow (w : HyperbolicSpace) : ramifiedSourceFunction omega w = cubicSourceResidualFunction w := by
    unfold ramifiedSourceFunction
    rw [hfactor, mul_smul, mul_smul, cubicSourceResidualFunction_rational]
    have hm := hperiod (-omega) (integralComplexMatrix (rationalEmbedding ModularGroup.S⁻¹) • w)
    simp only [map_neg] at hm
    rw [hm, cubicSourceResidualFunction_rational]
  have hchar : complexCharacter (ramifiedParabolic omega 1) = ringComplex omega := by
    have he := ramifiedParabolic_omega_character 1 0
    simpa [Coordinates.eval, cubicExp] using he
  apply cubicSourceResidualFunction_ne_zero
  funext w
  obtain ⟨z, v, hv, rfl⟩ := upperPoint_surjective w
  have he := ramifiedSourceFunction_period omega 1 z v hv
  have hp := cubicSourceResidualFunction_period v hv z 1
  simp only [map_one] at hp
  rw [← ramifiedParabolic_character, hchar, hlow, hlow, map_one,
    hp] at he
  have hz : (ringComplex omega - 1) * cubicSourceResidualFunction (upperPoint z v hv) = 0 := by
    linear_combination -he
  have hn : ringComplex omega - 1 ≠ 0 := sub_ne_zero.mpr (by
    intro h
    exact omega_primitive.ne_one (by decide) (ringComplex_injective (by simpa only [map_one] using h)))
  exact (mul_eq_zero.mp hz).resolve_left hn

lemma source_period_of_three_supported
    (hs : ∀ h : O, ¬ (3 : O) ∣ h → rationalSourceResidualFourierCoefficient h = 0)
    (a : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    cubicSourceResidualFunction (upperPoint (z + ringComplex a) v hv) =
      cubicSourceResidualFunction (upperPoint z v hv) := by
  rw [cubicSourceResidualFunction_fourier_expansion, cubicSourceResidualFunction_fourier_expansion]
  apply tsum_congr
  intro h
  by_cases hd : (3 : O) ∣ h
  · obtain ⟨b, rfl⟩ := hd
    have hp : tracePhase (cuspFrequency (3 * b) * ringComplex a) = 1 := by
      have he : cuspFrequency (3 * b) * ringComplex a = cuspFrequency b * (3 * ringComplex a) := by
        simp only [cuspFrequency, map_mul, map_ofNat]
        ring
      rw [he, cuspFrequency_period]
    rw [mul_add, AddChar.map_add_eq_mul, hp, mul_one]
  · have hh : h ≠ 0 := fun he => hd (he ▸ dvd_zero 3)
    rw [rationalSourceModeAmplitude_bessel v hv h hh, hs h hd, zero_mul, zero_mul, zero_mul, zero_mul]

theorem exists_source_coefficient_not_three :
    ∃ h : O, ¬ (3 : O) ∣ h ∧ rationalSourceResidualFourierCoefficient h ≠ 0 := by
  by_contra hn
  have hs : ∀ h : O, ¬ (3 : O) ∣ h → rationalSourceResidualFourierCoefficient h = 0 := by
    intro h hh
    by_contra he
    exact hn ⟨h, hh, he⟩
  apply cubicSource_not_eisenstein_periodic
  intro a w
  obtain ⟨z, v, hv, rfl⟩ := upperPoint_surjective w
  rw [complexTranslation_action]
  exact source_period_of_three_supported hs a z v hv

lemma sourceFourier_phase_of_ne_zero (h : O) (hh : h ≠ 0)
    (hT : rationalSourceResidualFourierCoefficient h ≠ 0) : tracePhase (cuspFrequency h) = 1 := by
  have hR : rationalSourceScatteringResidue h ≠ 0 := by
    intro hz
    exact hT (by rw [rationalSourceResidualFourierCoefficient_eq h hh, hz, zero_mul])
  have hK : sourceFourierKernel (4 / 3) (cuspFrequency h) ≠ 0 := by
    have hk : 0 < (sourceFourierKernel (4 / 3) (cuspFrequency h)).re := by
      convert sourceFourierKernel_real_re_pos (4 / 3) (by norm_num) (cuspFrequency h) using 1 <;> norm_num
    intro he
    rw [he, Complex.zero_re] at hk
    exact (lt_irrefl 0) hk
  have hs (z : ℂ) : cubicSourceResidualFunction (upperPoint (z + 1) 1 (by norm_num)) =
      cubicSourceResidualFunction (upperPoint z 1 (by norm_num)) := by
    have he := cubicSourceResidualFunction_period_one_action (upperPoint z 1 (by norm_num))
    rwa [complexTranslation_action] at he
  have he := period_fourier_translation
    (fun z => cubicSourceResidualFunction (upperPoint z 1 (by norm_num)))
    (fun n z => cubicSourceResidualFunction_period 1 (by norm_num) z n) h 1
  simp only [hs, mul_one] at he
  rw [cubicSourceResidualFunction_fourier 1 (by norm_num) h] at he
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one, one_mul] at he
  exact mul_right_cancel₀ (mul_ne_zero (mul_ne_zero cusp_volume_ne_zero hR) hK)
    (he.symm.trans (one_mul _).symm)

lemma sourceRayPhase_coordinate (h : O) (hphase : tracePhase (cuspFrequency h) = 1) :
    (3 : ℤ) ∣ (Coordinates.coords h).2 := by
  have he := complexTrace_div_traceLambda (Coordinates.coords h).1 (Coordinates.coords h).2
  rw [Coordinates.eval_coords] at he
  have ht : cuspFrequency h + starRingEnd ℂ (cuspFrequency h) = ((Coordinates.coords h).2 : ℂ) / 3 := by
    rw [cuspFrequency, show ringComplex h / (3 * ringComplex traceLambda) =
      (ringComplex h / ringComplex traceLambda) / 3 by ring, map_div₀, map_ofNat, ← add_div, he]
  change Complex.exp (2 * Real.pi * Complex.I * (cuspFrequency h + starRingEnd ℂ (cuspFrequency h))) = 1 at hphase
  rw [ht] at hphase
  have hp : Complex.exp (2 * Real.pi * Complex.I * ((((Coordinates.coords h).2 : ℝ) / 3 : ℝ) : ℂ)) = 1 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat] using hphase
  obtain ⟨n, hn⟩ := exp_two_pi_real_eq_one (((Coordinates.coords h).2 : ℝ) / 3) hp
  refine ⟨n, ?_⟩
  have hc : ((Coordinates.coords h).2 : ℝ) = 3 * (n : ℝ) := by linarith only [hn]
  exact_mod_cast hc

lemma primary_or_negative_primary_of_source_mask (h : O) (h3 : ¬ (3 : O) ∣ h)
    (hphase : tracePhase (cuspFrequency h) = 1) : lambda ^ 2 ∣ h - 1 ∨ lambda ^ 2 ∣ -h - 1 := by
  let a : ℤ := (Coordinates.coords h).1
  let b : ℤ := (Coordinates.coords h).2
  have heval : h = (a : O) + (b : O) * omega := (Coordinates.eval_coords h).symm
  obtain ⟨B, hB⟩ := sourceRayPhase_coordinate h hphase
  have hBc : (b : O) = 3 * (B : O) := by exact_mod_cast hB
  have ha : ¬ (3 : ℤ) ∣ a := by
    rintro ⟨A, hA⟩
    apply h3
    refine ⟨(A : O) + (B : O) * omega, ?_⟩
    have hAc : (a : O) = 3 * (A : O) := by exact_mod_cast hA
    rw [heval, hAc, hBc]
    ring
  have hcases : (3 : ℤ) ∣ a - 1 ∨ (3 : ℤ) ∣ a + 1 := by omega
  rcases hcases with ⟨A, hA⟩ | ⟨A, hA⟩
  · left
    apply lambda_sq_dvd_three.trans
    refine ⟨(A : O) + (B : O) * omega, ?_⟩
    have hAc : (a : O) - 1 = 3 * (A : O) := by exact_mod_cast hA
    rw [heval, hBc]
    linear_combination hAc
  · right
    apply lambda_sq_dvd_three.trans
    refine ⟨-((A : O) + (B : O) * omega), ?_⟩
    have hAc : (a : O) + 1 = 3 * (A : O) := by exact_mod_cast hA
    rw [heval, hBc]
    linear_combination -hAc

/-- The base Fourier coefficient is nonzero: otherwise the entire source gains a forbidden period. -/
theorem rationalSourceThetaScalar_ne_zero : rationalSourceThetaScalar ≠ 0 := by
  intro hC
  obtain ⟨h, h3, hT⟩ := exists_source_coefficient_not_three
  have hh : h ≠ 0 := fun he => h3 (he ▸ dvd_zero 3)
  rcases primary_or_negative_primary_of_source_mask h h3 (sourceFourier_phase_of_ne_zero h hh hT) with hp | hp
  · exact hT (rationalSourceFourier_primary_zero_of_base_zero hC h hp)
  · exact hT ((rationalSourceResidualFourierCoefficient_neg h).symm.trans
      (rationalSourceFourier_primary_zero_of_base_zero hC (-h) hp))

/-- The frequency-nine twist is the cubic symbol of the different. -/
lemma symbol_nine_eq_traceLambda (n : O) (hn : lambda ^ 2 ∣ n - 1) :
    symbol 9 n = symbol traceLambda n := by
  have hs : traceLambda ^ 2 = (-3 : O) := by
    unfold traceLambda
    linear_combination 4 * cusp_omega_relation
  have hc3 : IsCoprime (3 : O) n := by
    simpa only [Units.val_one, pow_zero, mul_one] using ramified_primary_coprime (1 : Oˣ) 0 n hn
  have hc : IsCoprime traceLambda n := by
    have he : traceLambda * (-traceLambda) = (3 : O) := by linear_combination -hs
    rw [← he] at hc3
    exact hc3.of_mul_left_left
  have h9 : (9 : O) = traceLambda ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hs]
    norm_num
  rw [h9, symbol_pow_numerator _ _ hn 4, show (4 : ℕ) = 3 + 1 by decide, pow_add,
    symbol_cube_of_isCoprime _ _ hn hc, pow_one, one_mul]

/-- The normalized residual theta coefficient has the exact different-symbol phase. -/
theorem normalized_sourceFourier_squarefree_cube (I J : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0) (hsq : Squarefree I) :
    rationalSourceThetaScalar⁻¹ *
      star (rationalSourceResidualFourierCoefficient (primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3)) =
        (‖ringComplex (primaryIdealGenerator J)‖ : ℂ) *
          star (ringComplex (symbol traceLambda (primaryIdealGenerator I))) * normalizedCubicUnitGauss (primaryIdealGenerator I) := by
  rw [rationalSourceResidualFourierCoefficient_squarefree_cube I J hI hJ hsq,
    symbol_nine_eq_traceLambda _ (primaryIdealGenerator_spec I hI).2]
  simp only [← mul_assoc, inv_mul_cancel₀ rationalSourceThetaScalar_ne_zero, one_mul]

lemma normalizedCubicUnitGauss_prime_norm (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) :
    ‖normalizedCubicUnitGauss p‖ = 1 := by
  have hp1 : ¬ p ∣ (1 : O) := fun hd => hp.2.1 (isUnit_of_dvd_one hd)
  rw [normalizedCubicUnitGauss, norm_div, cubicUnitGaussSum_prime_norm p hp hprimary 1 hp1,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (ringComplex_ne_zero hp.ne_zero))]

lemma normalizedCubicUnitGauss_coprime_norm (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hap : lambda ^ 2 ∣ a - 1) (hbp : lambda ^ 2 ∣ b - 1) (hab : IsCoprime a b) :
    ‖normalizedCubicUnitGauss (a * b)‖ = ‖normalizedCubicUnitGauss a‖ * ‖normalizedCubicUnitGauss b‖ := by
  have he := congrArg norm (normalizedCubicUnitGauss_coprime_product a b ha hb hap hbp hab)
  simpa only [norm_mul, norm_star, symbol_norm_one a b hbp hab, one_mul] using he

lemma normalizedCubicUnitGauss_prime_product_norm {ι : Type*} (s : Finset ι) (p : ι → O)
    (hp : ∀ i ∈ s, Prime (p i)) (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (p i) (p j)) :
    ‖normalizedCubicUnitGauss (∏ i ∈ s, p i)‖ = 1 := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, normalizedCubicUnitGauss_one, norm_one]
  | @insert i s hi ih =>
    have hpi := hp i (Finset.mem_insert_self _ _)
    have hpri := hprimary i (Finset.mem_insert_self _ _)
    have hps : ∀ j ∈ s, Prime (p j) := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    have hprs : ∀ j ∈ s, lambda ^ 2 ∣ p j - 1 := fun j hj => hprimary j (Finset.mem_insert_of_mem hj)
    have hc : IsCoprime (p i) (∏ j ∈ s, p j) := IsCoprime.prod_right (fun j hj =>
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro he; subst j; exact hi hj))
    have hbs : (∏ j ∈ s, p j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j hj => (hps j hj).ne_zero)
    rw [Finset.prod_insert hi, normalizedCubicUnitGauss_coprime_norm _ _ hpi.ne_zero hbs hpri
      (primary_finset_product s p hprs) hc, normalizedCubicUnitGauss_prime_norm _ hpi hpri,
      ih hps hprs (fun j hj k hk hjk => hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk),
      one_mul]

lemma normalizedCubicUnitGauss_squarefree_norm (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0)
    (hsq : Squarefree I) : ‖normalizedCubicUnitGauss (primaryIdealGenerator I)‖ = 1 := by
  rw [primaryIdealGenerator_squarefree_support I hI hsq]
  exact normalizedCubicUnitGauss_prime_product_norm _ _
    (fun P hP => primaryIdealPrime_isPrime_of_mem I P hI hP)
    (fun P hP => (primaryIdealPrime_spec P
      (primaryIdealPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2)
    (primaryIdealPrime_support_coprime I hI)

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
