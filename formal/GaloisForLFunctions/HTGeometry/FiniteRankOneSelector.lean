import GaloisForLFunctions.HTGeometry.HermitianInertiaPosDef
import GaloisForLFunctions.HTGeometry.FiniteRankBoundarySchurIndex

/-!
# Finite rank-one selector crossing

This module formalizes the exact finite-dimensional Hermitian rank-one crossing used by the
`finite-rank-one-selector-no-free-lunch` card.  It proves the Schur scalar criterion, the
below/wall/above inertia trichotomy, the one-dimensional crossing kernel, and the precise
selector-factorization statement without adding assumptions or axioms.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Complex
open scoped ComplexOrder Matrix

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

def rankOneChannel (v : E → ℂ) : Matrix E (Fin 1) ℂ :=
  Matrix.replicateCol (Fin 1) v

def rankOneBoundary (t : ℝ) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal fun _ => (t : ℂ)

def rankOneRepair (A : Matrix E E ℂ) (v : E → ℂ) (t : ℝ) : Matrix E E ℂ :=
  A + t • Matrix.vecMulVec v (star v)

def rankOneEnergy (A : Matrix E E ℂ) (v : E → ℂ) : ℝ :=
  (star v ⬝ᵥ A⁻¹ *ᵥ v).re

def rankOneSchurScalar (A : Matrix E E ℂ) (v : E → ℂ) (t : ℝ) : ℝ :=
  -t⁻¹ - rankOneEnergy A v

def rankOneThreshold (A : Matrix E E ℂ) (v : E → ℂ) : ℝ :=
  -1 / rankOneEnergy A v

theorem rankOneBoundary_isHermitian (t : ℝ) : (rankOneBoundary t).IsHermitian := by
  rw [rankOneBoundary, Matrix.isHermitian_diagonal_iff]
  intro i
  rw [isSelfAdjoint_iff]
  simp

theorem rankOneBoundary_inv (t : ℝ) :
    (rankOneBoundary t)⁻¹ = rankOneBoundary t⁻¹ := by
  ext i j
  fin_cases i
  fin_cases j
  simp [rankOneBoundary, Matrix.inv_subsingleton]

theorem rankOneBoundary_isUnit {t : ℝ} (ht : t ≠ 0) : IsUnit (rankOneBoundary t) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  simpa [rankOneBoundary] using (isUnit_iff_ne_zero.mpr htC)

omit [Fintype E] [DecidableEq E] in
theorem rankOneRepair_eq_finiteRankRepaired (A : Matrix E E ℂ) (v : E → ℂ) (t : ℝ) :
    finiteRankRepaired A (rankOneChannel v) (rankOneBoundary t) = rankOneRepair A v t := by
  ext i j
  simp [finiteRankRepaired, rankOneChannel, rankOneBoundary, rankOneRepair,
    Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.replicateCol_apply,
    Matrix.smul_apply, Complex.real_smul, mul_assoc]
  ring

theorem rankOneEnergy_coe (A : Matrix E E ℂ) (v : E → ℂ) (hA : A.IsHermitian) :
    ((rankOneEnergy A v : ℝ) : ℂ) = star v ⬝ᵥ A⁻¹ *ᵥ v := by
  have him : (star v ⬝ᵥ A⁻¹ *ᵥ v).im = 0 :=
    hA.inv.im_star_dotProduct_mulVec_self v
  apply Complex.ext <;> simp [rankOneEnergy, him]

theorem rankOneBoundarySchur_eq (A : Matrix E E ℂ) (v : E → ℂ) (t : ℝ)
    (hA : A.IsHermitian) :
    finiteRankBoundarySchur A (rankOneChannel v) (rankOneBoundary t) =
      rankOneBoundary (rankOneSchurScalar A v t) := by
  have hquad :
      ∑ x, (∑ y, star (v y) * A⁻¹ y x) * v x = star v ⬝ᵥ A⁻¹ *ᵥ v := by
    calc
      ∑ x, (∑ y, star (v y) * A⁻¹ y x) * v x =
          ∑ x, ∑ y, (star (v y) * A⁻¹ y x) * v x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_mul]
      _ = ∑ y, ∑ x, (star (v y) * A⁻¹ y x) * v x := by
        rw [Finset.sum_comm]
      _ = ∑ y, star (v y) * ∑ x, A⁻¹ y x * v x := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = star v ⬝ᵥ A⁻¹ *ᵥ v := by
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [finiteRankBoundarySchur, rankOneBoundary_inv]
  ext i j
  fin_cases i
  fin_cases j
  simp only [rankOneChannel, rankOneBoundary, Matrix.replicateCol_apply,
    Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [hquad, ← rankOneEnergy_coe A v hA]
  simp [rankOneSchurScalar]

theorem rankOneBoundary_posIndex_of_pos {x : ℝ} (hx : 0 < x) :
    hermPosIndex (rankOneBoundary x) = 1 := by
  rw [rankOneBoundary, posIndex_diagonal]
  simp [hx]

theorem rankOneBoundary_negIndex_of_pos {x : ℝ} (hx : 0 < x) :
    hermNegIndex (rankOneBoundary x) = 0 := by
  rw [rankOneBoundary, negIndex_diagonal]
  simp [not_lt_of_ge hx.le]

theorem rankOneBoundary_nullIndex_of_pos {x : ℝ} (hx : 0 < x) :
    hermNullIndex (rankOneBoundary x) = 0 := by
  rw [rankOneBoundary, nullIndex_diagonal]
  simp [hx.ne']

theorem rankOneBoundary_posIndex_of_neg {x : ℝ} (hx : x < 0) :
    hermPosIndex (rankOneBoundary x) = 0 := by
  rw [rankOneBoundary, posIndex_diagonal]
  simp [not_lt_of_ge hx.le]

theorem rankOneBoundary_negIndex_of_neg {x : ℝ} (hx : x < 0) :
    hermNegIndex (rankOneBoundary x) = 1 := by
  rw [rankOneBoundary, negIndex_diagonal]
  simp [hx]

theorem rankOneBoundary_nullIndex_of_neg {x : ℝ} (hx : x < 0) :
    hermNullIndex (rankOneBoundary x) = 0 := by
  rw [rankOneBoundary, nullIndex_diagonal]
  simp [ne_of_lt hx]

theorem rankOneBoundary_posIndex_of_zero :
    hermPosIndex (rankOneBoundary 0) = 0 := by
  rw [rankOneBoundary, posIndex_diagonal]
  simp

theorem rankOneBoundary_negIndex_of_zero :
    hermNegIndex (rankOneBoundary 0) = 0 := by
  rw [rankOneBoundary, negIndex_diagonal]
  simp

theorem rankOneBoundary_nullIndex_of_zero :
    hermNullIndex (rankOneBoundary 0) = 1 := by
  rw [rankOneBoundary, nullIndex_diagonal]
  simp

theorem neg_rankOneBoundary_inv_eq (t : ℝ) :
    -(rankOneBoundary t)⁻¹ = rankOneBoundary (-t⁻¹) := by
  rw [rankOneBoundary_inv]
  ext i j
  fin_cases i
  fin_cases j
  simp [rankOneBoundary]

omit [Fintype E] [DecidableEq E] in
theorem rankOneRepair_isHermitian (A : Matrix E E ℂ) (v : E → ℂ) (t : ℝ)
    (hA : A.IsHermitian) : (rankOneRepair A v t).IsHermitian := by
  rw [← rankOneRepair_eq_finiteRankRepaired]
  exact finiteRankRepaired_isHermitian hA (rankOneBoundary_isHermitian t)

theorem rankOneRepair_inertia_balanced (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (hA : A.IsHermitian) (hAunit : IsUnit A) (ht : 0 < t) :
    hermPosIndex A + hermPosIndex (rankOneBoundary (rankOneSchurScalar A v t)) =
        hermPosIndex (rankOneRepair A v t) + hermPosIndex (rankOneBoundary (-t⁻¹)) ∧
      hermNegIndex A + hermNegIndex (rankOneBoundary (rankOneSchurScalar A v t)) =
        hermNegIndex (rankOneRepair A v t) + hermNegIndex (rankOneBoundary (-t⁻¹)) ∧
      hermNullIndex A + hermNullIndex (rankOneBoundary (rankOneSchurScalar A v t)) =
        hermNullIndex (rankOneRepair A v t) + hermNullIndex (rankOneBoundary (-t⁻¹)) := by
  have h := finiteRankBoundary_inertia_balanced hA (rankOneBoundary_isHermitian t) hAunit
    (rankOneBoundary_isUnit ht.ne') (V := rankOneChannel v)
  rw [rankOneRepair_eq_finiteRankRepaired, rankOneBoundarySchur_eq A v t hA,
    neg_rankOneBoundary_inv_eq] at h
  exact h

theorem rankOneRepair_inertia_of_schur_pos (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (hA : A.IsHermitian) (hAunit : IsUnit A) (hAneg : hermNegIndex A = 1)
    (hAnull : hermNullIndex A = 0) (ht : 0 < t)
    (hs : 0 < rankOneSchurScalar A v t) :
    hermPosIndex (rankOneRepair A v t) = hermPosIndex A + 1 ∧
      hermNegIndex (rankOneRepair A v t) = 0 ∧
        hermNullIndex (rankOneRepair A v t) = 0 := by
  obtain ⟨hpos, hneg, hnull⟩ := rankOneRepair_inertia_balanced A v hA hAunit ht
  have htn : -t⁻¹ < 0 := by
    have hti : 0 < t⁻¹ := inv_pos.mpr ht
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [rankOneBoundary_posIndex_of_pos hs,
      rankOneBoundary_posIndex_of_neg htn] at hpos
    omega
  · rw [hAneg, rankOneBoundary_negIndex_of_pos hs,
      rankOneBoundary_negIndex_of_neg htn] at hneg
    omega
  · rw [hAnull, rankOneBoundary_nullIndex_of_pos hs,
      rankOneBoundary_nullIndex_of_neg htn] at hnull
    omega

theorem rankOneRepair_inertia_of_schur_neg (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (hA : A.IsHermitian) (hAunit : IsUnit A) (hAneg : hermNegIndex A = 1)
    (hAnull : hermNullIndex A = 0) (ht : 0 < t)
    (hs : rankOneSchurScalar A v t < 0) :
    hermPosIndex (rankOneRepair A v t) = hermPosIndex A ∧
      hermNegIndex (rankOneRepair A v t) = 1 ∧
        hermNullIndex (rankOneRepair A v t) = 0 := by
  obtain ⟨hpos, hneg, hnull⟩ := rankOneRepair_inertia_balanced A v hA hAunit ht
  have htn : -t⁻¹ < 0 := by
    have hti : 0 < t⁻¹ := inv_pos.mpr ht
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [rankOneBoundary_posIndex_of_neg hs,
      rankOneBoundary_posIndex_of_neg htn] at hpos
    omega
  · rw [hAneg, rankOneBoundary_negIndex_of_neg hs,
      rankOneBoundary_negIndex_of_neg htn] at hneg
    omega
  · rw [hAnull, rankOneBoundary_nullIndex_of_neg hs,
      rankOneBoundary_nullIndex_of_neg htn] at hnull
    omega

theorem rankOneRepair_inertia_of_schur_zero (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (hA : A.IsHermitian) (hAunit : IsUnit A) (hAneg : hermNegIndex A = 1)
    (hAnull : hermNullIndex A = 0) (ht : 0 < t)
    (hs : rankOneSchurScalar A v t = 0) :
    hermPosIndex (rankOneRepair A v t) = hermPosIndex A ∧
      hermNegIndex (rankOneRepair A v t) = 0 ∧
        hermNullIndex (rankOneRepair A v t) = 1 := by
  obtain ⟨hpos, hneg, hnull⟩ := rankOneRepair_inertia_balanced A v hA hAunit ht
  have htn : -t⁻¹ < 0 := by
    have hti : 0 < t⁻¹ := inv_pos.mpr ht
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hs, rankOneBoundary_posIndex_of_zero,
      rankOneBoundary_posIndex_of_neg htn] at hpos
    omega
  · rw [hAneg, hs, rankOneBoundary_negIndex_of_zero,
      rankOneBoundary_negIndex_of_neg htn] at hneg
    omega
  · rw [hAnull, hs, rankOneBoundary_nullIndex_of_zero,
      rankOneBoundary_nullIndex_of_neg htn] at hnull
    omega

theorem rankOneRepair_posDef_iff_schurScalar_pos (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (hA : A.IsHermitian) (hAunit : IsUnit A) (hAneg : hermNegIndex A = 1)
    (hAnull : hermNullIndex A = 0) (ht : 0 < t) :
    (rankOneRepair A v t).PosDef ↔ 0 < rankOneSchurScalar A v t := by
  constructor
  · intro hH
    obtain ⟨hHneg, hHnull⟩ :=
      (hermPosDef_iff_negIndex_eq_zero_and_nullIndex_eq_zero
        (rankOneRepair_isHermitian A v t hA)).mp hH
    by_contra hs
    rcases lt_or_eq_of_le (le_of_not_gt hs) with hsneg | hszero
    · obtain ⟨_, hneg, _⟩ :=
        rankOneRepair_inertia_of_schur_neg A v hA hAunit hAneg hAnull ht hsneg
      omega
    · obtain ⟨_, _, hnull⟩ :=
        rankOneRepair_inertia_of_schur_zero A v hA hAunit hAneg hAnull ht hszero
      omega
  · intro hs
    obtain ⟨_, hneg, hnull⟩ :=
      rankOneRepair_inertia_of_schur_pos A v hA hAunit hAneg hAnull ht hs
    exact (hermPosDef_iff_negIndex_eq_zero_and_nullIndex_eq_zero
      (rankOneRepair_isHermitian A v t hA)).mpr ⟨hneg, hnull⟩

theorem rankOneRepair_not_isUnit_of_schur_zero (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (hA : A.IsHermitian) (hAunit : IsUnit A) (hAneg : hermNegIndex A = 1)
    (hAnull : hermNullIndex A = 0) (ht : 0 < t)
    (hs : rankOneSchurScalar A v t = 0) : ¬ IsUnit (rankOneRepair A v t) := by
  intro hunit
  obtain ⟨_, _, hnull⟩ :=
    rankOneRepair_inertia_of_schur_zero A v hA hAunit hAneg hAnull ht hs
  have hinj : Function.Injective (rankOneRepair A v t).mulVecLin :=
    mulVecLin_injective hunit
  have hker : LinearMap.ker (rankOneRepair A v t).mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  rw [hermNullIndex, hker] at hnull
  rw [finrank_bot] at hnull
  omega

theorem rankOneSchurScalar_eq_neg_one_add_mul_div (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (ht : 0 < t) :
    rankOneSchurScalar A v t = -(1 + rankOneEnergy A v * t) / t := by
  unfold rankOneSchurScalar
  field_simp [ht.ne']
  ring

theorem rankOneThreshold_pos (A : Matrix E E ℂ) (v : E → ℂ)
    (hm : rankOneEnergy A v < 0) : 0 < rankOneThreshold A v := by
  unfold rankOneThreshold
  exact div_pos_of_neg_of_neg (by norm_num) hm

theorem rankOneSchurScalar_pos_iff_threshold_lt (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (ht : 0 < t) (hm : rankOneEnergy A v < 0) :
    0 < rankOneSchurScalar A v t ↔ rankOneThreshold A v < t := by
  rw [rankOneThreshold, rankOneSchurScalar_eq_neg_one_add_mul_div A v ht,
    div_pos_iff_of_pos_right ht, neg_pos, div_lt_iff_of_neg hm]
  constructor <;> intro h <;> nlinarith [h]

theorem rankOneSchurScalar_neg_iff_lt_threshold (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (ht : 0 < t) (hm : rankOneEnergy A v < 0) :
    rankOneSchurScalar A v t < 0 ↔ t < rankOneThreshold A v := by
  rw [rankOneThreshold, rankOneSchurScalar_eq_neg_one_add_mul_div A v ht]
  constructor
  · intro hs
    rw [neg_div] at hs
    have hdiv : 0 < (1 + rankOneEnergy A v * t) / t := by linarith
    have hnum : 0 < 1 + rankOneEnergy A v * t :=
      (div_pos_iff_of_pos_right ht).mp hdiv
    rw [lt_div_iff_of_neg hm]
    nlinarith [hnum]
  · intro hlt
    rw [lt_div_iff_of_neg hm] at hlt
    have hnum : 0 < 1 + rankOneEnergy A v * t := by nlinarith [hlt]
    have hdiv : 0 < (1 + rankOneEnergy A v * t) / t :=
      (div_pos_iff_of_pos_right ht).mpr hnum
    rw [neg_div]
    linarith

theorem rankOneSchurScalar_eq_zero_iff_threshold (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (ht : 0 < t) (hm : rankOneEnergy A v < 0) :
    rankOneSchurScalar A v t = 0 ↔ t = rankOneThreshold A v := by
  constructor
  · intro hs
    have hnotUpper : ¬ rankOneThreshold A v < t := by
      intro hlt
      have hpos := (rankOneSchurScalar_pos_iff_threshold_lt A v ht hm).mpr hlt
      linarith
    have hnotLower : ¬ t < rankOneThreshold A v := by
      intro hlt
      have hneg := (rankOneSchurScalar_neg_iff_lt_threshold A v ht hm).mpr hlt
      linarith
    exact le_antisymm (le_of_not_gt hnotUpper) (le_of_not_gt hnotLower)
  · intro htEq
    subst t
    have hthresholdPos := rankOneThreshold_pos A v hm
    apply le_antisymm
    · apply le_of_not_gt
      intro hpos
      have hlt :=
        (rankOneSchurScalar_pos_iff_threshold_lt A v hthresholdPos hm).mp hpos
      exact (lt_irrefl _ hlt)
    · apply le_of_not_gt
      intro hneg
      have hlt :=
        (rankOneSchurScalar_neg_iff_lt_threshold A v hthresholdPos hm).mp hneg
      exact (lt_irrefl _ hlt)

theorem rankOneRepair_posDef_iff_above_threshold (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (hA : A.IsHermitian) (hAunit : IsUnit A) (hAneg : hermNegIndex A = 1)
    (hAnull : hermNullIndex A = 0) (ht : 0 < t) (hm : rankOneEnergy A v < 0) :
    (rankOneRepair A v t).PosDef ↔ rankOneThreshold A v < t :=
  (rankOneRepair_posDef_iff_schurScalar_pos A v hA hAunit hAneg hAnull ht).trans
    (rankOneSchurScalar_pos_iff_threshold_lt A v ht hm)

theorem rankOneRepair_inertia_below_threshold (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (hA : A.IsHermitian) (hAunit : IsUnit A) (hAneg : hermNegIndex A = 1)
    (hAnull : hermNullIndex A = 0) (ht : 0 < t) (hm : rankOneEnergy A v < 0)
    (hlt : t < rankOneThreshold A v) :
    hermPosIndex (rankOneRepair A v t) = hermPosIndex A ∧
      hermNegIndex (rankOneRepair A v t) = 1 ∧
        hermNullIndex (rankOneRepair A v t) = 0 :=
  rankOneRepair_inertia_of_schur_neg A v hA hAunit hAneg hAnull ht
    ((rankOneSchurScalar_neg_iff_lt_threshold A v ht hm).mpr hlt)

theorem rankOneRepair_crossing_kernel (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (hA : A.IsHermitian) (hAunit : IsUnit A) (hAneg : hermNegIndex A = 1)
    (hAnull : hermNullIndex A = 0) (ht : 0 < t) (hm : rankOneEnergy A v < 0)
    (htEq : t = rankOneThreshold A v) :
    hermPosIndex (rankOneRepair A v t) = hermPosIndex A ∧
      hermNegIndex (rankOneRepair A v t) = 0 ∧
        hermNullIndex (rankOneRepair A v t) = 1 ∧ ¬ IsUnit (rankOneRepair A v t) := by
  have hs := (rankOneSchurScalar_eq_zero_iff_threshold A v ht hm).mpr htEq
  obtain ⟨hpos, hneg, hnull⟩ :=
    rankOneRepair_inertia_of_schur_zero A v hA hAunit hAneg hAnull ht hs
  exact ⟨hpos, hneg, hnull,
    rankOneRepair_not_isUnit_of_schur_zero A v hA hAunit hAneg hAnull ht hs⟩

theorem rankOneSelector_iff_schurScalar_pos (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (hA : A.IsHermitian) (hAunit : IsUnit A) (hAneg : hermNegIndex A = 1)
    (hAnull : hermNullIndex A = 0) (ht : 0 < t) {P : ℝ → Prop}
    (hP : P t ↔ (rankOneRepair A v t).PosDef) :
    P t ↔ 0 < rankOneSchurScalar A v t :=
  hP.trans (rankOneRepair_posDef_iff_schurScalar_pos A v hA hAunit hAneg hAnull ht)

theorem rankOneEnergy_neg_implies_ne_zero (A : Matrix E E ℂ) (v : E → ℂ)
    (hm : rankOneEnergy A v < 0) : v ≠ 0 := by
  intro hv
  subst v
  simp [rankOneEnergy] at hm

/-- Exact finite rank-one crossing certificate underlying the no-free-lunch selector card. -/
theorem finiteRankOneSelector_noFreeLunch (n : ℕ) (A : Matrix E E ℂ) (v : E → ℂ) {t : ℝ}
    (hA : A.IsHermitian) (hAunit : IsUnit A) (hApos : hermPosIndex A = n)
    (hAneg : hermNegIndex A = 1) (hAnull : hermNullIndex A = 0) (ht : 0 < t)
    (hm : rankOneEnergy A v < 0) :
    v ≠ 0 ∧
      ((rankOneRepair A v t).PosDef ↔ rankOneThreshold A v < t) ∧
      (0 < rankOneSchurScalar A v t →
        hermPosIndex (rankOneRepair A v t) = n + 1 ∧
          hermNegIndex (rankOneRepair A v t) = 0 ∧
            hermNullIndex (rankOneRepair A v t) = 0) ∧
      (t < rankOneThreshold A v →
        hermPosIndex (rankOneRepair A v t) = n ∧
          hermNegIndex (rankOneRepair A v t) = 1 ∧
            hermNullIndex (rankOneRepair A v t) = 0) ∧
      (t = rankOneThreshold A v →
        hermPosIndex (rankOneRepair A v t) = n ∧
          hermNegIndex (rankOneRepair A v t) = 0 ∧
            hermNullIndex (rankOneRepair A v t) = 1 ∧ ¬ IsUnit (rankOneRepair A v t)) := by
  refine ⟨rankOneEnergy_neg_implies_ne_zero A v hm,
    rankOneRepair_posDef_iff_above_threshold A v hA hAunit hAneg hAnull ht hm, ?_, ?_, ?_⟩
  · intro hs
    obtain ⟨hpos, hneg, hnull⟩ :=
      rankOneRepair_inertia_of_schur_pos A v hA hAunit hAneg hAnull ht hs
    rw [hApos] at hpos
    exact ⟨hpos, hneg, hnull⟩
  · intro hlt
    obtain ⟨hpos, hneg, hnull⟩ :=
      rankOneRepair_inertia_below_threshold A v hA hAunit hAneg hAnull ht hm hlt
    rw [hApos] at hpos
    exact ⟨hpos, hneg, hnull⟩
  · intro htEq
    obtain ⟨hpos, hneg, hnull, hsing⟩ :=
      rankOneRepair_crossing_kernel A v hA hAunit hAneg hAnull ht hm htEq
    rw [hApos] at hpos
    exact ⟨hpos, hneg, hnull, hsing⟩

end

end GaloisForLFunctions.HTGeometry

