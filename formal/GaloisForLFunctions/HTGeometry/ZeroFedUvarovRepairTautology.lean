import GaloisForLFunctions.HTGeometry.FiniteRankOneSelector

/-!
# Zero-fed Uvarov repair tautology

This module formalizes the finite-dimensional rank-one identity behind the
`zero-fed-uvarov-repair-tautology` card.  If an "unrepaired" Hermitian form is
defined by removing an atom from a given form, restoring that same atom is
exactly the original form.  The Schur scalar then records the standard
rank-one inertia crossing, not an independent source-selection statement.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Complex
open scoped ComplexOrder

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Remove the same rank-one channel that is later added back in the Uvarov chart. -/
def zeroFedUvarovMinus (H0 : Matrix E E ℂ) (v : E → ℂ) (a : ℝ) : Matrix E E ℂ :=
  rankOneRepair H0 v (-a)

omit [Fintype E] [DecidableEq E] in
theorem zeroFedUvarovMinus_eq_sub (H0 : Matrix E E ℂ) (v : E → ℂ) (a : ℝ) :
    zeroFedUvarovMinus H0 v a = H0 - a • Matrix.vecMulVec v (star v) := by
  ext i j
  simp [zeroFedUvarovMinus, rankOneRepair, Matrix.smul_apply, Complex.real_smul]
  ring

omit [Fintype E] [DecidableEq E] in
theorem zeroFedUvarov_repair_eq_base (H0 : Matrix E E ℂ) (v : E → ℂ) (a : ℝ) :
    rankOneRepair (zeroFedUvarovMinus H0 v a) v a = H0 := by
  ext i j
  simp [zeroFedUvarovMinus, rankOneRepair, Matrix.smul_apply, Complex.real_smul]

omit [Fintype E] [DecidableEq E] in
theorem zeroFedUvarov_posSemidef_iff_base (H0 : Matrix E E ℂ) (v : E → ℂ) (a : ℝ) :
    (rankOneRepair (zeroFedUvarovMinus H0 v a) v a).PosSemidef ↔ H0.PosSemidef := by
  rw [zeroFedUvarov_repair_eq_base]

omit [Fintype E] [DecidableEq E] in
theorem zeroFedUvarovMinus_isHermitian {H0 : Matrix E E ℂ} {v : E → ℂ} {a : ℝ}
    (hH0 : H0.IsHermitian) : (zeroFedUvarovMinus H0 v a).IsHermitian :=
  rankOneRepair_isHermitian H0 v (-a) hH0

theorem zeroFedUvarov_scalar_pos_iff_base_posDef {H0 : Matrix E E ℂ} {v : E → ℂ} {a : ℝ}
    (hH0 : H0.IsHermitian) (hHminusUnit : IsUnit (zeroFedUvarovMinus H0 v a))
    (hHminusNeg : hermNegIndex (zeroFedUvarovMinus H0 v a) = 1)
    (hHminusNull : hermNullIndex (zeroFedUvarovMinus H0 v a) = 0) (ha : 0 < a) :
    H0.PosDef ↔ 0 < rankOneSchurScalar (zeroFedUvarovMinus H0 v a) v a := by
  calc
    H0.PosDef ↔ (rankOneRepair (zeroFedUvarovMinus H0 v a) v a).PosDef := by
      rw [zeroFedUvarov_repair_eq_base H0 v a]
    _ ↔ 0 < rankOneSchurScalar (zeroFedUvarovMinus H0 v a) v a :=
      rankOneRepair_posDef_iff_schurScalar_pos (zeroFedUvarovMinus H0 v a) v
        (zeroFedUvarovMinus_isHermitian hH0) hHminusUnit hHminusNeg hHminusNull ha

theorem zeroFedUvarov_wall_kernel {H0 : Matrix E E ℂ} {v : E → ℂ} {a : ℝ}
    (hH0 : H0.IsHermitian) (hHminusUnit : IsUnit (zeroFedUvarovMinus H0 v a))
    (hHminusNeg : hermNegIndex (zeroFedUvarovMinus H0 v a) = 1)
    (hHminusNull : hermNullIndex (zeroFedUvarovMinus H0 v a) = 0) (ha : 0 < a)
    (hs : rankOneSchurScalar (zeroFedUvarovMinus H0 v a) v a = 0) :
    hermNegIndex H0 = 0 ∧ hermNullIndex H0 = 1 ∧ ¬ IsUnit H0 := by
  have h := rankOneRepair_inertia_of_schur_zero (zeroFedUvarovMinus H0 v a) v
    (zeroFedUvarovMinus_isHermitian hH0) hHminusUnit hHminusNeg hHminusNull ha hs
  obtain ⟨_, hneg, hnull⟩ := h
  have hunit := rankOneRepair_not_isUnit_of_schur_zero (zeroFedUvarovMinus H0 v a) v
    (zeroFedUvarovMinus_isHermitian hH0) hHminusUnit hHminusNeg hHminusNull ha hs
  rw [zeroFedUvarov_repair_eq_base] at hneg hnull hunit
  exact ⟨hneg, hnull, hunit⟩

theorem zeroFedUvarov_negative_side {H0 : Matrix E E ℂ} {v : E → ℂ} {a : ℝ}
    (hH0 : H0.IsHermitian) (hHminusUnit : IsUnit (zeroFedUvarovMinus H0 v a))
    (hHminusNeg : hermNegIndex (zeroFedUvarovMinus H0 v a) = 1)
    (hHminusNull : hermNullIndex (zeroFedUvarovMinus H0 v a) = 0) (ha : 0 < a)
    (hs : rankOneSchurScalar (zeroFedUvarovMinus H0 v a) v a < 0) :
    hermNegIndex H0 = 1 ∧ hermNullIndex H0 = 0 := by
  obtain ⟨_, hneg, hnull⟩ := rankOneRepair_inertia_of_schur_neg
    (zeroFedUvarovMinus H0 v a) v (zeroFedUvarovMinus_isHermitian hH0) hHminusUnit
    hHminusNeg hHminusNull ha hs
  rw [zeroFedUvarov_repair_eq_base] at hneg hnull
  exact ⟨hneg, hnull⟩

/-- Exact finite zero-fed Uvarov certificate: subtraction followed by the same
rank-one repair contains no positivity information beyond the original form.

The parameter `d` is the positive inertia index of the unrepaired form; thus
the card's notation `inertia (d, 1)` is interpreted as positive index `d`,
negative index `1`, and null index `0`. -/
theorem zeroFedUvarovRepairTautology (d : ℕ) (H0 : Matrix E E ℂ) (v : E → ℂ) {a : ℝ}
    (hH0 : H0.IsHermitian) (hHminusUnit : IsUnit (zeroFedUvarovMinus H0 v a))
    (hHminusPos : hermPosIndex (zeroFedUvarovMinus H0 v a) = d)
    (hHminusNeg : hermNegIndex (zeroFedUvarovMinus H0 v a) = 1)
    (hHminusNull : hermNullIndex (zeroFedUvarovMinus H0 v a) = 0) (ha : 0 < a)
    (hm : rankOneEnergy (zeroFedUvarovMinus H0 v a) v < 0) :
    v ≠ 0 ∧
      ((rankOneRepair (zeroFedUvarovMinus H0 v a) v a).PosSemidef ↔ H0.PosSemidef) ∧
      (H0.PosDef ↔ 0 < rankOneSchurScalar (zeroFedUvarovMinus H0 v a) v a) ∧
      (rankOneSchurScalar (zeroFedUvarovMinus H0 v a) v a = 0 →
        hermPosIndex H0 = d ∧ hermNegIndex H0 = 0 ∧ hermNullIndex H0 = 1 ∧ ¬ IsUnit H0) ∧
      (rankOneSchurScalar (zeroFedUvarovMinus H0 v a) v a < 0 →
        hermPosIndex H0 = d ∧ hermNegIndex H0 = 1 ∧ hermNullIndex H0 = 0) := by
  refine ⟨rankOneEnergy_neg_implies_ne_zero (zeroFedUvarovMinus H0 v a) v hm,
    zeroFedUvarov_posSemidef_iff_base H0 v a,
    zeroFedUvarov_scalar_pos_iff_base_posDef hH0 hHminusUnit hHminusNeg hHminusNull ha,
    ?_, ?_⟩
  · intro hs
    obtain ⟨hpos, hneg, hnull⟩ :=
      rankOneRepair_inertia_of_schur_zero (zeroFedUvarovMinus H0 v a) v
        (zeroFedUvarovMinus_isHermitian hH0) hHminusUnit hHminusNeg hHminusNull ha hs
    have hunit := rankOneRepair_not_isUnit_of_schur_zero (zeroFedUvarovMinus H0 v a) v
      (zeroFedUvarovMinus_isHermitian hH0) hHminusUnit hHminusNeg hHminusNull ha hs
    rw [zeroFedUvarov_repair_eq_base H0 v a, hHminusPos] at hpos
    rw [zeroFedUvarov_repair_eq_base H0 v a] at hneg hnull hunit
    exact ⟨hpos, hneg, hnull, hunit⟩
  · intro hs
    obtain ⟨hpos, hneg, hnull⟩ :=
      rankOneRepair_inertia_of_schur_neg (zeroFedUvarovMinus H0 v a) v
        (zeroFedUvarovMinus_isHermitian hH0) hHminusUnit hHminusNeg hHminusNull ha hs
    rw [zeroFedUvarov_repair_eq_base H0 v a, hHminusPos] at hpos
    rw [zeroFedUvarov_repair_eq_base H0 v a] at hneg hnull
    exact ⟨hpos, hneg, hnull⟩

end

end GaloisForLFunctions.HTGeometry
