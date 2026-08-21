import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Special-unitary phase normalization for the Haferkamp et al. construction

The Clifford representatives used in Appendix B of Haferkamp--Faist--
Kothakonda--Eisert--Yunger Halpern (2022) act by conjugation, so their global
complex phase is immaterial.  The random-circuit parameter space, however,
uses `SU(4)`.  This module proves that every finite nonempty unitary matrix
can be multiplied by a unit complex scalar to obtain determinant one, while
leaving every conjugation action exactly unchanged.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every positive natural root of a unit complex number can be chosen to be
a unit complex number. -/
theorem exists_unit_phase_pow_eq
    (w : ℂ) (hw : star w * w = 1) {k : ℕ} (hk : 0 < k) :
    ∃ z : ℂ, star z * z = 1 ∧ z ^ k = w := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w hk
  refine ⟨z, ?_, hz⟩
  have hnormsq_w : Complex.normSq w = 1 := by
    have hcomplex : (Complex.normSq w : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact hw
    exact_mod_cast hcomplex
  have hnormsq_z_pow : Complex.normSq z ^ k = 1 := by
    calc
      Complex.normSq z ^ k = Complex.normSq (z ^ k) := by
        induction k with
        | zero => simp
        | succ k ih => simp [pow_succ, Complex.normSq_mul]
      _ = Complex.normSq w := by rw [hz]
      _ = 1 := hnormsq_w
  have hnormsq_z : Complex.normSq z = 1 :=
    (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg z)
      (Nat.ne_of_gt hk)).mp hnormsq_z_pow
  change (starRingEnd ℂ) z * z = 1
  rw [← Complex.normSq_eq_conj_mul_self]
  exact_mod_cast hnormsq_z

/-- Every unitary matrix on a finite nonempty carrier has a scalar phase
normalization in the special unitary group. -/
theorem exists_scalar_smul_mem_specialUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : 0 < Fintype.card ι)
    (U : Matrix.unitaryGroup ι ℂ) :
    ∃ z : ℂ, star z * z = 1 ∧
      z • (U : Matrix ι ι ℂ) ∈ Matrix.specialUnitaryGroup ι ℂ := by
  have hdet : star U.1.det * U.1.det = 1 := by
    exact (Unitary.mem_iff.mp (Matrix.det_of_mem_unitary U.2)).1
  have hdet_ne : U.1.det ≠ 0 := by
    intro hzero
    rw [hzero, star_zero, zero_mul] at hdet
    norm_num at hdet
  have hstar_det_ne : star U.1.det ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hdet
    norm_num at hdet
  have hstar_det_inv : star (U.1.det)⁻¹ = U.1.det := by
    rw [star_inv₀]
    field_simp [hstar_det_ne]
    exact hdet.symm
  have hdet_inv : star (U.1.det)⁻¹ * (U.1.det)⁻¹ = 1 := by
    rw [hstar_det_inv]
    exact mul_inv_cancel₀ hdet_ne
  obtain ⟨z, hzphase, hzpow⟩ :=
    exists_unit_phase_pow_eq (U.1.det)⁻¹ hdet_inv hι
  refine ⟨z, hzphase, ?_⟩
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    have hzphase' : z * star z = 1 := by
      simpa [mul_comm] using hzphase
    have hU : U.1 * star U.1 = 1 :=
      Matrix.mem_unitaryGroup_iff.mp U.2
    simp only [Matrix.smul_mul, star_smul]
    rw [Matrix.mul_smul]
    simp only [smul_smul, hzphase', hU, one_smul]
  · rw [Matrix.det_smul, hzpow]
    exact inv_mul_cancel₀ hdet_ne

/-- In particular, every two-qubit unitary has a scalar representative in
`SU(4)`. -/
theorem exists_scalar_smul_mem_specialUnitary_twoQubit
    (U : Matrix.unitaryGroup (Bool × Bool) ℂ) :
    ∃ z : ℂ, star z * z = 1 ∧
      z • (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) ∈
        Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  exists_scalar_smul_mem_specialUnitary Fintype.card_pos U

/-- A chosen scalar phase placing a finite nonempty unitary matrix in the
special unitary group. -/
noncomputable def scalarSpecialUnitaryPhase
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U : Matrix.unitaryGroup ι ℂ) : ℂ :=
  Classical.choose (exists_scalar_smul_mem_specialUnitary Fintype.card_pos U)

/-- The chosen normalization scalar has unit modulus. -/
theorem scalarSpecialUnitaryPhase_unitary
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    star (scalarSpecialUnitaryPhase U) * scalarSpecialUnitaryPhase U = 1 :=
  (Classical.choose_spec
    (exists_scalar_smul_mem_specialUnitary Fintype.card_pos U)).1

/-- The chosen phase-normalized matrix has determinant one. -/
theorem scalarSpecialUnitaryPhase_mem_specialUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    scalarSpecialUnitaryPhase U • (U : Matrix ι ι ℂ) ∈
      Matrix.specialUnitaryGroup ι ℂ :=
  (Classical.choose_spec
    (exists_scalar_smul_mem_specialUnitary Fintype.card_pos U)).2

/-- A canonical special-unitary representative of a finite nonempty unitary
matrix, differing only by a global scalar phase. -/
noncomputable def scalarSpecialUnitaryRepresentative
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U : Matrix.unitaryGroup ι ℂ) : Matrix.specialUnitaryGroup ι ℂ :=
  ⟨scalarSpecialUnitaryPhase U • (U : Matrix ι ι ℂ),
    scalarSpecialUnitaryPhase_mem_specialUnitary U⟩

@[simp]
theorem scalarSpecialUnitaryRepresentative_coe
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    (scalarSpecialUnitaryRepresentative U : Matrix ι ι ℂ) =
      scalarSpecialUnitaryPhase U • (U : Matrix ι ι ℂ) := rfl

/-- A unit scalar phase cancels exactly in every matrix conjugation. -/
theorem scalar_smul_conjugation_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ℂ) (U M : Matrix ι ι ℂ) (hz : star z * z = 1) :
    (z • U) * M * Matrix.conjTranspose (z • U) =
      U * M * Matrix.conjTranspose U := by
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hz, one_smul]

/-- The chosen special-unitary representative has exactly the same
conjugation action as the original unitary matrix. -/
theorem scalarSpecialUnitaryRepresentative_conjugation_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U : Matrix.unitaryGroup ι ℂ) (M : Matrix ι ι ℂ) :
    (scalarSpecialUnitaryRepresentative U : Matrix ι ι ℂ) * M *
        Matrix.conjTranspose (scalarSpecialUnitaryRepresentative U : Matrix ι ι ℂ) =
      (U : Matrix ι ι ℂ) * M * Matrix.conjTranspose (U : Matrix ι ι ℂ) := by
  rw [scalarSpecialUnitaryRepresentative_coe]
  exact scalar_smul_conjugation_eq _ _ _ (scalarSpecialUnitaryPhase_unitary U)

end

end GaloisForLFunctions.HTGeometry
