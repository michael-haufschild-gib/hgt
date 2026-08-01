import GaloisForLFunctions.HTGeometry.PurePairNormalFracture
import GaloisForLFunctions.HTGeometry.HiggsCausalOrbit
import Mathlib.LinearAlgebra.UnitaryGroup

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

abbrev PurePairAgreementNormal := Fin 3 → ℂ

abbrev PurePairNormalModel := PurePairAgreementNormal × ColorPreservingNormal

def purePairNormalSplit : (Fin 5 → ℂ) ≃ₗ[ℂ] PurePairNormalModel where
  toFun w := (![w 0, w 1, w 2], ![w 3, w 4])
  invFun x := ![x.1 0, x.1 1, x.1 2, x.2 0, x.2 1]
  left_inv w := by
    funext i
    fin_cases i <;> simp
  right_inv x := by
    ext i <;> fin_cases i <;> simp
  map_add' x y := by
    ext i <;> fin_cases i <;> simp
  map_smul' c x := by
    ext i <;> fin_cases i <;> simp

def purePairAgreementDifferential :
    SpinTenEvenCoordinate →ₗ[ℂ] PurePairAgreementNormal where
  toFun := purePairAgreementReporter
  map_add' x y := by
    funext i
    fin_cases i <;>
      simp [purePairAgreementReporter, firstPairVectorReporter, spinTenFour]
  map_smul' c x := by
    funext i
    fin_cases i <;>
      simp [purePairAgreementReporter, firstPairVectorReporter, spinTenFour]

def secondPurePairTangentConstraintDifferential :
    SpinTenEvenCoordinate →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun v := ![spinTenTwo v 0 1, spinTenTwo v 0 2,
    spinTenTwo v 1 2, spinTenFour v 3, spinTenFour v 4]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [spinTenTwo, spinTenFour]
  map_smul' c x := by
    funext i
    fin_cases i <;> simp [spinTenTwo, spinTenFour]

def purePairTangentAtSecondSubmodule : Submodule ℂ SpinTenEvenCoordinate :=
  LinearMap.ker secondPurePairTangentConstraintDifferential

theorem mem_purePairTangentAtSecondSubmodule_iff
    (v : SpinTenEvenCoordinate) :
    v ∈ purePairTangentAtSecondSubmodule ↔ tangentCartanAtSecond v := by
  rw [purePairTangentAtSecondSubmodule, LinearMap.mem_ker,
    tangentCartanAtSecond_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [secondPurePairTangentConstraintDifferential] using congrFun h 0
    · simpa [secondPurePairTangentConstraintDifferential] using congrFun h 1
    · simpa [secondPurePairTangentConstraintDifferential] using congrFun h 2
    · simpa [secondPurePairTangentConstraintDifferential] using congrFun h 3
    · simpa [secondPurePairTangentConstraintDifferential] using congrFun h 4
  · rintro ⟨h01, h02, h12, h3, h4⟩
    funext i
    fin_cases i <;>
      simp [secondPurePairTangentConstraintDifferential,
        h01, h02, h12, h3, h4]

def purePairTangentAgreementDifferential :
    purePairTangentAtSecondSubmodule →ₗ[ℂ] PurePairAgreementNormal :=
  purePairAgreementDifferential.domRestrict purePairTangentAtSecondSubmodule

theorem purePairTangentAgreementDifferential_surjective :
    Function.Surjective purePairTangentAgreementDifferential := by
  intro c
  refine ⟨⟨pureTangentVariationOfAgreement c,
    (mem_purePairTangentAtSecondSubmodule_iff _).mpr
      (pureTangentVariationOfAgreement_is_tangent c)⟩, ?_⟩
  exact purePairAgreementReporter_variationOfAgreement c

abbrev PurePairJointlyPureTangentAtSecond :=
  LinearMap.ker purePairTangentAgreementDifferential

abbrev PurePairTangentCompatibilityQuotient :=
  purePairTangentAtSecondSubmodule ⧸ PurePairJointlyPureTangentAtSecond

def purePairTangentAgreementRangeEquiv :
    LinearMap.range purePairTangentAgreementDifferential ≃ₗ[ℂ]
      PurePairAgreementNormal :=
  LinearEquiv.ofBijective
    (LinearMap.range purePairTangentAgreementDifferential).subtype
    ⟨Submodule.subtype_injective _, by
      intro c
      obtain ⟨v, hv⟩ := purePairTangentAgreementDifferential_surjective c
      exact ⟨⟨c, ⟨v, hv⟩⟩, rfl⟩⟩

def purePairTangentCompatibilityQuotientEquivAgreement :
    PurePairTangentCompatibilityQuotient ≃ₗ[ℂ] PurePairAgreementNormal :=
  (LinearMap.quotKerEquivRange purePairTangentAgreementDifferential).trans
    purePairTangentAgreementRangeEquiv

theorem purePairTangent_image_eq_agreement :
    LinearMap.range purePairTangentAgreementDifferential = ⊤ := by
  exact LinearMap.range_eq_top.mpr
    purePairTangentAgreementDifferential_surjective

theorem purePairTangent_disagreement_eq_zero
    (v : purePairTangentAtSecondSubmodule) :
    purePairDisagreementReporter v.1 = 0 := by
  apply purePairDisagreementReporter_eq_zero_of_tangent v.1
  exact (mem_purePairTangentAtSecondSubmodule_iff v.1).mp v.property

def firstPurePairCartanDifferential :
    SpinTenEvenCoordinate →ₗ[ℂ] PurePairNormalModel where
  toFun v := purePairNormalSplit (spinTenFour v)
  map_add' x y := by
    simp [spinTenFour]
  map_smul' c x := by
    simp [spinTenFour]

theorem firstPurePairCartanDifferential_eq_reporters
    (v : SpinTenEvenCoordinate) :
    firstPurePairCartanDifferential v =
      (purePairAgreementReporter v, purePairDisagreementReporter v) := by
  ext i <;> fin_cases i <;>
    simp [firstPurePairCartanDifferential, purePairNormalSplit,
      purePairAgreementReporter, purePairDisagreementReporter,
      firstPairVectorReporter, spinTenFour]

theorem firstPurePairCartanDifferential_eq_cartanPolar
    (v : SpinTenEvenCoordinate) :
    purePairNormalSplit (spinTenCartanPolar firstPurePairSpinor v).1 =
        firstPurePairCartanDifferential v ∧
      (spinTenCartanPolar firstPurePairSpinor v).2 = 0 := by
  constructor
  · rw [firstPairVectorReporter_eq_cartanPolar_upper]
    rfl
  · exact firstPair_cartanPolar_lower_eq_zero v

theorem firstPurePairCartanDifferential_surjective :
    Function.Surjective firstPurePairCartanDifferential := by
  rintro ⟨a, b⟩
  refine ⟨(0, 0, ![a 0, a 1, a 2, b 0, b 1]), ?_⟩
  ext i <;> fin_cases i <;>
    simp [firstPurePairCartanDifferential, purePairNormalSplit, spinTenFour]

theorem mem_firstPurePairCartanDifferential_ker_iff
    (v : SpinTenEvenCoordinate) :
    v ∈ LinearMap.ker firstPurePairCartanDifferential ↔
      spinTenCartanPolar firstPurePairSpinor v = 0 := by
  constructor
  · intro hv
    rw [LinearMap.mem_ker] at hv
    have hfour : firstPairVectorReporter v = 0 := by
      apply purePairNormalSplit.injective
      simpa [firstPurePairCartanDifferential, firstPairVectorReporter] using hv
    apply Prod.ext
    · rw [firstPairVectorReporter_eq_cartanPolar_upper]
      exact hfour
    · exact firstPair_cartanPolar_lower_eq_zero v
  · intro hv
    rw [LinearMap.mem_ker]
    have hu := congrArg Prod.fst hv
    rw [firstPairVectorReporter_eq_cartanPolar_upper] at hu
    change firstPairVectorReporter v = 0 at hu
    change purePairNormalSplit (spinTenFour v) = 0
    rw [← purePairNormalSplit.map_zero]
    apply congrArg purePairNormalSplit
    simpa [firstPairVectorReporter] using hu

abbrev FirstPurePairProjectiveNormalFiber :=
  SpinTenEvenCoordinate ⧸ LinearMap.ker firstPurePairCartanDifferential

def firstPurePairCartanDifferentialRangeEquiv :
    LinearMap.range firstPurePairCartanDifferential ≃ₗ[ℂ]
      PurePairNormalModel :=
  LinearEquiv.ofBijective
    (LinearMap.range firstPurePairCartanDifferential).subtype
    ⟨Submodule.subtype_injective _, by
      intro y
      obtain ⟨v, hv⟩ := firstPurePairCartanDifferential_surjective y
      exact ⟨⟨y, ⟨v, hv⟩⟩, rfl⟩⟩

def firstPurePairProjectiveNormalFiberEquiv :
    FirstPurePairProjectiveNormalFiber ≃ₗ[ℂ] PurePairNormalModel :=
  (LinearMap.quotKerEquivRange firstPurePairCartanDifferential).trans
    firstPurePairCartanDifferentialRangeEquiv

def purePairColorSignDiagonal (i : Fin 3) : Fin 3 → ℂ :=
  match i with
  | ⟨0, _⟩ => ![-1, -1, 1]
  | ⟨1, _⟩ => ![1, -1, -1]
  | ⟨2, _⟩ => ![-1, 1, -1]

def purePairColorSignFlipMatrix (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (purePairColorSignDiagonal i)

theorem purePairColorSignFlipMatrix_mem (i : Fin 3) :
    purePairColorSignFlipMatrix i ∈
      Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff']
    rw [purePairColorSignFlipMatrix, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp [purePairColorSignDiagonal]
  · rw [purePairColorSignFlipMatrix, Matrix.det_diagonal]
    fin_cases i <;>
      simp [purePairColorSignDiagonal, Fin.prod_univ_succ]

def purePairColorAction
    (U : Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    PurePairNormalModel →ₗ[ℂ] PurePairNormalModel where
  toFun x := ((U.1 *ᵥ x.1), x.2)
  map_add' x y := by
    ext i <;> simp [Matrix.mulVec_add]
  map_smul' c x := by
    ext i <;> simp [Matrix.mulVec_smul]

theorem purePairColorAction_one (x : PurePairNormalModel) :
    purePairColorAction 1 x = x := by
  ext i <;> simp [purePairColorAction]

theorem purePairColorAction_mul
    (U V : Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (x : PurePairNormalModel) :
    purePairColorAction (U * V) x =
      purePairColorAction U (purePairColorAction V x) := by
  ext i <;> simp [purePairColorAction, Matrix.mulVec_mulVec]

def purePairColorFixedSubspace : Submodule ℂ PurePairNormalModel where
  carrier := {x | ∀ U, purePairColorAction U x = x}
  zero_mem' := by
    intro U
    exact LinearMap.map_zero _
  add_mem' := by
    intro x y hx hy
    change (∀ U, purePairColorAction U x = x) at hx
    change (∀ U, purePairColorAction U y = y) at hy
    change ∀ U, purePairColorAction U (x + y) = x + y
    intro U
    rw [LinearMap.map_add, hx U, hy U]
  smul_mem' := by
    intro c x hx
    change (∀ U, purePairColorAction U x = x) at hx
    change ∀ U, purePairColorAction U (c • x) = c • x
    intro U
    rw [LinearMap.map_smul, hx U]

theorem purePairColorSignFlipMatrix_mulVec_apply
    (i : Fin 3) (a : Fin 3 → ℂ) :
    (purePairColorSignFlipMatrix i *ᵥ a) i = -a i := by
  fin_cases i <;>
    simp [purePairColorSignFlipMatrix, purePairColorSignDiagonal,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem mem_purePairColorFixedSubspace_iff
    (x : PurePairNormalModel) :
    x ∈ purePairColorFixedSubspace ↔ x.1 = 0 := by
  constructor
  · intro hx
    change ∀ U, purePairColorAction U x = x at hx
    funext i
    let U : Matrix.specialUnitaryGroup (Fin 3) ℂ :=
      ⟨purePairColorSignFlipMatrix i,
        purePairColorSignFlipMatrix_mem i⟩
    have hU := hx U
    have hi := congrFun (congrArg Prod.fst hU) i
    change (purePairColorSignFlipMatrix i *ᵥ x.1) i = x.1 i at hi
    rw [purePairColorSignFlipMatrix_mulVec_apply] at hi
    have hsum : x.1 i + x.1 i = 0 := by
      simpa only [hi] using neg_add_cancel (x.1 i)
    exact add_self_eq_zero.mp hsum
  · intro hx
    change ∀ U, purePairColorAction U x = x
    intro U
    rcases x with ⟨a, b⟩
    change a = 0 at hx
    subst a
    ext i <;> simp [purePairColorAction]

def purePairColorFixedEquivWeak :
    purePairColorFixedSubspace ≃ₗ[ℂ] ColorPreservingNormal where
  toFun x := x.1.2
  invFun b := ⟨(0, b), by
    rw [mem_purePairColorFixedSubspace_iff]⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact (mem_purePairColorFixedSubspace_iff x.1).mp x.2 |>.symm
    · rfl
  right_inv b := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

theorem finrank_purePairColorFixedSubspace_complex :
    Module.finrank ℂ purePairColorFixedSubspace = 2 := by
  rw [LinearEquiv.finrank_eq purePairColorFixedEquivWeak]
  exact finrank_colorPreservingNormal_complex

theorem finrank_purePairColorFixedSubspace_real :
    Module.finrank ℝ purePairColorFixedSubspace = 4 := by
  rw [← Module.finrank_mul_finrank ℝ ℂ purePairColorFixedSubspace,
    Complex.finrank_real_complex, finrank_purePairColorFixedSubspace_complex]

theorem purePair_normalActualityFracture :
    LinearMap.range purePairTangentAgreementDifferential = ⊤ ∧
      (∀ v : purePairTangentAtSecondSubmodule,
        purePairDisagreementReporter v.1 = 0) ∧
      Function.Surjective firstPurePairCartanDifferential ∧
      (∀ x : PurePairNormalModel,
        x ∈ purePairColorFixedSubspace ↔ x.1 = 0) ∧
      Module.finrank ℂ purePairColorFixedSubspace = 2 ∧
      Module.finrank ℝ purePairColorFixedSubspace = 4 ∧
      (∀ q x : EventQuaternion, inner ℝ q q = 1 →
        ∃! a : eventQuaternionImaginary,
          pointedTime q x • q + a.1 * q = x) := by
  refine ⟨purePairTangent_image_eq_agreement,
    purePairTangent_disagreement_eq_zero,
    firstPurePairCartanDifferential_surjective,
    mem_purePairColorFixedSubspace_iff,
    finrank_purePairColorFixedSubspace_complex,
    finrank_purePairColorFixedSubspace_real, ?_⟩
  intro q x hq
  exact pointedTime_smul_add_unique_quaternionLeftOrbitDirection q x hq

end GaloisForLFunctions.HTGeometry
