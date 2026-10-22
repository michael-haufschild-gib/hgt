import GaloisForLFunctions.HTGeometry.PurePairNormalFracture
import GaloisForLFunctions.HTGeometry.HiggsCausalOrbit
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Normal fibers and color stabilizer at a compatible Spin(10) pure-spinor pair

In the even-form chart `ℂ × Λ²ℂ⁵ × Λ⁴ℂ⁵` (scalar, skew matrix, five four-form coordinates) the
linearized Cartan pure-spinor equations at the pair `1` and `e⁴ ∧ e⁵` are packaged as linear maps.
The tangent space to the Cartan locus at `e⁴ ∧ e⁵` maps onto the agreement space `ℂ³` (first three
four-form coordinates) with zero disagreement part, so its compatibility quotient is `ℂ³`. The
linearized Cartan map at `1` is the four-form coordinate split as `ℂ³ × ℂ²`; it is surjective, so
the normal fiber at `1` is `ℂ³ × ℂ²`. Letting `SU(3)` act on the `ℂ³` factor, the fixed subspace is
exactly `0 × ℂ²`, of complex dimension 2 and real dimension 4.

## Main results

- `purePairTangentCompatibilityQuotientEquivAgreement`: the tangent space at `e⁴ ∧ e⁵` modulo the
  kernel of the agreement differential is linearly isomorphic to `ℂ³`.
- `purePairTangent_disagreement_eq_zero`: tangent variations at `e⁴ ∧ e⁵` have zero disagreement
  reporter.
- `firstPurePairProjectiveNormalFiberEquiv`: the chart modulo the kernel of the linearized Cartan
  map at `1` is linearly isomorphic to `ℂ³ × ℂ²`.
- `mem_purePairColorFixedSubspace_iff`: a vector of `ℂ³ × ℂ²` is fixed by every element of `SU(3)`
  iff its `ℂ³` component is zero.
- `finrank_purePairColorFixedSubspace_complex`, `finrank_purePairColorFixedSubspace_real`: the
  fixed subspace has dimension 2 over `ℂ` and 4 over `ℝ`.
- `purePair_normalActualityFracture`: the conjunction of these facts with the unique decomposition
  `x = ⟪q, x⟫ q + a q`, `a` purely imaginary, for a unit quaternion `q`.

## Hypotheses

All results are unconditional linear algebra on explicit coordinates. The only premise is
`inner ℝ q q = 1` (a unit quaternion) in the quaternion clause of
`purePair_normalActualityFracture`. No physical interpretation is asserted.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The agreement normal space `ℂ³` (first three four-form coordinates). -/
abbrev PurePairAgreementNormal := Fin 3 → ℂ

/-- Model normal space `ℂ³ × ℂ²`: agreement part times the color-preserving doublet. -/
abbrev PurePairNormalModel := PurePairAgreementNormal × ColorPreservingNormal

/-- The linear isomorphism `ℂ⁵ ≃ ℂ³ × ℂ²` splitting off the first three coordinates. -/
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

/-- The agreement reporter (first three four-form coordinates) as a `ℂ`-linear map on the chart. -/
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

/-- Linear constraint map at `e⁴ ∧ e⁵`: the two-form entries `(0,1), (0,2), (1,2)` and the
four-form entries `3, 4`; its kernel is the Cartan tangent space there. -/
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

/-- Tangent space to the Cartan pure-spinor locus at the second spinor `e⁴ ∧ e⁵`. -/
def purePairTangentAtSecondSubmodule : Submodule ℂ SpinTenEvenCoordinate :=
  LinearMap.ker secondPurePairTangentConstraintDifferential

/-- Membership in the tangent submodule is exactly the linearized Cartan system at `e⁴ ∧ e⁵`. -/
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

/-- The agreement reporter restricted to the tangent space at `e⁴ ∧ e⁵`. -/
def purePairTangentAgreementDifferential :
    purePairTangentAtSecondSubmodule →ₗ[ℂ] PurePairAgreementNormal :=
  purePairAgreementDifferential.domRestrict purePairTangentAtSecondSubmodule

/-- Every agreement vector in `ℂ³` is the agreement reporter of some tangent variation at
`e⁴ ∧ e⁵`. -/
theorem purePairTangentAgreementDifferential_surjective :
    Function.Surjective purePairTangentAgreementDifferential := by
  intro c
  refine ⟨⟨pureTangentVariationOfAgreement c,
    (mem_purePairTangentAtSecondSubmodule_iff _).mpr
      (pureTangentVariationOfAgreement_is_tangent c)⟩, ?_⟩
  exact purePairAgreementReporter_variationOfAgreement c

/-- Tangent variations at `e⁴ ∧ e⁵` with zero agreement reporter. -/
abbrev PurePairJointlyPureTangentAtSecond :=
  LinearMap.ker purePairTangentAgreementDifferential

/-- The tangent space at `e⁴ ∧ e⁵` modulo the agreement-silent tangent variations. -/
abbrev PurePairTangentCompatibilityQuotient :=
  purePairTangentAtSecondSubmodule ⧸ PurePairJointlyPureTangentAtSecond

/-- The range of the tangent agreement differential is all of `ℂ³`, as a linear equivalence. -/
def purePairTangentAgreementRangeEquiv :
    LinearMap.range purePairTangentAgreementDifferential ≃ₗ[ℂ]
      PurePairAgreementNormal :=
  LinearEquiv.ofBijective
    (LinearMap.range purePairTangentAgreementDifferential).subtype
    ⟨Submodule.subtype_injective _, by
      intro c
      obtain ⟨v, hv⟩ := purePairTangentAgreementDifferential_surjective c
      exact ⟨⟨c, ⟨v, hv⟩⟩, rfl⟩⟩

/-- First isomorphism theorem: the tangent compatibility quotient at `e⁴ ∧ e⁵` is `ℂ³`. -/
def purePairTangentCompatibilityQuotientEquivAgreement :
    PurePairTangentCompatibilityQuotient ≃ₗ[ℂ] PurePairAgreementNormal :=
  (LinearMap.quotKerEquivRange purePairTangentAgreementDifferential).trans
    purePairTangentAgreementRangeEquiv

/-- The tangent agreement differential has full range `ℂ³`. -/
theorem purePairTangent_image_eq_agreement :
    LinearMap.range purePairTangentAgreementDifferential = ⊤ := by
  exact LinearMap.range_eq_top.mpr
    purePairTangentAgreementDifferential_surjective

/-- Every tangent variation at `e⁴ ∧ e⁵` has zero disagreement reporter (four-form
coordinates 3 and 4). -/
theorem purePairTangent_disagreement_eq_zero
    (v : purePairTangentAtSecondSubmodule) :
    purePairDisagreementReporter v.1 = 0 := by
  apply purePairDisagreementReporter_eq_zero_of_tangent v.1
  exact (mem_purePairTangentAtSecondSubmodule_iff v.1).mp v.property

/-- Linearized Cartan map at the first spinor `1`: the four-form coordinate, split as
`ℂ³ × ℂ²`. -/
def firstPurePairCartanDifferential :
    SpinTenEvenCoordinate →ₗ[ℂ] PurePairNormalModel where
  toFun v := purePairNormalSplit (spinTenFour v)
  map_add' x y := by
    simp [spinTenFour]
  map_smul' c x := by
    simp [spinTenFour]

/-- The linearized Cartan map at `1` is the pair (agreement reporter, disagreement reporter). -/
theorem firstPurePairCartanDifferential_eq_reporters
    (v : SpinTenEvenCoordinate) :
    firstPurePairCartanDifferential v =
      (purePairAgreementReporter v, purePairDisagreementReporter v) := by
  ext i <;> fin_cases i <;>
    simp [firstPurePairCartanDifferential, purePairNormalSplit,
      purePairAgreementReporter, purePairDisagreementReporter,
      firstPairVectorReporter, spinTenFour]

/-- The Cartan polarization at `1` has upper part equal to the linearized Cartan map (after the
`ℂ³ × ℂ²` split) and vanishing lower part. -/
theorem firstPurePairCartanDifferential_eq_cartanPolar
    (v : SpinTenEvenCoordinate) :
    purePairNormalSplit (spinTenCartanPolar firstPurePairSpinor v).1 =
        firstPurePairCartanDifferential v ∧
      (spinTenCartanPolar firstPurePairSpinor v).2 = 0 := by
  constructor
  · rw [firstPairVectorReporter_eq_cartanPolar_upper]
    rfl
  · exact firstPair_cartanPolar_lower_eq_zero v

/-- The linearized Cartan map at `1` is surjective onto `ℂ³ × ℂ²`. -/
theorem firstPurePairCartanDifferential_surjective :
    Function.Surjective firstPurePairCartanDifferential := by
  rintro ⟨a, b⟩
  refine ⟨(0, 0, ![a 0, a 1, a 2, b 0, b 1]), ?_⟩
  ext i <;> fin_cases i <;>
    simp [firstPurePairCartanDifferential, purePairNormalSplit, spinTenFour]

/-- The kernel of the linearized Cartan map at `1` is exactly the zero set of the full Cartan
polarization at `1`. -/
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

/-- Normal fiber at `1`: the chart modulo the kernel of the linearized Cartan map. -/
abbrev FirstPurePairProjectiveNormalFiber :=
  SpinTenEvenCoordinate ⧸ LinearMap.ker firstPurePairCartanDifferential

/-- The range of the linearized Cartan map at `1` is all of `ℂ³ × ℂ²`. -/
def firstPurePairCartanDifferentialRangeEquiv :
    LinearMap.range firstPurePairCartanDifferential ≃ₗ[ℂ]
      PurePairNormalModel :=
  LinearEquiv.ofBijective
    (LinearMap.range firstPurePairCartanDifferential).subtype
    ⟨Submodule.subtype_injective _, by
      intro y
      obtain ⟨v, hv⟩ := firstPurePairCartanDifferential_surjective y
      exact ⟨⟨y, ⟨v, hv⟩⟩, rfl⟩⟩

/-- First isomorphism theorem: the normal fiber at `1` is linearly isomorphic to `ℂ³ × ℂ²`. -/
def firstPurePairProjectiveNormalFiberEquiv :
    FirstPurePairProjectiveNormalFiber ≃ₗ[ℂ] PurePairNormalModel :=
  (LinearMap.quotKerEquivRange firstPurePairCartanDifferential).trans
    firstPurePairCartanDifferentialRangeEquiv

/-- Diagonal of a determinant-one sign matrix negating coordinate `i` and one other
coordinate of `ℂ³`. -/
def purePairColorSignDiagonal (i : Fin 3) : Fin 3 → ℂ :=
  match i with
  | ⟨0, _⟩ => ![-1, -1, 1]
  | ⟨1, _⟩ => ![1, -1, -1]
  | ⟨2, _⟩ => ![-1, 1, -1]

def purePairColorSignFlipMatrix (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (purePairColorSignDiagonal i)

/-- The sign-flip diagonal matrix lies in the special unitary group `SU(3)`. -/
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

/-- `SU(3)` acts on `ℂ³ × ℂ²` by matrix multiplication on the `ℂ³` factor and trivially on
`ℂ²`. -/
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

/-- The subspace of `ℂ³ × ℂ²` fixed by every element of `SU(3)`. -/
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

/-- A vector is `SU(3)`-fixed iff its `ℂ³` component is zero; the sign-flip matrices already
force each coordinate to vanish. -/
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

/-- The `SU(3)`-fixed subspace is linearly isomorphic to the color-preserving doublet `ℂ²`. -/
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

/-- The `SU(3)`-fixed subspace has complex dimension 2. -/
theorem finrank_purePairColorFixedSubspace_complex :
    Module.finrank ℂ purePairColorFixedSubspace = 2 := by
  rw [LinearEquiv.finrank_eq purePairColorFixedEquivWeak]
  exact finrank_colorPreservingNormal_complex

/-- The `SU(3)`-fixed subspace has real dimension 4. -/
theorem finrank_purePairColorFixedSubspace_real :
    Module.finrank ℝ purePairColorFixedSubspace = 4 := by
  rw [← Module.finrank_mul_finrank ℝ ℂ purePairColorFixedSubspace,
    Complex.finrank_real_complex, finrank_purePairColorFixedSubspace_complex]

/-- Summary: tangent agreement differential onto `ℂ³` with zero disagreement, surjective Cartan
map at `1`, `SU(3)`-fixed subspace `0 × ℂ²` of dimensions 2 over `ℂ` and 4 over `ℝ`, and, for
a unit quaternion `q`, unique decomposition `x = ⟪q, x⟫ q + a q` with `a` purely imaginary. -/
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
