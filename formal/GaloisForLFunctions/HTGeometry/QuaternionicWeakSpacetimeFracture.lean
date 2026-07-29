import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Quaternionic parent of the weak-to-spacetime representation fracture

The real four-space of quaternions carries two natural actions of the unit quaternions:

* left multiplication, obtained from the left-factor embedding in
  `Spin(4) = SU(2) × SU(2)`;
* conjugation, obtained from the diagonal embedding.

This file proves the algebraic core without bundling the Lie groups.  The pair action

`(u, v) • q = u * q * star v`

restricts to left multiplication at `(u, 1)` and conjugation at `(u, u)`.  At the central
quaternion `-1`, the left action negates all four real directions while the diagonal action is
the identity.  The diagonal action preserves the scalar line and the three-dimensional imaginary
subspace, giving the exact real `1 + 3` splitting.

These are unconditional quaternion identities.  No identification with the Higgs, spacetime,
Lorentz signature, gravity, or an internal gauge force is assumed.
-/

open scoped Quaternion

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The real four-dimensional quaternion carrier. -/
abbrev EventQuaternion := ℍ[ℝ]

/-- Algebraic `Spin(4)` pair action before restricting to unit quaternions. -/
def spinFourPairAction (u v q : EventQuaternion) : EventQuaternion :=
  u * q * star v

/-- Restriction of the pair action to the left factor. -/
def quaternionLeftAction (u q : EventQuaternion) : EventQuaternion :=
  u * q

/-- Restriction of the pair action to the diagonal: quaternionic conjugation. -/
def quaternionDiagonalAction (u q : EventQuaternion) : EventQuaternion :=
  u * q * star u

/-- The pair formula composes with componentwise multiplication. -/
theorem spinFourPairAction_mul
    (u₁ v₁ u₂ v₂ q : EventQuaternion) :
    spinFourPairAction (u₁ * u₂) (v₁ * v₂) q =
      spinFourPairAction u₁ v₁ (spinFourPairAction u₂ v₂ q) := by
  simp only [spinFourPairAction, star_mul]
  noncomm_ring

/-- The identity pair acts trivially. -/
@[simp]
theorem spinFourPairAction_one (q : EventQuaternion) :
    spinFourPairAction 1 1 q = q := by
  simp [spinFourPairAction]

/-- The left-factor embedding gives left multiplication. -/
@[simp]
theorem spinFourPairAction_left (u q : EventQuaternion) :
    spinFourPairAction u 1 q = quaternionLeftAction u q := by
  simp [spinFourPairAction, quaternionLeftAction]

/-- The diagonal embedding gives quaternionic conjugation. -/
@[simp]
theorem spinFourPairAction_diagonal (u q : EventQuaternion) :
    spinFourPairAction u u q = quaternionDiagonalAction u q := by
  rfl

/-- The central element of the left factor reverses the whole real four-carrier. -/
theorem quaternionLeftAction_neg_one (q : EventQuaternion) :
    quaternionLeftAction (-1) q = -q := by
  apply Quaternion.ext <;>
    simp [quaternionLeftAction]

/-- A vector fixed by the central weak half-turn is zero. -/
theorem quaternionLeftAction_fixed_by_neg_one_eq_zero
    (q : EventQuaternion)
    (h : quaternionLeftAction (-1) q = q) :
    q = 0 := by
  rw [quaternionLeftAction_neg_one] at h
  have hq : q + q = 0 := by
    calc
      q + q = -q + q := by rw [h]
      _ = 0 := neg_add_cancel q
  have htwo : (2 : ℝ) • q = 0 := by
    simpa [two_smul ℝ q] using hq
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The incoming left-factor action has no nonzero vector fixed by every unit quaternion. -/
theorem quaternionLeftAction_common_unit_fixed_eq_zero
    (q : EventQuaternion)
    (h : ∀ u : EventQuaternion, Quaternion.normSq u = 1 →
      quaternionLeftAction u q = q) :
    q = 0 := by
  apply quaternionLeftAction_fixed_by_neg_one_eq_zero q
  apply h (-1)
  rw [Quaternion.normSq_neg, Quaternion.normSq_def]
  simp only [star_one, mul_one]
  change (1 : ℝ) = 1
  rfl

/-- The same central element in the diagonal subgroup acts trivially by conjugation. -/
theorem quaternionDiagonalAction_neg_one (q : EventQuaternion) :
    quaternionDiagonalAction (-1) q = q := by
  apply Quaternion.ext <;>
    simp [quaternionDiagonalAction]

/--
Exact central-character fracture on one real four-carrier: left-factor `-1` is `-id`, while
diagonal `-1` is `id`.
-/
theorem quaternionic_central_fracture (q : EventQuaternion) :
    quaternionLeftAction (-1) q = -q ∧
      quaternionDiagonalAction (-1) q = q :=
  ⟨quaternionLeftAction_neg_one q, quaternionDiagonalAction_neg_one q⟩

/-- Real-part projection as a linear map. -/
def eventQuaternionRe : EventQuaternion →ₗ[ℝ] ℝ :=
  QuaternionAlgebra.reₗ (-1 : ℝ) (0 : ℝ) (-1 : ℝ)

/-- The imaginary quaternion three-plane. -/
def eventQuaternionImaginary : Submodule ℝ EventQuaternion :=
  eventQuaternionRe.ker

/-- Membership in the imaginary subspace is exactly vanishing real part. -/
theorem mem_eventQuaternionImaginary_iff (q : EventQuaternion) :
    q ∈ eventQuaternionImaginary ↔ q.re = 0 := by
  rfl

/-- The imaginary quaternion subspace has real dimension three. -/
theorem finrank_eventQuaternionImaginary :
    Module.finrank ℝ eventQuaternionImaginary = 3 := by
  change Module.finrank ℝ eventQuaternionRe.ker = 3
  have hrange : eventQuaternionRe.range = ⊤ := LinearMap.range_eq_top.mpr (by
    intro r
    exact ⟨(r : EventQuaternion), rfl⟩)
  have hrangeDim : Module.finrank ℝ eventQuaternionRe.range = 1 := by
    rw [hrange, finrank_top]
    exact Module.finrank_self ℝ
  have hdim := eventQuaternionRe.finrank_range_add_finrank_ker
  rw [hrangeDim, Quaternion.finrank_eq_four] at hdim
  omega

/-- Inclusion of real scalars as the scalar quaternion line. -/
def eventQuaternionScalarEmbedding : ℝ →ₗ[ℝ] EventQuaternion where
  toFun r := (r : EventQuaternion)
  map_add' x y := by simp
  map_smul' x y := Quaternion.coe_smul x y

/-- The scalar quaternion line. -/
def eventQuaternionScalar : Submodule ℝ EventQuaternion :=
  eventQuaternionScalarEmbedding.range

/-- The scalar quaternion subspace has real dimension one. -/
theorem finrank_eventQuaternionScalar :
    Module.finrank ℝ eventQuaternionScalar = 1 := by
  change Module.finrank ℝ eventQuaternionScalarEmbedding.range = 1
  rw [LinearMap.finrank_range_of_inj]
  · exact Module.finrank_self ℝ
  · change Function.Injective (Quaternion.coe : ℝ → EventQuaternion)
    exact Quaternion.coe_injective

/-- Every quaternion is its scalar part plus its imaginary part. -/
theorem eventQuaternion_scalar_add_imaginary (q : EventQuaternion) :
    (q.re : EventQuaternion) + q.im = q :=
  Quaternion.re_add_im q

/-- The imaginary part of every quaternion lies in the three-plane. -/
theorem eventQuaternion_im_mem (q : EventQuaternion) :
    q.im ∈ eventQuaternionImaginary := by
  exact Quaternion.re_im q

/-- Conjugation scales the real part by quaternion norm squared. -/
theorem quaternionDiagonalAction_re (u q : EventQuaternion) :
    (quaternionDiagonalAction u q).re = Quaternion.normSq u * q.re := by
  simp [quaternionDiagonalAction, Quaternion.normSq_def', Quaternion.re_mul]
  ring

/-- Quaternionic conjugation preserves the imaginary three-plane. -/
theorem quaternionDiagonalAction_preserves_imaginary
    (u q : EventQuaternion) (hq : q ∈ eventQuaternionImaginary) :
    quaternionDiagonalAction u q ∈ eventQuaternionImaginary := by
  rw [mem_eventQuaternionImaginary_iff] at hq ⊢
  rw [quaternionDiagonalAction_re, hq, mul_zero]

/-- A unit quaternion fixes every point of the scalar line under diagonal conjugation. -/
theorem quaternionDiagonalAction_scalar
    (u : EventQuaternion) (r : ℝ) (hu : Quaternion.normSq u = 1) :
    quaternionDiagonalAction u (r : EventQuaternion) = (r : EventQuaternion) := by
  rw [quaternionDiagonalAction, ← Quaternion.coe_commutes, mul_assoc,
    Quaternion.self_mul_star, hu]
  simp

/--
The diagonal action has an invariant `1 + 3` decomposition: a pointwise-fixed scalar line and a
preserved three-dimensional imaginary subspace.
-/
theorem quaternionDiagonalAction_one_plus_three
    (u : EventQuaternion) (hu : Quaternion.normSq u = 1) :
    (∀ r : ℝ, quaternionDiagonalAction u (r : EventQuaternion) = (r : EventQuaternion)) ∧
      (∀ q ∈ eventQuaternionImaginary,
        quaternionDiagonalAction u q ∈ eventQuaternionImaginary) := by
  exact ⟨fun r => quaternionDiagonalAction_scalar u r hu,
    fun q hq => quaternionDiagonalAction_preserves_imaginary u q hq⟩

end GaloisForLFunctions.HTGeometry
