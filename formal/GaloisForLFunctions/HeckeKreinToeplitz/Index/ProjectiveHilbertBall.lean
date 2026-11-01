import GaloisForLFunctions.HeckeKreinToeplitz.Index.OneNegativeDirection
import GaloisForLFunctions.HTGeometry.WeakHilbertCompactness

/-!
# Projective action on the weak Hilbert ball

Nonpositive lines in a space with one negative direction are represented by
`(z,1)` with `‖z‖ ≤ 1`. A form-preserving invertible operator acts by a
fractional linear map on this ball. Its denominator never vanishes, and the
action is weakly continuous.
-/

noncomputable section
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz.IndexOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The positive coordinate of the image of a normalized vector. -/
def firstAffine (T : (H × ℂ) →L[ℂ] (H × ℂ)) (x : WeakSpace ℂ H) : WeakSpace ℂ H :=
  toWeakSpace ℂ H (T ((toWeakSpace ℂ H).symm x, 1)).1

/-- The scalar coordinate of the image of a normalized vector. -/
def lastAffine (T : (H × ℂ) →L[ℂ] (H × ℂ)) (x : WeakSpace ℂ H) : ℂ :=
  (T ((toWeakSpace ℂ H).symm x, 1)).2

theorem continuous_firstAffine (T : (H × ℂ) →L[ℂ] (H × ℂ)) : Continuous (firstAffine T) := by
  let A : H →L[ℂ] H := (ContinuousLinearMap.fst ℂ H ℂ).comp
    (T.comp (ContinuousLinearMap.inl ℂ H ℂ))
  have he : firstAffine T = fun x => WeakSpace.map A x + toWeakSpace ℂ H (T (0, 1)).1 := by
    funext x
    change (T ((toWeakSpace ℂ H).symm x, 1)).1 =
      (T ((toWeakSpace ℂ H).symm x, 0)).1 + (T (0, 1)).1
    rw [show ((toWeakSpace ℂ H).symm x, (1 : ℂ)) =
      ((toWeakSpace ℂ H).symm x, 0) + (0, 1) by simp, map_add]
    rfl
  rw [he]
  exact (WeakSpace.map A).continuous.add continuous_const

theorem continuous_lastAffine (T : (H × ℂ) →L[ℂ] (H × ℂ)) : Continuous (lastAffine T) := by
  let l : H →L[ℂ] ℂ := (ContinuousLinearMap.snd ℂ H ℂ).comp
    (T.comp (ContinuousLinearMap.inl ℂ H ℂ))
  have he : lastAffine T = fun x => l ((toWeakSpace ℂ H).symm x) + (T (0, 1)).2 := by
    funext x
    change (T ((toWeakSpace ℂ H).symm x, 1)).2 =
      (T ((toWeakSpace ℂ H).symm x, 0)).2 + (T (0, 1)).2
    rw [show ((toWeakSpace ℂ H).symm x, (1 : ℂ)) =
      ((toWeakSpace ℂ H).symm x, 0) + (0, 1) by simp, map_add]
    rfl
  rw [he]
  exact (WeakBilin.eval_continuous (topDualPairing ℂ H).flip l).add continuous_const

variable (T : (H × ℂ) ≃L[ℂ] (H × ℂ))
  (hT : ∀ v w, pairing (T v) (T w) = pairing v w)

include hT

/-- The projective denominator cannot vanish on a nonpositive line. -/
theorem lastAffine_ne_zero (x : weakHilbertBall (H := H) 1) :
    lastAffine T.toContinuousLinearMap x.val ≠ 0 := by
  have hq : (pairing ((toWeakSpace ℂ H).symm x.val, (1 : ℂ))
      ((toWeakSpace ℂ H).symm x.val, 1)).re ≤ 0 :=
    (pairing_self_nonpos_iff _).mpr (by
      simpa only [weakHilbertBall, mem_setOf_eq, norm_one] using x.property)
  have hv : T ((toWeakSpace ℂ H).symm x.val, 1) ≠ 0 := by
    intro he
    exact one_ne_zero (congrArg Prod.snd (T.injective (he.trans (map_zero T).symm)))
  apply snd_ne_zero_of_nonpositive hv
  change (pairing (T ((toWeakSpace ℂ H).symm x.val, 1))
    (T ((toWeakSpace ℂ H).symm x.val, 1))).re ≤ 0
  rw [hT]
  exact hq

/-- A form-preserving operator maps the normalized nonpositive ball into itself. -/
theorem normalized_image_norm_le (x : weakHilbertBall (H := H) 1) :
    ‖(lastAffine T.toContinuousLinearMap x.val)⁻¹ •
      (T ((toWeakSpace ℂ H).symm x.val, 1)).1‖ ≤ 1 := by
  have hq : (pairing ((toWeakSpace ℂ H).symm x.val, (1 : ℂ))
      ((toWeakSpace ℂ H).symm x.val, 1)).re ≤ 0 :=
    (pairing_self_nonpos_iff _).mpr (by
      simpa only [weakHilbertBall, mem_setOf_eq, norm_one] using x.property)
  have hn := (pairing_self_nonpos_iff (T ((toWeakSpace ℂ H).symm x.val, 1))).mp
    (by rw [hT]; exact hq)
  rw [norm_smul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr (lastAffine_ne_zero T hT x)),
    mul_one]
  exact hn

/-- Fractional linear action on the weak Hilbert unit ball. -/
def ballAction : weakHilbertBall (H := H) 1 → weakHilbertBall (H := H) 1 := fun x =>
  ⟨(lastAffine T.toContinuousLinearMap x.val)⁻¹ • firstAffine T.toContinuousLinearMap x.val,
    normalized_image_norm_le T hT x⟩

theorem continuous_ballAction : Continuous (ballAction T hT) := by
  apply Continuous.subtype_mk
  exact (((continuous_lastAffine T.toContinuousLinearMap).comp continuous_subtype_val).inv₀
    (lastAffine_ne_zero T hT)).smul
      ((continuous_firstAffine T.toContinuousLinearMap).comp continuous_subtype_val)

/-- Normalizing a nonpositive image rescales the whole vector by its last coordinate. -/
theorem ballAction_normalized_vector (x : weakHilbertBall (H := H) 1) :
    ((toWeakSpace ℂ H).symm (ballAction T hT x).val, (1 : ℂ)) =
      (lastAffine T.toContinuousLinearMap x.val)⁻¹ • T ((toWeakSpace ℂ H).symm x.val, 1) := by
  apply Prod.ext
  · rfl
  · change (1 : ℂ) = (lastAffine T.toContinuousLinearMap x.val)⁻¹ *
      lastAffine T.toContinuousLinearMap x.val
    exact (inv_mul_cancel₀ (lastAffine_ne_zero T hT x)).symm

/-- A projective fixed point is a nonpositive eigenline of the original operator. -/
theorem eigenvector_of_ballAction_fixed {x : weakHilbertBall (H := H) 1}
    (hx : ballAction T hT x = x) :
    T ((toWeakSpace ℂ H).symm x.val, 1) =
      lastAffine T.toContinuousLinearMap x.val • ((toWeakSpace ℂ H).symm x.val, 1) := by
  have he := ballAction_normalized_vector T hT x
  rw [hx] at he
  have he' := congrArg (fun v : H × ℂ => lastAffine T.toContinuousLinearMap x.val • v) he
  rw [smul_inv_smul₀ (lastAffine_ne_zero T hT x)] at he'
  exact he'.symm

/-- Every isometry of a complete index-one space has a nonpositive eigenline. -/
theorem exists_normalized_nonpositive_eigenvector [CompleteSpace H] :
    ∃ z : H, ‖z‖ ≤ 1 ∧ ∃ a : ℂ, a ≠ 0 ∧ T (z, 1) = a • (z, 1) := by
  obtain ⟨x, hx⟩ := exists_fixedPoint_weakHilbert_convex
    (isCompact_weakHilbertBall (H := H) 1) (nonempty_weakHilbertBall zero_le_one)
    (convex_weakHilbertBall 1) (ballAction T hT) (continuous_ballAction T hT)
  exact ⟨(toWeakSpace ℂ H).symm x.val, x.property,
    lastAffine T.toContinuousLinearMap x.val, lastAffine_ne_zero T hT x,
    eigenvector_of_ballAction_fixed T hT hx⟩

end GaloisForLFunctions.HeckeKreinToeplitz.IndexOne
