import GaloisForLFunctions.RHTower.Artin.ArtinVirtualCharacter
import Mathlib.LinearAlgebra.Trace

/-!
# The character on the range of a commuting idempotent

Let `σ` be a representation of a group `T` on `V` and `P` an idempotent endomorphism of `V`
commuting with every `σ(t)`. The range of `P` carries the representation
`t ↦ P ∘ σ(t)` (`rangeRepresentation`), and its character is `t ↦ tr(σ(t) P)`
(`rangeRepresentation_character`). So `t ↦ tr(σ(t) P)` is a character of `T`
(`trace_mul_idempotent_mem_fdCharacterSet`).
-/

noncomputable section

universe u w

namespace GaloisForLFunctions

variable {T : Type u} [Group T] {V : Type w} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ T V) (P : V →ₗ[ℂ] V)

/-- An idempotent fixes its range. -/
theorem idempotent_apply_of_mem_range (hP : P * P = P) (w : LinearMap.range P) :
    P (w : V) = w := by
  obtain ⟨v, hv⟩ := w.2
  rw [← hv]
  exact LinearMap.congr_fun hP v

/-- The representation on the range of an idempotent that commutes with the group:
`t ↦ P ∘ σ(t)`. -/
def rangeRepresentation (hP : P * P = P) (hcomm : ∀ t, σ t * P = P * σ t) :
    Representation ℂ T (LinearMap.range P) where
  toFun t := P.rangeRestrict ∘ₗ σ t ∘ₗ (LinearMap.range P).subtype
  map_one' := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    show P (σ 1 (w : V)) = w
    rw [map_one]
    exact idempotent_apply_of_mem_range P hP w
  map_mul' s t := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    show P (σ (s * t) (w : V)) = P (σ s (P (σ t (w : V))))
    rw [map_mul, show σ s (P (σ t (w : V))) = P (σ s (σ t (w : V))) from
      LinearMap.congr_fun (hcomm s) _]
    exact (LinearMap.congr_fun hP _).symm

theorem coe_rangeRepresentation_apply (hP : P * P = P) (hcomm : ∀ t, σ t * P = P * σ t) (t : T)
    (w : LinearMap.range P) : ((rangeRepresentation σ P hP hcomm t w : LinearMap.range P) : V) =
      P (σ t (w : V)) :=
  rfl

variable [FiniteDimensional ℂ V]

/-- **The character on the range of a commuting idempotent is `t ↦ tr(σ(t) P)`.** -/
theorem rangeRepresentation_character (hP : P * P = P) (hcomm : ∀ t, σ t * P = P * σ t)
    (t : T) : (rangeRepresentation σ P hP hcomm).character t = LinearMap.trace ℂ V (σ t * P) := by
  show LinearMap.trace ℂ _ (P.rangeRestrict ∘ₗ σ t ∘ₗ (LinearMap.range P).subtype) = _
  rw [LinearMap.trace_comp_comm' (σ t ∘ₗ (LinearMap.range P).subtype) P.rangeRestrict,
    LinearMap.comp_assoc]
  rfl

/-- **`t ↦ tr(σ(t) P)` is a character**, for an idempotent `P` commuting with the group. -/
theorem trace_mul_idempotent_mem_fdCharacterSet (hP : P * P = P)
    (hcomm : ∀ t, σ t * P = P * σ t) :
    (fun t => LinearMap.trace ℂ V (σ t * P)) ∈ fdCharacterSet T := by
  have h := representation_character_mem_fdCharacterSet T (rangeRepresentation σ P hP hcomm)
  have e : (rangeRepresentation σ P hP hcomm).character =
      fun t => LinearMap.trace ℂ V (σ t * P) :=
    funext (rangeRepresentation_character σ P hP hcomm)
  rwa [e] at h

end GaloisForLFunctions
