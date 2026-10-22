import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Exact and almost-complemented polarization legs

A polarization leg is a pair `(ι, π)` of maps between a source and an ambient space.  When
`π ∘ ι = 1` the composite `ι ∘ π` is an honest idempotent, its range is the range of `ι`, and the
ambient space splits.  When `π ∘ ι` is only `1` plus a defect, `ι ∘ π` is idempotent exactly when
the transported defect vanishes; in general its idempotence defect is the transported defect, so it
is idempotent modulo any class of operators closed under composition on both sides — for instance a
trace ideal.

The reason the distinction matters is the last statement: exact idempotence of the almost-leg,
together with surjectivity of `π ∘ ι`, *produces* a topological complement of the range of `ι`.  So
assuming the almost-leg is a projection is not a normalization; it is a complementation statement.

* `deningerExactLeg_isIdempotent`, `_range`, `_isCompl` : the exact leg.
* `deningerAlmostLeg_defect`, `_isIdempotent_iff` : the idempotence defect of the almost-leg.
* `deningerAlmostLeg_defect_mem` : it lies in any two-sided class containing the defect.
* `deningerAlmostLeg_isCompl_of_isIdempotent` : exact idempotence complements the range.
-/

namespace RHTower

section PolarizationLegs

variable {R W H : Type*} [Ring R]
variable [AddCommGroup W] [Module R W] [AddCommGroup H] [Module R H]

/-- The leg operator attached to an embedding and a retraction. -/
def deningerLeg (iota : H →ₗ[R] W) (pi : W →ₗ[R] H) : W →ₗ[R] W := iota ∘ₗ pi

theorem deningerLeg_apply (iota : H →ₗ[R] W) (pi : W →ₗ[R] H) (w : W) :
    deningerLeg iota pi w = iota (pi w) := rfl

/-- **The exact leg is an idempotent.**  A retraction of the embedding makes the leg operator a
projection. -/
theorem deningerExactLeg_isIdempotent {iota : H →ₗ[R] W} {pi : W →ₗ[R] H}
    (h : pi ∘ₗ iota = LinearMap.id) :
    deningerLeg iota pi ∘ₗ deningerLeg iota pi = deningerLeg iota pi := by
  refine LinearMap.ext fun w => ?_
  show iota (pi (iota (pi w))) = iota (pi w)
  have := LinearMap.congr_fun h (pi w)
  rw [LinearMap.comp_apply] at this
  rw [this]
  rfl

/-- **The exact leg projects onto the source.** -/
theorem deningerExactLeg_range {iota : H →ₗ[R] W} {pi : W →ₗ[R] H}
    (h : pi ∘ₗ iota = LinearMap.id) :
    LinearMap.range (deningerLeg iota pi) = LinearMap.range iota := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    exact ⟨pi w, rfl⟩
  · rintro _ ⟨y, rfl⟩
    refine ⟨iota y, ?_⟩
    show iota (pi (iota y)) = iota y
    have := LinearMap.congr_fun h y
    rw [LinearMap.comp_apply] at this
    rw [this]
    rfl

/-- **The exact leg splits the ambient space.** -/
theorem deningerExactLeg_isCompl {iota : H →ₗ[R] W} {pi : W →ₗ[R] H}
    (h : pi ∘ₗ iota = LinearMap.id) :
    IsCompl (LinearMap.ker (deningerLeg iota pi)) (LinearMap.range iota) := by
  rw [← deningerExactLeg_range h]
  exact IsCompl.symm (LinearMap.IsIdempotentElem.isCompl (deningerExactLeg_isIdempotent h))

/-- **The idempotence defect of a leg is the transported defect of its retraction.** -/
theorem deningerAlmostLeg_defect (iota : H →ₗ[R] W) (pi : W →ₗ[R] H) :
    deningerLeg iota pi ∘ₗ deningerLeg iota pi - deningerLeg iota pi
      = iota ∘ₗ (pi ∘ₗ iota - LinearMap.id) ∘ₗ pi := by
  refine LinearMap.ext fun w => ?_
  show iota (pi (iota (pi w))) - iota (pi w)
      = iota ((pi ∘ₗ iota - LinearMap.id : H →ₗ[R] H) (pi w))
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub]

/-- **A leg is idempotent exactly when its transported defect vanishes.** -/
theorem deningerAlmostLeg_isIdempotent_iff (iota : H →ₗ[R] W) (pi : W →ₗ[R] H) :
    deningerLeg iota pi ∘ₗ deningerLeg iota pi = deningerLeg iota pi
      ↔ iota ∘ₗ (pi ∘ₗ iota - LinearMap.id) ∘ₗ pi = 0 := by
  rw [← deningerAlmostLeg_defect, sub_eq_zero]

/-- **Idempotence modulo a two-sided class.**  If the retraction defect belongs to a class of
operators closed under composition with the embedding and the retraction — a trace ideal, for
instance — then so does the idempotence defect of the leg.  This is the exact sense in which the
almost-complemented leg is a projection. -/
theorem deningerAlmostLeg_defect_mem (iota : H →ₗ[R] W) (pi : W →ₗ[R] H)
    (N : (H →ₗ[R] H) → Prop) (M : (W →ₗ[R] W) → Prop)
    (hideal : ∀ n : H →ₗ[R] H, N n → M (iota ∘ₗ n ∘ₗ pi))
    (hdefect : N (pi ∘ₗ iota - LinearMap.id)) :
    M (deningerLeg iota pi ∘ₗ deningerLeg iota pi - deningerLeg iota pi) := by
  rw [deningerAlmostLeg_defect]
  exact hideal _ hdefect

/-- **The cutoff shape of the retraction defect.**  If the retraction composes to `1` plus a cutoff
minus its conjugate, and the class is closed under differences and under the conjugation, then the
defect belongs to the class. -/
theorem deningerAlmostLeg_defect_of_cutoff (iota : H →ₗ[R] W) (pi : W →ₗ[R] H)
    (N : (H →ₗ[R] H) → Prop) (cutoff conj : H →ₗ[R] H)
    (hshape : pi ∘ₗ iota = LinearMap.id + cutoff - conj)
    (hcutoff : N cutoff) (hconj : N conj)
    (hsub : ∀ a b : H →ₗ[R] H, N a → N b → N (a - b)) :
    N (pi ∘ₗ iota - LinearMap.id) := by
  have hrw : pi ∘ₗ iota - LinearMap.id = cutoff - conj := by
    rw [hshape, add_comm (LinearMap.id : H →ₗ[R] H) cutoff, sub_right_comm,
      add_sub_cancel_right]
  rw [hrw]
  exact hsub _ _ hcutoff hconj

/-- **Exact idempotence of an almost-leg complements the range of the embedding.**  If the leg is a
genuine idempotent and the retraction composite is onto, then the range of the embedding has the
kernel of the leg as a complement.  Assuming exact idempotence therefore asserts a
complementation, not a normalization. -/
theorem deningerAlmostLeg_isCompl_of_isIdempotent {iota : H →ₗ[R] W} {pi : W →ₗ[R] H}
    (hidem : deningerLeg iota pi ∘ₗ deningerLeg iota pi = deningerLeg iota pi)
    (hsurj : Function.Surjective (pi ∘ₗ iota)) :
    IsCompl (LinearMap.ker (deningerLeg iota pi)) (LinearMap.range iota) := by
  have hrange : LinearMap.range (deningerLeg iota pi) = LinearMap.range iota := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨w, rfl⟩
      exact ⟨pi w, rfl⟩
    · rintro _ ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := hsurj y
      refine ⟨iota z, ?_⟩
      show iota (pi (iota z)) = iota y
      rw [show pi (iota z) = (pi ∘ₗ iota) z from rfl, hz]
  rw [← hrange]
  exact IsCompl.symm (LinearMap.IsIdempotentElem.isCompl hidem)

end PolarizationLegs

section Nonvacuous

variable {S : Type*} [CommRing S]

/-- Almost-legs with nonzero defect exist: the scalar retraction `c` has defect `c - 1`. -/
theorem deningerScalarLeg_defect (c : S) :
    (LinearMap.id : S →ₗ[S] S) ∘ₗ (c • (LinearMap.id : S →ₗ[S] S)) - LinearMap.id
      = (c - 1) • (LinearMap.id : S →ₗ[S] S) := by
  refine LinearMap.ext fun x => ?_
  show c * x - x = (c - 1) * x
  ring

/-- The scalar leg is idempotent exactly when its scalar is. -/
theorem deningerScalarLeg_isIdempotent_iff (c : S) :
    deningerLeg (LinearMap.id : S →ₗ[S] S) (c • (LinearMap.id : S →ₗ[S] S))
        ∘ₗ deningerLeg (LinearMap.id : S →ₗ[S] S) (c • (LinearMap.id : S →ₗ[S] S))
        = deningerLeg (LinearMap.id : S →ₗ[S] S) (c • (LinearMap.id : S →ₗ[S] S))
      ↔ c * c = c := by
  constructor
  · intro h
    have hone : c * (c * (1 : S)) = c * (1 : S) := LinearMap.congr_fun h 1
    calc c * c = c * (c * (1 : S)) := by rw [mul_one]
      _ = c * (1 : S) := hone
      _ = c := mul_one c
  · intro h
    refine LinearMap.ext fun x => ?_
    show c * (c * x) = c * x
    rw [← mul_assoc, h]

end Nonvacuous

end RHTower
