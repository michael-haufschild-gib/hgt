import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Full formation idempotence defect in a topologically simple ring

This module isolates the algebraic core of `ULF-PHFI-001`.  In a topological ring whose only
closed two-sided ideals are zero and the whole ring, a continuous multiplicative map that kills
one nonzero element is zero.  Applied to `d(T)=T-T²`, any idempotent image of a nonidempotent
formation operator forces the complete source map to vanish.

No positivity, unit, star operation, trace, or norm contractivity is assumed.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- A possibly nonunital topological ring is topologically simple when its only closed two-sided
ideals are zero and the whole ring. -/
class IsTopologicallySimpleRing (A : Type*) [TopologicalSpace A]
    [NonUnitalNonAssocRing A] : Prop where
  eq_bot_or_eq_top : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [NonUnitalRing A] [NonUnitalRing B] [T1Space B]

/-- Failure of a formed source element to be an idempotent completed event. -/
def formationIdempotenceDefect (T : A) : A := T - T * T

/-- Kernel ideal of a possibly nonunital ring homomorphism. -/
def nonUnitalRingHomKernelIdeal (f : A →ₙ+* B) : TwoSidedIdeal A :=
  (⊥ : TwoSidedIdeal B).comap f

/-- Continuity makes the kernel ideal closed. -/
theorem isClosed_nonUnitalRingHomKernelIdeal (f : A →ₙ+* B) (hf : Continuous f) :
    IsClosed ((nonUnitalRingHomKernelIdeal f : TwoSidedIdeal A) : Set A) := by
  have hset : ((nonUnitalRingHomKernelIdeal f : TwoSidedIdeal A) : Set A) =
      f ⁻¹' ({0} : Set B) := by
    ext x
    simp [nonUnitalRingHomKernelIdeal, TwoSidedIdeal.mem_comap]
  rw [hset]
  exact isClosed_singleton.preimage hf

/-- Killing one nonzero source element kills a continuous multiplicative map out of a
topologically simple ring. -/
theorem nonUnitalRingHom_eq_zero_of_maps_nonzero_to_zero
    [IsTopologicallySimpleRing A] (f : A →ₙ+* B) (hf : Continuous f)
    (d : A) (hd : d ≠ 0) (hfd : f d = 0) :
    ∀ x, f x = 0 := by
  let I := nonUnitalRingHomKernelIdeal f
  have hdI : d ∈ I := by
    simp [I, nonUnitalRingHomKernelIdeal, TwoSidedIdeal.mem_comap, hfd]
  have hI_ne : I ≠ ⊥ := by
    intro hI
    have : d ∈ (⊥ : TwoSidedIdeal A) := hI ▸ hdI
    exact hd (by simpa using this)
  have hI_top : I = ⊤ :=
    (IsTopologicallySimpleRing.eq_bot_or_eq_top I
      (isClosed_nonUnitalRingHomKernelIdeal f hf)).resolve_left hI_ne
  intro x
  have hxI : x ∈ I := by rw [hI_top]; simp
  simpa [I, nonUnitalRingHomKernelIdeal, TwoSidedIdeal.mem_comap] using hxI

/-- **Bounded/continuous multiplicative horizon exclusion.**  If `T-T²` is nonzero, every
continuous multiplicative map from a topologically simple formation ring whose image of `T` is
idempotent vanishes on the whole source ring. -/
theorem nonUnitalRingHom_idempotent_image_forces_zero
    [IsTopologicallySimpleRing A] (f : A →ₙ+* B) (hf : Continuous f)
    (T : A) (hdefect : formationIdempotenceDefect T ≠ 0)
    (hidem : f T * f T = f T) :
    ∀ x, f x = 0 := by
  apply nonUnitalRingHom_eq_zero_of_maps_nonzero_to_zero f hf
    (formationIdempotenceDefect T) hdefect
  simp [formationIdempotenceDefect, map_sub, map_mul, hidem]

/-- Closed theorem package for the formation-to-event defect: idempotent image implies both
source-map extinction and zero image of the formed object. -/
theorem topologicallySimpleFormationIdempotenceDefect_closed
    [IsTopologicallySimpleRing A] (f : A →ₙ+* B) (hf : Continuous f)
    (T : A) (hdefect : formationIdempotenceDefect T ≠ 0)
    (hidem : f T * f T = f T) :
    (∀ x, f x = 0) ∧ f T = 0 := by
  have hzero := nonUnitalRingHom_idempotent_image_forces_zero f hf T hdefect hidem
  exact ⟨hzero, hzero T⟩

end GaloisForLFunctions.HTGeometry
