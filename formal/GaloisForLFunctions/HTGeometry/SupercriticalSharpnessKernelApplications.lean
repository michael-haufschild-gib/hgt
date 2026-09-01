import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.HTGeometry.KernelNestedFiniteSectionInertia

/-!
# Supercritical-sharpness mechanisms for nested kernel sections

Closed applications of the sequential-touch alternative from arXiv:2603.03257 to the corpus's
nested Hermitian kernel matrices.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Over any finite block of newly sampled kernel points, negative inertia either gains at least
one unit per point in aggregate, or some single enlargement adds no negative direction. -/
theorem kernelFiniteSectionNegIndex_grows_or_exists_stall
    {X : Type*} (K : X → X → ℂ) (z : ℕ → X) (N t : ℕ) :
    kernelFiniteSectionNegIndex K z N + t ≤ kernelFiniteSectionNegIndex K z (N + t) ∨
      ∃ i < t,
        kernelFiniteSectionNegIndex K z (N + (i + 1)) =
          kernelFiniteSectionNegIndex K z (N + i) := by
  have hmono : Monotone (fun i ↦ kernelFiniteSectionNegIndex K z (N + i)) := by
    intro i j hij
    exact kernelFiniteSectionNegIndex_monotone K z (Nat.add_le_add_left hij N)
  simpa [Nat.add_assoc] using
    (accumulates_touches_or_exists_stall
      (fun i ↦ kernelFiniteSectionNegIndex K z (N + i)) t hmono)

end GaloisForLFunctions.HTGeometry
