import GaloisForLFunctions.HTGeometry.AlgebraSpectrumCovering
import GaloisForLFunctions.HTGeometry.AlgebraCharpoly
import GaloisForLFunctions.HTGeometry.PowerMatrixCramer
import GaloisForLFunctions.HTGeometry.PowerDeterminantNonvanishing
import GaloisForLFunctions.HTGeometry.SplitAlgebraSeparation
import GaloisForLFunctions.HTGeometry.SplitParameterSeparability

/-!
# Complex points of a split fibre are distinct

If a family of complex points of an algebra is jointly surjective onto the coordinate space, the
points are pairwise distinct.  This turns the splitness hypothesis of the fibre into the
distinctness needed by `SplitAlgebraSeparation` and `SplitParameterSeparability`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {B : Type*} [CommRing B] [Algebra ℂ B]

/-- Distinct values of a separating family are witnessed by distinct complex points. -/
theorem injective_of_surjective_family {n : ℕ} (χ : Fin n → AlgSpec B)
    (hsurj : Function.Surjective fun b : B => fun i => (χ i b)) :
    Function.Injective χ := by
  intro i j hij
  by_contra hne
  obtain ⟨b, hb⟩ := hsurj (fun k => if k = i then 0 else 1)
  have h1 : χ i b = 0 := by have := congrFun hb i; simpa using this
  have hji : ¬ (j = i) := fun h => hne (h ▸ rfl)
  have h2 : χ j b = 1 := by
    have := congrFun hb j
    simpa [hji] using this
  rw [hij] at h1
  rw [h1] at h2
  exact zero_ne_one h2

end

end GaloisForLFunctions.HTGeometry
