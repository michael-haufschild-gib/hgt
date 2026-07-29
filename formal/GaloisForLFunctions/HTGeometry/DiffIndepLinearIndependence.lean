import GaloisForLFunctions.HTGeometry.DifferentialMatroidFoundations

/-!
# Differential independence is linear independence at order zero

A differentially independent family is algebraically independent in all its jets, and the order-zero
jets are the family itself.  Restricting the algebraic independence along `x ↦ (x, 0)` therefore
gives ordinary linear independence, together with injectivity of the family.

* **`linearIndependent_of_differentialIndependent`**, **`linearIndependent_of_diffIndepOn`**;
* `injective_of_differentialIndependent`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [Differential K]

/-- A differentially independent family is linearly independent over the base. -/
theorem linearIndependent_of_differentialIndependent {ι : Type*} {x : ι → K}
    (h : DifferentialIndependent k x) : LinearIndependent k x := by
  have hcomp := h.linearIndependent.comp (fun i : ι => (i, 0))
    (fun i j hij => congrArg Prod.fst hij)
  have hfun :
      ((fun p : ι × ℕ => differentialJet p.2 (x p.1)) ∘ fun i => (i, 0)) = x := by
    funext i
    rfl
  rw [hfun] at hcomp
  exact hcomp

/-- A differentially independent family is injective. -/
theorem injective_of_differentialIndependent {ι : Type*} {x : ι → K}
    (h : DifferentialIndependent k x) : Function.Injective x :=
  (linearIndependent_of_differentialIndependent h).injective

/-- A differentially independent set is linearly independent. -/
theorem linearIndependent_of_diffIndepOn {s : Set K} (h : DiffIndepOn k s) :
    LinearIndependent k (Subtype.val : s → K) :=
  linearIndependent_of_differentialIndependent h

end GaloisForLFunctions.HTGeometry
