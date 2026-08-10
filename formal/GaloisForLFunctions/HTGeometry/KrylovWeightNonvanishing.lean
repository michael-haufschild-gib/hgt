import GaloisForLFunctions.HTGeometry.EulerPrimeOrbitFourOrganLaw
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Cyclicity forces every weight to be nonzero

`EulerPrimeOrbitFourOrganLaw` proves the forward implication: distinct nodes and nowhere-vanishing
weights make the weighted Vandermonde (Krylov) family linearly independent.  The converse
implication is recorded here, and it needs no hypothesis on the nodes at all.

If one weight vanishes then every Krylov vector has a zero in that coordinate, so the whole family
lies in a hyperplane.  A family of `card ι` independent vectors in `ι → ℂ` is a basis, and a
coordinate functional cannot vanish on a basis.

This is the step "cyclicity makes every overlap nonzero" of a spectral argument: a cyclic vector
has nonzero component along every eigenvector.
-/

namespace GaloisForLFunctions.HTGeometry

namespace Krylov

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A vanishing weight destroys independence.** -/
theorem not_linearIndependent_of_weight_eq_zero {node weight : ι → ℂ} {i₀ : ι}
    (hw : weight i₀ = 0) :
    ¬ LinearIndependent ℂ (fun k : Fin (Fintype.card ι) =>
      finiteDiagonalKrylovVector node weight (k : ℕ)) := by
  intro hind
  haveI : Nonempty ι := ⟨i₀⟩
  haveI : Nonempty (Fin (Fintype.card ι)) :=
    Fin.pos_iff_nonempty.mp (Fintype.card_pos_iff.mpr ⟨i₀⟩)
  -- the family has as many members as the dimension, hence spans
  have hcard : Fintype.card (Fin (Fintype.card ι)) = Module.finrank ℂ (ι → ℂ) := by
    simp
  have hspan : Submodule.span ℂ
      (Set.range fun k : Fin (Fintype.card ι) =>
        finiteDiagonalKrylovVector node weight (k : ℕ)) = ⊤ :=
    hind.span_eq_top_of_card_eq_finrank hcard
  -- but every member has a zero in coordinate `i₀`
  have hzero : ∀ v ∈ Submodule.span ℂ
      (Set.range fun k : Fin (Fintype.card ι) =>
        finiteDiagonalKrylovVector node weight (k : ℕ)), v i₀ = 0 := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k, rfl⟩
      simp [finiteDiagonalKrylovVector, hw]
    · rfl
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro a x _ hx
      simp [hx]
  have hone : (Pi.single i₀ (1 : ℂ) : ι → ℂ) i₀ = 0 := by
    refine hzero _ ?_
    rw [hspan]
    exact Submodule.mem_top
  simp at hone

/-- **Cyclicity forces every weight to be nonzero.** -/
theorem weight_ne_zero_of_linearIndependent {node weight : ι → ℂ}
    (hind : LinearIndependent ℂ (fun k : Fin (Fintype.card ι) =>
      finiteDiagonalKrylovVector node weight (k : ℕ))) (i : ι) :
    weight i ≠ 0 := fun hw => not_linearIndependent_of_weight_eq_zero hw hind

end Krylov

end GaloisForLFunctions.HTGeometry
