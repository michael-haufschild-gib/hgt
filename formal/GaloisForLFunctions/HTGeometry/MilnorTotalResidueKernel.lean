import GaloisForLFunctions.HTGeometry.MilnorGradedInjectivity

/-!
# The kernel of the total residue is the constants

A class of `K_n^M(F(t))` whose residue vanishes at every finite place lies at the bottom of Milnor's
degree filtration, hence comes from `K_n^M(F)`.  Descending the filtration one degree at a time is
exactly the graded injectivity statement.

Together with the surjectivity of the total residue this is the exactness of

`0 → K_n^M(F) → K_n^M(F(t)) --(⊕ ∂_π)--> ⊕_π K_{n−1}^M(F[X]/π) → 0`.

* `mem_degreeFiltration_zero_of_residues_zero` : the class lies in `L_0`.
* `mem_range_of_residues_zero` : **it is the image of a class of `K_n^M(F)`.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F]

/-- A class with vanishing residues everywhere lies at the bottom of the degree filtration. -/
theorem mem_degreeFiltration_zero_of_residues_zero (n : ℕ) :
    ∀ (d : ℕ) (x : MilnorKDeg (RatFunc F) (n + 1)),
      x ∈ degreeFiltration (F := F) d (n + 1) →
      (∀ (π : Polynomial F) (hπ : Irreducible π), π.Monic →
        milnorResidue (polyResidueData hπ) (n + 1) x = 0) →
      x ∈ degreeFiltration (F := F) 0 (n + 1) := by
  intro d
  induction d with
  | zero => intro x hx _; exact hx
  | succ d ih =>
      intro x hx hres
      have hstep := mem_degreeFiltration_pred_of_residues_zero (F := F) (d := d + 1) (n := n)
        (by omega) hx (fun p => hres p.1 p.2.1 p.2.2.2)
      simp only [Nat.add_sub_cancel] at hstep
      exact ih x hstep hres

/-- **The kernel of the total residue is the image of `K_n^M(F)`.**  This is the left exactness of
Milnor's sequence for a rational function field, in every degree, for every field. -/
theorem mem_range_of_residues_zero (n : ℕ) (x : MilnorKDeg (RatFunc F) (n + 1))
    (hres : ∀ (π : Polynomial F) (hπ : Irreducible π), π.Monic →
      milnorResidue (polyResidueData hπ) (n + 1) x = 0) :
    x ∈ AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) (n + 1)) := by
  obtain ⟨d, hd⟩ := exists_mem_degreeFiltration (F := F) (n + 1) x
  exact degreeFiltration_zero_le_range (F := F) (n + 1)
    (mem_degreeFiltration_zero_of_residues_zero n d x hd hres)

end GaloisForLFunctions.HTGeometry
