import GaloisForLFunctions.HTGeometry.IsogenyFinitelyGenerated

/-!
# Concrete finite-generation applications of the Mordell-Weil mechanism

Mordell-Weil uses finite generation to split a rational-point group, up to
isogeny, into a finite-rank lattice and finite torsion. Here that mechanism is
instantiated for `ℤ × ZMod 6` and for its finite torsion factor.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Projection away from the finite torsion factor is an isogeny. -/
theorem integer_times_zmod_six_isAddIsogeny :
    IsAddIsogeny (AddMonoidHom.fst ℤ (ZMod 6)) :=
  IsogenyFinitelyGenerated.isAddIsogeny_fst ℤ (ZMod 6)

/-- The concrete finitely generated group is isogenous to a finite-rank lattice. -/
theorem integer_times_zmod_six_isogenous_to_finite_lattice :
    ∃ n : ℕ, IsAddIsogenous (ℤ × ZMod 6) (Fin n → ℤ) :=
  IsogenyFinitelyGenerated.exists_isAddIsogenous_fin_fun (ℤ × ZMod 6)

/-- A finite torsion group is isogenous to the rank-zero lattice. -/
theorem zmod_six_isogenous_to_rank_zero_lattice :
    IsAddIsogenous (ZMod 6) (Fin 0 → ℤ) := by
  refine ⟨0, IsAddIsogeny.of_surjective ?_ ?_⟩
  · intro x
    exact ⟨0, Subsingleton.elim _ _⟩
  · exact Finite.of_injective Subtype.val Subtype.val_injective

end GaloisForLFunctions.HTGeometry
