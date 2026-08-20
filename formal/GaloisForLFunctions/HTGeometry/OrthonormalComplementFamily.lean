/-
# Orthonormal families in the orthogonal complement of a finite-dimensional subspace

An infinite-dimensional inner product space has a unit vector orthogonal to any finite-dimensional
subspace: the complement of a complete subspace is a complement, so it can only be trivial when the
subspace is everything.  Iterating, absorbing each chosen vector into the subspace, produces an
orthonormal family of any prescribed finite size inside the orthogonal complement.

This is the room the determinant-completion sufficiency construction needs: a place to put a
vanishing micro-spectrum block that commutes trivially with a given finite-rank operator.

Main results:
* `exists_unit_mem_orthogonal` — a unit vector orthogonal to a finite-dimensional subspace.
* `exists_orthonormal_mem_orthogonal` — **an orthonormal family of any size in the complement**.
-/
import Mathlib

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **A unit vector orthogonal to a finite-dimensional subspace** of an infinite-dimensional
inner product space. -/
theorem exists_unit_mem_orthogonal (hE : ¬ FiniteDimensional ℂ E)
    (W : Submodule ℂ E) [FiniteDimensional ℂ W] : ∃ u : E, u ∈ Wᗮ ∧ ‖u‖ = 1 := by
  have hne : Wᗮ ≠ ⊥ := by
    intro h
    have hW : W = ⊤ := Submodule.orthogonal_eq_bot_iff.mp h
    refine hE ?_
    have : FiniteDimensional ℂ (⊤ : Submodule ℂ E) := hW ▸ ‹FiniteDimensional ℂ W›
    exact Module.Finite.equiv (Submodule.topEquiv)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
  refine ⟨((‖v‖ : ℂ))⁻¹ • v, Submodule.smul_mem _ _ hv, ?_⟩
  have hvpos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hvpos,
    inv_mul_cancel₀ hvpos.ne']

/-- **An orthonormal family of any prescribed size inside the orthogonal complement** of a
finite-dimensional subspace of an infinite-dimensional inner product space. -/
theorem exists_orthonormal_mem_orthogonal (hE : ¬ FiniteDimensional ℂ E) :
    ∀ (m : ℕ) (W : Submodule ℂ E), FiniteDimensional ℂ W →
      ∃ e : Fin m → E, Orthonormal ℂ e ∧ ∀ i, e i ∈ Wᗮ := by
  intro m
  induction m with
  | zero =>
      intro W _
      exact ⟨Fin.elim0, ⟨fun i => i.elim0, fun {i} => i.elim0⟩, fun i => i.elim0⟩
  | succ m ih =>
      intro W hW
      haveI := hW
      obtain ⟨u, hu, hu1⟩ := exists_unit_mem_orthogonal hE W
      haveI hspan : FiniteDimensional ℂ (Submodule.span ℂ ({u} : Set E)) :=
        FiniteDimensional.span_of_finite ℂ (Set.finite_singleton u)
      haveI hsup : FiniteDimensional ℂ ((W ⊔ Submodule.span ℂ ({u} : Set E) : Submodule ℂ E)) :=
        Submodule.finiteDimensional_sup _ _
      obtain ⟨e, he, hmem⟩ := ih (W ⊔ Submodule.span ℂ ({u} : Set E)) hsup
      have humem : u ∈ (W ⊔ Submodule.span ℂ ({u} : Set E) : Submodule ℂ E) :=
        le_sup_right (a := W) (Submodule.mem_span_singleton_self u)
      have hue : ∀ i : Fin m, ⟪u, e i⟫_ℂ = 0 := fun i =>
        (Submodule.mem_orthogonal _ _).mp (hmem i) u humem
      refine ⟨Fin.cons u e, ?_, ?_⟩
      · classical
        rw [orthonormal_iff_ite]
        intro i j
        refine Fin.cases ?_ ?_ i
        · refine Fin.cases ?_ ?_ j
          · simp [inner_self_eq_norm_sq_to_K, hu1]
          · intro j'
            rw [Fin.cons_zero, Fin.cons_succ, if_neg (Ne.symm (Fin.succ_ne_zero j'))]
            exact hue j'
        · intro i'
          refine Fin.cases ?_ ?_ j
          · have hz : ⟪e i', u⟫_ℂ = 0 := by
              rw [← inner_conj_symm, hue i', map_zero]
            rw [Fin.cons_zero, Fin.cons_succ, if_neg (Fin.succ_ne_zero i')]
            exact hz
          · intro j'
            have := (orthonormal_iff_ite (𝕜 := ℂ) (v := e)).mp he i' j'
            simpa [Fin.succ_inj] using this
      · intro i
        refine Fin.cases ?_ ?_ i
        · simpa using hu
        · intro i'
          have hle : W ≤ W ⊔ Submodule.span ℂ ({u} : Set E) := le_sup_left
          simpa using Submodule.orthogonal_le hle (hmem i')

end

end GaloisForLFunctions.HTGeometry
