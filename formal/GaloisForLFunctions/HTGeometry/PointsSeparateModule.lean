import GaloisForLFunctions.HTGeometry.PointsSeparate

/-!
# Points separate with coefficients in an arbitrary module

The Galois correspondence has to separate elements of `R ⊗_C E`, not just of `E`: an element
`Σ r_j ⊗ b_j` killed by every point of `E` must vanish, with the `r_j` in the base ring rather than
in `C`.

That follows from separation on `E` by a finite-dimensional duality argument.  The vectors
`(χ b_1, …, χ b_n)` span `C^n`, because otherwise they lie in the kernel of a nonzero functional,
whose coefficients would give a nontrivial `C`-relation among the `b_j`.  Since the linear map
`x ↦ Σ x_j • r_j` kills all those vectors, it kills their span, hence everything, hence each `r_j`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Points separate with coefficients in a module.** -/
theorem eq_zero_of_forall_point_smul_eq_zero
    {C E M : Type*} [Field C] [IsAlgClosed C] [CommRing E] [IsReduced E] [Algebra C E]
    [Algebra.FiniteType C E] [AddCommGroup M] [Module C M]
    {n : ℕ} (b : Fin n → E)
    (hb : ∀ c : Fin n → C, (∑ j, c j • b j) = 0 → ∀ j, c j = 0)
    (r : Fin n → M)
    (h : ∀ χ : E →ₐ[C] C, (∑ j, (χ (b j)) • r j) = 0) : ∀ k, r k = 0 := by
  classical
  set T : (Fin n → C) →ₗ[C] M := Fintype.linearCombination C r with hT
  set S : Set (Fin n → C) := Set.range (fun χ : E →ₐ[C] C => fun j => χ (b j)) with hS
  have hkill : ∀ x ∈ S, T x = 0 := by
    rintro x ⟨χ, rfl⟩
    rw [hT, Fintype.linearCombination_apply]
    exact h χ
  have hVtop : Submodule.span C S = ⊤ := by
    by_contra hne
    have hlt : Submodule.span C S < ⊤ := lt_of_le_of_ne le_top hne
    obtain ⟨f, hf0, hfle⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    set c : Fin n → C := fun j => f (Pi.single j 1) with hc
    have hexpand : ∀ x : Fin n → C, x = ∑ j, x j • (Pi.single j (1 : C)) := by
      intro x
      funext k
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · intro hcon
        exact absurd (Finset.mem_univ k) hcon
    have hfx : ∀ x : Fin n → C, f x = ∑ j, x j * c j := by
      intro x
      conv_lhs => rw [hexpand x]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
    have hrel : ∀ χ : E →ₐ[C] C, (∑ j, χ (b j) * c j) = 0 := by
      intro χ
      have hmem : f (fun j => χ (b j)) ∈ Submodule.map f (Submodule.span C S) :=
        Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self χ))
      rw [hfle, Submodule.mem_bot] at hmem
      rw [← hfx]
      exact hmem
    have hsum : (∑ j, c j • b j) = 0 := by
      refine eq_zero_of_forall_algHom_eq_zero (C := C) (E := E) ?_
      intro χ
      rw [map_sum]
      rw [← hrel χ]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
    have hc0 := hb c hsum
    refine hf0 (LinearMap.ext fun x => ?_)
    rw [hfx]
    simp [hc0]
  have hTzero : ∀ x : Fin n → C, T x = 0 := by
    have hle : Submodule.span C S ≤ LinearMap.ker T := Submodule.span_le.mpr hkill
    rw [hVtop] at hle
    intro x
    exact hle (Submodule.mem_top)
  intro k
  have hval : T (Pi.single k (1 : C)) = r k := by
    rw [hT, Fintype.linearCombination_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro hcon
      exact absurd (Finset.mem_univ k) hcon
  rw [← hval, hTzero]

end

end GaloisForLFunctions.HTGeometry
