import GaloisForLFunctions.HTGeometry.PointsSeparateModule

/-!
# Separation by a subset of points, with coefficients in a module

A set of points that already detects zero on a commutative algebra detects zero for coefficients in
any module: the vectors of values at those points span the coordinate space, because a functional
killing them all would give a nontrivial relation among the basis elements, which the separation
hypothesis forbids.

This is the form the parameterised Galois group needs — its points are the differential ones, not
all of them.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A separating set of points separates with coefficients in a module.**  If a set of points is
enough to detect zero on the algebra, it is enough to detect zero for coefficients in any module. -/
theorem eq_zero_of_forall_pointSubset_smul_eq_zero
    {C E M : Type*} [Field C] [CommRing E] [Algebra C E] [AddCommGroup M] [Module C M]
    (S : Set (E →ₐ[C] C)) (hsep : ∀ e : E, (∀ χ ∈ S, χ e = 0) → e = 0)
    {n : ℕ} (b : Fin n → E)
    (hb : ∀ c : Fin n → C, (∑ j, c j • b j) = 0 → ∀ j, c j = 0)
    (r : Fin n → M)
    (h : ∀ χ ∈ S, (∑ j, (χ (b j)) • r j) = 0) : ∀ k, r k = 0 := by
  classical
  set T : (Fin n → C) →ₗ[C] M := Fintype.linearCombination C r with hT
  set V : Set (Fin n → C) := {x | ∃ χ ∈ S, (fun j => χ (b j)) = x} with hV
  have hkill : ∀ x ∈ V, T x = 0 := by
    rintro x ⟨χ, hχ, rfl⟩
    rw [hT, Fintype.linearCombination_apply]
    exact h χ hχ
  have hVtop : Submodule.span C V = ⊤ := by
    by_contra hne
    have hlt : Submodule.span C V < ⊤ := lt_of_le_of_ne le_top hne
    obtain ⟨f, hf0, hfle⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    set c : Fin n → C := fun j => f (Pi.single j 1) with hc
    have hexpand : ∀ x : Fin n → C, x = ∑ j, x j • (Pi.single j (1 : C)) := by
      intro x
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
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
    have hrel : ∀ χ ∈ S, (∑ j, χ (b j) * c j) = 0 := by
      intro χ hχ
      have hmem : f (fun j => χ (b j)) ∈ Submodule.map f (Submodule.span C V) :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨χ, hχ, rfl⟩)
      rw [hfle, Submodule.mem_bot] at hmem
      rw [← hfx]
      exact hmem
    have hsum : (∑ j, c j • b j) = 0 := by
      refine hsep _ ?_
      intro χ hχ
      rw [map_sum]
      rw [← hrel χ hχ]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
    have hc0 := hb c hsum
    refine hf0 (LinearMap.ext fun x => ?_)
    rw [hfx]
    simp [hc0]
  have hTzero : ∀ x : Fin n → C, T x = 0 := by
    have hle : Submodule.span C V ≤ LinearMap.ker T := Submodule.span_le.mpr hkill
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
