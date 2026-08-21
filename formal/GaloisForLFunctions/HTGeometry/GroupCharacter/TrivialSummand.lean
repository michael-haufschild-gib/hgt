import GaloisForLFunctions.HTGeometry.GroupCharacter.Schur

/-!
# Exactly one summand carries the trivial action

In any decomposition of `ℂ[G]` into minimal `G`-stable subspaces, exactly one summand carries the
trivial `G`-action, and that summand is one-dimensional.  This is the input that turns the raw
column-orthogonality identity `sum_chi` into the classical `1 + ∑_{χ ≠ 1} χ(1) χ(g) = 0`.
-/

universe u

namespace GaloisForLFunctions.HTGeometry.GroupCharacter

open MonoidAlgebra

variable {G : Type u} [Group G] [Fintype G]

theorem finrank_eq_one_of_isTrivialOn {N : Submodule ℂ (MonoidAlgebra ℂ G)}
    (hN : IsMinimalGStable N) (htriv : IsTrivialOn hN.stable) :
    Module.finrank ℂ ↥N = 1 := by
  obtain ⟨v, hvN, hv0⟩ : ∃ v ∈ N, v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hN.ne_bot (Submodule.eq_bot_iff N |>.mpr fun x hx => h x hx)
  have hfix : ∀ g : G, regLeft G g v = v := by
    intro g
    have := congrArg (fun (f : ↥N →ₗ[ℂ] ↥N) => (f ⟨v, hvN⟩ : MonoidAlgebra ℂ G)) (htriv g)
    simpa using this
  have hstable : IsGStable G (ℂ ∙ v) := by
    intro g x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    rw [map_smul, hfix]
  have hle : (ℂ ∙ v) ≤ N := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvN)
  have hne : (ℂ ∙ v) ≠ ⊥ := by
    simp [hv0]
  have hspan : (ℂ ∙ v) = N := (hN.minimal _ hstable hle).resolve_left hne
  rw [← hspan, finrank_span_singleton hv0]

theorem trace_sumRho {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) :
    LinearMap.trace ℂ ↥N (sumRho hN) = ∑ g : G, chi hN g := by
  rw [sumRho, map_sum]
  rfl

theorem sum_chi_of_trivial {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsMinimalGStable N)
    (htriv : IsTrivialOn hN.stable) :
    ∑ g : G, chi hN.stable g = (Fintype.card G : ℂ) := by
  rcases sumRho_dichotomy hN with ⟨_, hs⟩ | ⟨hntriv, _⟩
  · rw [← trace_sumRho, hs, map_smul, LinearMap.trace_id,
      finrank_eq_one_of_isTrivialOn hN htriv]
    simp
  · exact absurd htriv hntriv

theorem sum_chi_of_not_trivial {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsMinimalGStable N)
    (hntriv : ¬ IsTrivialOn hN.stable) :
    ∑ g : G, chi hN.stable g = 0 := by
  rcases sumRho_dichotomy hN with ⟨htriv, _⟩ | ⟨_, hs⟩
  · exact absurd htriv hntriv
  · rw [← trace_sumRho, hs, map_zero]

/-- **Exactly one summand carries the trivial action.** -/
theorem existsUnique_isTrivialOn [DecidableEq G] {n : ℕ}
    {N : Fin n → Submodule ℂ (MonoidAlgebra ℂ G)}
    (hN : ∀ i, IsMinimalGStable (N i)) (hint : DirectSum.IsInternal N) :
    ∃! i : Fin n, IsTrivialOn (hN i).stable := by
  classical
  have total : ∑ i : Fin n, ∑ g : G, chi (hN i).stable g = (Fintype.card G : ℂ) := by
    rw [Finset.sum_comm,
      Finset.sum_congr rfl (fun g _ => sum_chi (fun i => (hN i).stable) hint g)]
    simp
  have hsplit : ∑ i : Fin n, ∑ g : G, chi (hN i).stable g
      = ((Finset.univ.filter fun i : Fin n => IsTrivialOn (hN i).stable).card : ℂ)
        * (Fintype.card G : ℂ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n => IsTrivialOn (hN i).stable),
      Finset.sum_congr rfl (fun i hi => sum_chi_of_trivial (hN i) (Finset.mem_filter.mp hi).2),
      Finset.sum_congr rfl (fun i hi => sum_chi_of_not_trivial (hN i) (Finset.mem_filter.mp hi).2)]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [hsplit] at total
  have hone : ((Finset.univ.filter fun i : Fin n => IsTrivialOn (hN i).stable).card : ℂ) = 1 := by
    field_simp at total
    exact_mod_cast total
  have hone' : (Finset.univ.filter fun i : Fin n => IsTrivialOn (hN i).stable).card = 1 := by
    exact_mod_cast hone
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone'
  refine ⟨i, ?_, ?_⟩
  · have hmem : i ∈ Finset.univ.filter fun i : Fin n => IsTrivialOn (hN i).stable := by
      rw [hi]; exact Finset.mem_singleton_self i
    exact (Finset.mem_filter.mp hmem).2
  · intro j hj
    have hmem : j ∈ Finset.univ.filter fun i : Fin n => IsTrivialOn (hN i).stable :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    rw [hi] at hmem
    exact Finset.mem_singleton.mp hmem

end GaloisForLFunctions.HTGeometry.GroupCharacter
