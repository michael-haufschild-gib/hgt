import GaloisForLFunctions.HTGeometry.FiniteObservableKoopmanBoundary

/-!
# Finite-family synchronized jet escape

A constant-coefficient differentially transcendental source can place at most `finrank V` of its
derivatives in one finite-dimensional function dictionary `V`.  For a finite source family, the
union of all captured derivative orders therefore has size at most
`Fintype.card ι * finrank V`.  Any larger finite test set contains one order missed by every source
simultaneously.

This is an arbitrary-window law, not only an initial-segment pigeonhole statement.  Its initial
segment corollary gives a common escape order bounded by the product of source count and dictionary
dimension.
-/

namespace HTGeometry

noncomputable section

/-- **Finite-family synchronized jet escape law.**  If a finite order set is larger than the total
finite-dictionary capacity of a finite family of constant-coefficient differentially
transcendental sources, one order in that exact set escapes the dictionary for every source. -/
theorem exists_common_iteratedDeriv_not_mem_of_card_mul_finrank_lt
    {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ)
    (hf : ∀ i, ConstantCoefficientDifferentiallyTranscendental (f i))
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (s : Finset ℕ)
    (hcard : Fintype.card ι * Module.finrank ℂ V < s.card) :
    ∃ n ∈ s, ∀ i, iteratedDeriv n (f i) ∉ V := by
  classical
  let captured : ι → Finset ℕ := fun i =>
    s.filter fun n => iteratedDeriv n (f i) ∈ V
  have hcaptured (i : ι) : (captured i).card ≤ Module.finrank ℂ V := by
    apply iteratedDeriv_mem_finset_card_le_finrank_of_constantCoefficientDifferentiallyTranscendental
      V (hf i)
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  by_contra hescape
  have hcover : s ⊆ Finset.univ.biUnion captured := by
    intro n hn
    have hexists : ∃ i, iteratedDeriv n (f i) ∈ V := by
      by_contra hnone
      apply hescape
      refine ⟨n, hn, ?_⟩
      intro i hi
      exact hnone ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hexists
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hn, hi⟩⟩
  have hsubsetCard : s.card ≤ (Finset.univ.biUnion captured).card :=
    Finset.card_le_card hcover
  have hunionCard : (Finset.univ.biUnion captured).card ≤
      Fintype.card ι * Module.finrank ℂ V := by
    simpa using Finset.card_biUnion_le_card_mul Finset.univ captured
      (Module.finrank ℂ V) (fun i _ => hcaptured i)
  omega

/-- Every finite family has one common escape order no larger than source count times dictionary
dimension. -/
theorem exists_common_iteratedDeriv_not_mem_le_card_mul_finrank
    {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ)
    (hf : ∀ i, ConstantCoefficientDifferentiallyTranscendental (f i))
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V] :
    ∃ n ≤ Fintype.card ι * Module.finrank ℂ V,
      ∀ i, iteratedDeriv n (f i) ∉ V := by
  let d := Fintype.card ι * Module.finrank ℂ V
  obtain ⟨n, hn, hescape⟩ :=
    exists_common_iteratedDeriv_not_mem_of_card_mul_finrank_lt
      f hf V (Finset.range (d + 1)) (by simp [d])
  exact ⟨n, by have := Finset.mem_range.mp hn; omega, hescape⟩

end

end HTGeometry
