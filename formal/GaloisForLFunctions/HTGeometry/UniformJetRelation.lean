import Mathlib

/-!
# One equation for a whole family from ultrafilter-wise annihilation

A family of tuples in a commutative algebra is *uniformly annihilated* when a single nonzero
polynomial vanishes on every member.  Annihilation sets are closed upward under products, so the
family of their complements is downward directed: if no single polynomial annihilated the whole
family, those complements would generate a proper filter and hence an ultrafilter on which no
annihilation set lies.

Consequently it suffices to annihilate the family *ultrafilter-wise*: if for every ultrafilter on
the index set some nonzero polynomial annihilates almost every member, then one nonzero polynomial
annihilates every member.  This is the compactness step that upgrades a transcendence-degree count
performed in an ultraproduct to a statement about each individual member.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {ι K Ω : Type*} [Field K] [CommRing Ω] [Algebra K Ω]

/-- The set of indices at which a polynomial annihilates the corresponding tuple. -/
def annihilationSet {m : ℕ} (ξ : ι → Fin m → Ω) (Q : MvPolynomial (Fin m) K) : Set ι :=
  {n : ι | MvPolynomial.aeval (ξ n) Q = 0}

theorem annihilationSet_mul_superset {m : ℕ} (ξ : ι → Fin m → Ω)
    (Q R : MvPolynomial (Fin m) K) :
    annihilationSet ξ Q ⊆ annihilationSet ξ (Q * R) := by
  intro n hn
  simp only [annihilationSet, Set.mem_setOf_eq] at hn ⊢
  rw [map_mul, hn, zero_mul]

theorem annihilationSet_mul_superset_right {m : ℕ} (ξ : ι → Fin m → Ω)
    (Q R : MvPolynomial (Fin m) K) :
    annihilationSet ξ R ⊆ annihilationSet ξ (Q * R) := by
  intro n hn
  simp only [annihilationSet, Set.mem_setOf_eq] at hn ⊢
  rw [map_mul, hn, mul_zero]

/-- **Ultrafilter-wise annihilation is uniform annihilation.**  If for every ultrafilter on the
index set some nonzero polynomial annihilates the tuples on a set of the ultrafilter, then a single
nonzero polynomial annihilates every tuple of the family. -/
theorem exists_uniform_annihilator {m : ℕ} (ξ : ι → Fin m → Ω)
    (h : ∀ u : Ultrafilter ι, ∃ Q : MvPolynomial (Fin m) K, Q ≠ 0 ∧ annihilationSet ξ Q ∈ u) :
    ∃ Q : MvPolynomial (Fin m) K, Q ≠ 0 ∧ ∀ n : ι, MvPolynomial.aeval (ξ n) Q = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  -- every nonzero polynomial misses at least one member
  have hcompl : ∀ Q : MvPolynomial (Fin m) K, Q ≠ 0 → (annihilationSet ξ Q)ᶜ.Nonempty := by
    intro Q hQ
    obtain ⟨n, hn⟩ := hcon Q hQ
    exact ⟨n, hn⟩
  have hι : Nonempty ι := by
    obtain ⟨n, -⟩ := hcompl 1 one_ne_zero
    exact ⟨n⟩
  -- the complements are downward directed, so they generate a proper filter
  set J := {Q : MvPolynomial (Fin m) K // Q ≠ 0} with hJ
  haveI : Nonempty J := ⟨⟨1, one_ne_zero⟩⟩
  set F : J → Filter ι := fun Q => Filter.principal (annihilationSet ξ (Q : MvPolynomial _ K))ᶜ
    with hF
  have hdir : Directed (fun x y => x ≥ y) F := by
    intro Q R
    refine ⟨⟨(Q : MvPolynomial (Fin m) K) * (R : MvPolynomial (Fin m) K),
      mul_ne_zero Q.2 R.2⟩, ?_, ?_⟩
    · exact Filter.principal_mono.mpr
        (Set.compl_subset_compl.mpr (annihilationSet_mul_superset ξ _ _))
    · exact Filter.principal_mono.mpr
        (Set.compl_subset_compl.mpr (annihilationSet_mul_superset_right ξ _ _))
  have hne : ∀ Q : J, (F Q).NeBot := by
    intro Q
    exact Filter.principal_neBot_iff.mpr (hcompl _ Q.2)
  haveI : (iInf F).NeBot := Filter.iInf_neBot_of_directed hdir hne
  obtain ⟨Q, hQ0, hQu⟩ := h (Ultrafilter.of (iInf F))
  have hle : ((Ultrafilter.of (iInf F) : Filter ι)) ≤ F ⟨Q, hQ0⟩ :=
    le_trans (Ultrafilter.of_le (iInf F)) (iInf_le F ⟨Q, hQ0⟩)
  have hmem : (annihilationSet ξ Q)ᶜ ∈ (Ultrafilter.of (iInf F) : Filter ι) :=
    hle (Filter.mem_principal_self _)
  have hempty : (∅ : Set ι) ∈ (Ultrafilter.of (iInf F) : Filter ι) := by
    have := Filter.inter_mem hQu hmem
    simp at this
  exact (Ultrafilter.of (iInf F)).neBot'.ne (Filter.empty_mem_iff_bot.mp hempty)

end GaloisForLFunctions.HTGeometry
