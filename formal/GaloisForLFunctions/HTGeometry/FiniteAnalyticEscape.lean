import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Simultaneous escape from finitely many analytic relations

An analytic scalar function on an arbitrary complex normed parameter space
cannot vanish on an open set without vanishing on the whole connected
domain.  Consequently every nonzero analytic relation has dense open
complement, and finitely many such relations can be escaped
simultaneously.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A globally analytic function on a complex normed space that is nonzero
somewhere has zero set with empty interior. -/
theorem interior_zeroSet_eq_empty_of_analyticOnNhd_complex
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {f : P → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ p, f p ≠ 0) :
    interior {p | f p = 0} = ∅ := by
  obtain ⟨p₁, hp₁⟩ := hne
  rw [Set.eq_empty_iff_forall_notMem]
  intro p₀ hp₀
  have hzeroNhd : f =ᶠ[𝓝 p₀] 0 := by
    filter_upwards [isOpen_interior.mem_nhds hp₀] with p hp
    change f p = 0
    exact
      (show p ∈ ({q : P | f q = 0} : Set P) from
        (interior_subset : interior {q : P | f q = 0} ⊆
          {q : P | f q = 0}) hp)
  have hzero :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ p₀) hzeroNhd
  exact hp₁ (hzero (Set.mem_univ p₁))

/-- The nonzero locus of a nontrivial globally analytic scalar relation is
dense. -/
theorem dense_neZero_of_analyticOnNhd_complex
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {f : P → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ p, f p ≠ 0) :
    Dense {p | f p ≠ 0} := by
  have hdense :=
    interior_eq_empty_iff_dense_compl.mp
      (interior_zeroSet_eq_empty_of_analyticOnNhd_complex hf hne)
  simpa only [Set.compl_setOf, not_not] using hdense

/-- Nonzero loci of a finite family of nontrivial globally analytic
relations have dense intersection. -/
theorem dense_forall_neZero_of_finite_analyticOnNhd_complex
    {P I : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [BaireSpace P] [Fintype I]
    (f : I → P → ℂ)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) Set.univ)
    (hne : ∀ i, ∃ p, f i p ≠ 0) :
    Dense {p | ∀ i, f i p ≠ 0} := by
  let U : I → Set P := fun i => {p | f i p ≠ 0}
  have hopen : ∀ i, IsOpen (U i) := by
    intro i
    exact isClosed_singleton.isOpen_compl.preimage
      (hf i).continuous
  have hdense : ∀ i, Dense (U i) :=
    fun i => dense_neZero_of_analyticOnNhd_complex
      (hf i) (hne i)
  have hall := dense_iInter_of_isOpen hopen hdense
  simpa only [U, Set.mem_setOf_eq, Set.setOf_forall] using hall

/-- There is one parameter point escaping every member of a finite family
of nontrivial globally analytic relations. -/
theorem exists_forall_neZero_of_finite_analyticOnNhd_complex
    {P I : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [BaireSpace P] [Fintype I]
    (f : I → P → ℂ)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) Set.univ)
    (hne : ∀ i, ∃ p, f i p ≠ 0) :
    ∃ p, ∀ i, f i p ≠ 0 :=
  (dense_forall_neZero_of_finite_analyticOnNhd_complex
    f hf hne).nonempty

/-- Every nonempty open part of a connected analytic domain contains a
point escaping a nontrivial analytic relation. -/
theorem exists_mem_neZero_of_analyticOnNhd_complex
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {f : P → ℂ} {U V : Set P}
    (hf : AnalyticOnNhd ℂ f U)
    (hU : IsPreconnected U)
    (hne : ∃ p ∈ U, f p ≠ 0)
    (hVopen : IsOpen V) (hVnonempty : V.Nonempty)
    (hVU : V ⊆ U) :
    ∃ p ∈ V, f p ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨p₀, hp₀V⟩ := hVnonempty
  have hzeroNhd : f =ᶠ[𝓝 p₀] 0 := by
    filter_upwards [hVopen.mem_nhds hp₀V] with p hp
    exact h p hp
  have hzero :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hU (hVU hp₀V) hzeroNhd
  obtain ⟨p₁, hp₁U, hp₁⟩ := hne
  exact hp₁ (hzero hp₁U)

/-- Local finite escape theorem. On any nonempty open preconnected complex
parameter domain, finitely many analytic relations that are individually
nontrivial can be escaped at one common point. -/
theorem exists_forall_neZero_of_finite_analyticOnNhd_complex_local
    {P I : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Fintype I]
    (f : I → P → ℂ) (U : Set P)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U)
    (hUnonempty : U.Nonempty)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (hne : ∀ i, ∃ p ∈ U, f i p ≠ 0) :
    ∃ p ∈ U, ∀ i, f i p ≠ 0 := by
  classical
  have hind :
      ∀ s : Finset I,
        ∃ V : Set P,
          IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
            ∀ p ∈ V, ∀ i ∈ s, f i p ≠ 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨U, hUopen, hUnonempty, Subset.rfl, by simp⟩
    | @insert i s his ih =>
        obtain ⟨V, hVopen, hVnonempty, hVU, hVgood⟩ := ih
        obtain ⟨p₀, hp₀V, hp₀ne⟩ :=
          exists_mem_neZero_of_analyticOnNhd_complex
            (hf i) hUconnected (hne i)
            hVopen hVnonempty hVU
        let W := V ∩
          (U ∩ (f i) ⁻¹' ({0} : Set ℂ)ᶜ)
        have hsecondOpen :
            IsOpen (U ∩ (f i) ⁻¹' ({0} : Set ℂ)ᶜ) :=
          (hf i).continuousOn.isOpen_inter_preimage
            hUopen isClosed_singleton.isOpen_compl
        have hWopen : IsOpen W :=
          hVopen.inter hsecondOpen
        have hp₀W : p₀ ∈ W := by
          exact ⟨hp₀V, hVU hp₀V, by simpa using hp₀ne⟩
        refine ⟨W, hWopen, ⟨p₀, hp₀W⟩,
          fun p hp => hp.2.1, ?_⟩
        intro p hp j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · simpa only [W, Set.mem_inter_iff, Set.mem_preimage,
            Set.mem_compl_iff, Set.mem_singleton_iff] using hp.2.2
        · exact hVgood p hp.1 j hj
  obtain ⟨V, hVopen, hVnonempty, hVU, hVgood⟩ :=
    hind Finset.univ
  obtain ⟨p, hpV⟩ := hVnonempty
  exact ⟨p, hVU hpV, fun i => hVgood p hpV i (Finset.mem_univ i)⟩

end

end GaloisForLFunctions.HTGeometry
