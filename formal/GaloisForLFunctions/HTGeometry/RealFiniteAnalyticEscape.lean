import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Finite escape for real-analytic relations

On an open preconnected real parameter domain, a nontrivial real-analytic
scalar relation has zero set with empty interior.  Finitely many such
relations therefore admit a common nonzero point.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every nonempty open part of a connected real-analytic domain contains
a point escaping a nontrivial scalar relation. -/
theorem exists_mem_neZero_of_analyticOnNhd_real
    {P F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : P → F} {U V : Set P}
    (hf : AnalyticOnNhd ℝ f U)
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

/-- Local simultaneous escape for a finite family of nontrivial
real-analytic scalar relations. -/
theorem exists_forall_neZero_of_finite_analyticOnNhd_real_local
    {P F I : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Fintype I]
    (f : I → P → F) (U : Set P)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U)
    (hUnonempty : U.Nonempty)
    (hf : ∀ i, AnalyticOnNhd ℝ (f i) U)
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
          exists_mem_neZero_of_analyticOnNhd_real
            (hf i) hUconnected (hne i)
            hVopen hVnonempty hVU
        let W := V ∩
          (U ∩ (f i) ⁻¹' ({0} : Set F)ᶜ)
        have hsecondOpen :
            IsOpen (U ∩ (f i) ⁻¹' ({0} : Set F)ᶜ) :=
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
  exact ⟨p, hVU hpV,
    fun i => hVgood p hpV i (Finset.mem_univ i)⟩

/-- Local simultaneous escape for a countable family of nontrivial
real-analytic scalar relations. -/
theorem exists_forall_neZero_of_countable_analyticOnNhd_real_local
    {P F I : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace P] [Countable I]
    (f : I → P → F) (U : Set P)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U)
    (hUnonempty : U.Nonempty)
    (hf : ∀ i, AnalyticOnNhd ℝ (f i) U)
    (hne : ∀ i, ∃ p ∈ U, f i p ≠ 0) :
    ∃ p ∈ U, ∀ i, f i p ≠ 0 := by
  let W : I → Set U :=
    fun i => {p | f i p ≠ 0}
  have hWopen : ∀ i, IsOpen (W i) := by
    intro i
    exact isClosed_singleton.isOpen_compl.preimage
      (hf i).continuousOn.restrict
  have hWdense : ∀ i, Dense (W i) := by
    intro i
    rw [dense_iff_inter_open]
    intro O hO hOnonempty
    have himageOpen :
        IsOpen (Subtype.val '' O) :=
      hUopen.isOpenEmbedding_subtypeVal.isOpenMap O hO
    have himageNonempty :
        (Subtype.val '' O).Nonempty :=
      hOnonempty.image Subtype.val
    have himageSubset :
        Subtype.val '' O ⊆ U := by
      rintro p ⟨q, hqO, rfl⟩
      exact q.property
    obtain ⟨p, hpImage, hpne⟩ :=
      exists_mem_neZero_of_analyticOnNhd_real
        (hf i) hUconnected (hne i)
        himageOpen himageNonempty himageSubset
    obtain ⟨q, hqO, rfl⟩ := hpImage
    exact ⟨q, hqO, hpne⟩
  letI : BaireSpace U :=
    hUopen.baireSpace
  letI : Nonempty U :=
    hUnonempty.to_subtype
  have hcommon :
      Dense (⋂ i, W i) :=
    dense_iInter_of_isOpen hWopen hWdense
  obtain ⟨p, hp⟩ := hcommon.nonempty
  refine ⟨p, p.property, ?_⟩
  intro i
  exact Set.mem_iInter.mp hp i

end

end GaloisForLFunctions.HTGeometry
