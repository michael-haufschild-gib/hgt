import GaloisForLFunctions.HTGeometry.InvarianceOfDomain

/-!
# A compact homogeneous space of full dimension does not embed in Euclidean space

If a compact homogeneous space embeds in a finite-dimensional Euclidean space `E` and at the same
time receives a continuous injection from a nonempty open subset of `E`, then its image is open by
invariance of domain at every point — homogeneity moves the one open patch everywhere — so the image
is clopen, hence all of `E`, contradicting compactness.

This is the sharp step behind Cartwright's frequency theorem: an almost-periodic solution of a
uniquely solvable autonomous system in `ℝ^p` has frequency rank strictly below `p`, not merely at
most `p`.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The homogeneous full-dimension obstruction.**  A compact homogeneous space cannot both embed
in `E` and receive a continuous injection from a nonempty open subset of `E`. -/
theorem false_of_compact_homogeneous_embedding [Nontrivial E]
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (J : X → E) (hJcont : Continuous J) (hJinj : Function.Injective J)
    (hhom : ∀ x y : X, ∃ h : X ≃ₜ X, h x = y)
    {U : Set E} (hUopen : IsOpen U) (hUne : U.Nonempty)
    {Φ : E → X} (hΦcont : ContinuousOn Φ U) (hΦinj : Set.InjOn Φ U) :
    False := by
  classical
  obtain ⟨u, hu⟩ := hUne
  set x₀ : X := Φ u with hx₀
  set K : Set E := Set.range J with hK
  have hKcompact : IsCompact K := isCompact_range hJcont
  -- every point of the image has an open neighbourhood inside the image
  have hopen : ∀ y : X, ∃ W : Set E, IsOpen W ∧ J y ∈ W ∧ W ⊆ K := by
    intro y
    obtain ⟨h, hh⟩ := hhom x₀ y
    refine ⟨(fun e => J (h (Φ e))) '' U, ?_, ?_, ?_⟩
    · refine invariance_of_domain_open_map (fun e => J (h (Φ e))) U hUopen ?_ ?_
      · exact (hJcont.comp h.continuous).comp_continuousOn hΦcont
      · intro a ha b hb hab
        exact hΦinj ha hb (h.injective (hJinj hab))
    · refine ⟨u, hu, ?_⟩
      show J (h (Φ u)) = J y
      rw [← hx₀, hh]
    · rintro _ ⟨e, -, rfl⟩
      exact ⟨h (Φ e), rfl⟩
  have hKopen : IsOpen K := by
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨y, rfl⟩
    obtain ⟨W, hWopen, hyW, hWK⟩ := hopen y
    exact ⟨W, hWK, hWopen, hyW⟩
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hKne : K.Nonempty := ⟨J x₀, ⟨x₀, rfl⟩⟩
  have hKuniv : K = Set.univ := by
    rcases (isClopen_iff (α := E)).mp ⟨hKclosed, hKopen⟩ with h | h
    · exact absurd h hKne.ne_empty
    · exact h
  have hcompact : IsCompact (Set.univ : Set E) := by
    rw [← hKuniv]
    exact hKcompact
  haveI : NoncompactSpace E := NormedSpace.noncompactSpace ℝ E
  exact NoncompactSpace.noncompact_univ hcompact

end GaloisForLFunctions.HTGeometry
