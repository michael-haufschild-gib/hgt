import GaloisForLFunctions.HTGeometry.TopSumMajorization
import GaloisForLFunctions.HTGeometry.HermitianDegenerationFlag

/-!
# Eigenframes ordered by decreasing eigenvalue

Every Hermitian direction has an orthonormal eigenframe whose eigenvalues are antitone, obtained by
reindexing the spectral frame along the sorting permutation.  In such a frame the degeneration flag
at a threshold is the span of an *initial segment* of the frame, because the indices above the
threshold form a lower set of a finite linear order.

This is the form in which the flag is transported by a symmetry: an initial segment is what the
Gram–Schmidt process preserves.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {T : E →ₗ[ℂ] E}

/-! ## The eigenframe in decreasing order -/

/-- **Every Hermitian direction has an orthonormal eigenframe with antitone eigenvalues.** -/
theorem exists_antitone_eigenframe (hT : T.IsSymmetric) (hn : finrank ℂ E = n) :
    ∃ (b : OrthonormalBasis (Fin n) ℂ E) (w : Fin n → ℝ), Antitone w ∧
      ∀ i, T (b i) = ((w i : ℝ) : ℂ) • b i := by
  classical
  refine ⟨(hT.eigenvectorBasis hn).reindex (descPerm (hT.eigenvalues hn)).symm,
    sortDesc (hT.eigenvalues hn), antitone_sortDesc _, fun i => ?_⟩
  rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
  exact hT.apply_eigenvectorBasis hn _

/-! ## The flag is an initial segment -/

theorem isLowerSet_gt {w : Fin n → ℝ} (hw : Antitone w) (c : ℝ) :
    IsLowerSet {i : Fin n | c < w i} := by
  intro i j hji hi
  exact lt_of_lt_of_le hi (hw hji)

/-- **In an antitone frame the indices above a threshold form an initial segment.** -/
theorem gt_set_eq_empty_or_Iic {w : Fin n → ℝ} (hw : Antitone w) (c : ℝ) :
    {i : Fin n | c < w i} = ∅ ∨ ∃ k : Fin n, {i : Fin n | c < w i} = Set.Iic k := by
  classical
  set s : Finset (Fin n) := Finset.univ.filter fun i => c < w i with hs
  have hmem : ∀ i : Fin n, i ∈ s ↔ c < w i := by
    intro i
    simp [hs]
  rcases Finset.eq_empty_or_nonempty s with hempty | hne
  · refine Or.inl ?_
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hi
    exact absurd ((hmem i).2 hi) (by rw [hempty]; exact Finset.notMem_empty i)
  · refine Or.inr ⟨s.max' hne, ?_⟩
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    constructor
    · intro hi
      exact Finset.le_max' s i ((hmem i).2 hi)
    · intro hi
      exact isLowerSet_gt hw c hi ((hmem _).1 (s.max'_mem hne))

omit [FiniteDimensional ℂ E] in
/-- **The flag at a threshold is the span of an initial segment of an antitone eigenframe.** -/
theorem eigenSum_eq_span_initial (b : OrthonormalBasis (Fin n) ℂ E)
    {w : Fin n → ℝ} (hw : Antitone w) (hd : ∀ i, T (b i) = ((w i : ℝ) : ℂ) • b i) (c : ℝ) :
    eigenSum T c = ⊥ ∨ ∃ k : Fin n, eigenSum T c = Submodule.span ℂ (b '' Set.Iic k) := by
  have hspan : eigenSum T c = Submodule.span ℂ (b '' {i : Fin n | c < w i}) := by
    have := eigenSum_eq_span_of_eigenbasis (T := T) b.toBasis (w := w)
      (fun i => by rw [OrthonormalBasis.coe_toBasis]; exact hd i) c
    rwa [OrthonormalBasis.coe_toBasis] at this
  rcases gt_set_eq_empty_or_Iic hw c with hempty | ⟨k, hk⟩
  · refine Or.inl ?_
    rw [hspan, hempty]
    simp
  · exact Or.inr ⟨k, by rw [hspan, hk]⟩

end GaloisForLFunctions.HTGeometry
