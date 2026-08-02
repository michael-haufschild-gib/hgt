import GaloisForLFunctions.HTGeometry.HermitianDegenerationFlag

/-!
# A direction is determined by its degeneration flag

Two Hermitian directions with the same flag at every threshold are equal.  The counts of eigenvalues
above a threshold are the dimensions of the flag members, so the eigenvalues agree; and each
eigenspace is the part of the flag just above an eigenvalue that is orthogonal to the flag at that
eigenvalue, so the spectral decompositions agree too.

So the degeneration data of a ray of observer metrics determines the direction of the ray: distinct
directions give distinct boundary data, and the assignment of a flag to a direction is faithful.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {S T : E →ₗ[ℂ] E}

/-! ## The flag determines the eigenvalues -/

theorem le_of_card_filter_eq {f g : Fin n → ℝ} (hf : Antitone f) (hg : Antitone g)
    (hcard : ∀ c : ℝ, (Finset.univ.filter fun i => c < f i).card
      = (Finset.univ.filter fun i => c < g i).card) (i : Fin n) : g i ≤ f i := by
  classical
  by_contra hcon
  have hlt : f i < g i := not_le.1 hcon
  have h1 : (Finset.univ.filter fun j => f i < f j) ⊆ Finset.Iio i := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_Iio]
    by_contra hji
    exact absurd hj (not_lt.2 (hf (not_lt.1 hji)))
  have h2 : Finset.Iic i ⊆ (Finset.univ.filter fun j => f i < g j) := by
    intro j hj
    simp only [Finset.mem_Iic] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_lt_of_le hlt (hg hj)
  have hc1 : (Finset.univ.filter fun j => f i < f j).card ≤ (i : ℕ) := by
    have := Finset.card_le_card h1
    simpa using this
  have hc2 : (i : ℕ) + 1 ≤ (Finset.univ.filter fun j => f i < g j).card := by
    have := Finset.card_le_card h2
    simpa using this
  rw [hcard (f i)] at hc1
  omega

/-- **The flag determines the eigenvalues.** -/
theorem eigenvalues_eq_of_eigenSum_eq (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : finrank ℂ E = n) (h : ∀ c : ℝ, eigenSum S c = eigenSum T c) :
    hS.eigenvalues hn = hT.eigenvalues hn := by
  classical
  have hcard : ∀ c : ℝ, (Finset.univ.filter fun i : Fin n => c < hS.eigenvalues hn i).card
      = (Finset.univ.filter fun i : Fin n => c < hT.eigenvalues hn i).card := by
    intro c
    rw [← finrank_eigenSum hS hn c, ← finrank_eigenSum hT hn c, h c]
  funext i
  exact le_antisymm
    (le_of_card_filter_eq (hT.eigenvalues_antitone hn) (hS.eigenvalues_antitone hn)
      (fun c => (hcard c).symm) i)
    (le_of_card_filter_eq (hS.eigenvalues_antitone hn) (hT.eigenvalues_antitone hn) hcard i)

/-! ## A threshold just below an eigenvalue -/

/-- **Below each value of a finite family there is a gap.**  A threshold that separates the values
below a given one from the values at or above it. -/
theorem exists_gap (f : Fin n → ℝ) (j : Fin n) : ∃ c : ℝ, ∀ i, (c < f i ↔ f j ≤ f i) := by
  classical
  set s := (Finset.univ.image f).filter (· < f j) with hs
  by_cases hne : s.Nonempty
  · have hmax : s.max' hne ∈ s := s.max'_mem hne
    have hmaxlt : s.max' hne < f j := (Finset.mem_filter.1 hmax).2
    refine ⟨s.max' hne, fun i => ?_⟩
    constructor
    · intro hlt
      by_contra hcon
      have hfi : f i < f j := not_le.1 hcon
      have hmem : f i ∈ s := by
        rw [hs, Finset.mem_filter]
        exact ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩, hfi⟩
      exact absurd hlt (not_lt.2 (s.le_max' _ hmem))
    · intro hle
      exact lt_of_lt_of_le hmaxlt hle
  · refine ⟨f j - 1, fun i => ?_⟩
    constructor
    · intro _
      by_contra hcon
      have hfi : f i < f j := not_le.1 hcon
      exact hne ⟨f i, by
        rw [hs, Finset.mem_filter]
        exact ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩, hfi⟩⟩
    · intro hle
      linarith

/-! ## The flag determines the direction -/

/-- **An eigenspace is cut out of the flag by a gap threshold.** -/
theorem eigenspace_eq_inf_orthogonal (hS : S.IsSymmetric) (hn : finrank ℂ E = n) {c : ℝ}
    {μ : ℝ} (hc : ∀ i, (c < hS.eigenvalues hn i ↔ μ ≤ hS.eigenvalues hn i)) :
    eigenSum S c ⊓ (eigenSum S μ)ᗮ = Module.End.eigenspace S (μ : ℂ) := by
  classical
  rw [eigenSum_eq_span hS hn c, eigenSum_eq_span hS hn μ,
    span_inf_orthogonal (hS.eigenvectorBasis hn) _ _, eigenspace_eq_span hS hn μ]
  congr 1
  ext y
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    simp only [Set.mem_sdiff, Set.mem_setOf_eq] at hi
    exact le_antisymm (not_lt.1 hi.2) ((hc i).1 hi.1)
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    simp only [Set.mem_setOf_eq] at hi
    exact ⟨(hc i).2 (le_of_eq hi.symm), by
      simp only [Set.mem_setOf_eq]
      exact not_lt.2 (le_of_eq hi)⟩

/-- **A direction is determined by its degeneration flag.**  Two Hermitian directions whose flags
agree at every threshold are equal, so the boundary data of a ray determines the ray. -/
theorem eq_of_eigenSum_eq (hS : S.IsSymmetric) (hT : T.IsSymmetric) (hn : finrank ℂ E = n)
    (h : ∀ c : ℝ, eigenSum S c = eigenSum T c) : S = T := by
  classical
  have hval : hS.eigenvalues hn = hT.eigenvalues hn := eigenvalues_eq_of_eigenSum_eq hS hT hn h
  refine Basis.ext (hT.eigenvectorBasis hn).toBasis fun j => ?_
  have hb : (hT.eigenvectorBasis hn).toBasis j = (hT.eigenvectorBasis hn) j := by
    rw [OrthonormalBasis.coe_toBasis]
  rw [hb, hT.apply_eigenvectorBasis hn j]
  obtain ⟨c, hc⟩ := exists_gap (hT.eigenvalues hn) j
  have hcS : ∀ i, (c < hS.eigenvalues hn i ↔ hT.eigenvalues hn j ≤ hS.eigenvalues hn i) := by
    intro i
    rw [hval]
    exact hc i
  have hmem1 : (hT.eigenvectorBasis hn) j ∈ eigenSum S c := by
    rw [h c, eigenSum_eq_span hT hn c]
    exact Submodule.subset_span ⟨j, by
      simp only [Set.mem_setOf_eq]
      exact (hc j).2 le_rfl, rfl⟩
  have hmem2 : (hT.eigenvectorBasis hn) j ∈ (eigenSum S (hT.eigenvalues hn j))ᗮ := by
    rw [h _, eigenSum_eq_span hT hn _]
    refine mem_orthogonal_span_of_notMem (hT.eigenvectorBasis hn) ?_
    simp only [Set.mem_setOf_eq]
    exact lt_irrefl _
  have hmem : (hT.eigenvectorBasis hn) j
      ∈ Module.End.eigenspace S ((hT.eigenvalues hn j : ℝ) : ℂ) := by
    rw [← eigenspace_eq_inf_orthogonal hS hn hcS]
    exact ⟨hmem1, hmem2⟩
  exact Module.End.mem_eigenspace_iff.1 hmem

end GaloisForLFunctions.HTGeometry
