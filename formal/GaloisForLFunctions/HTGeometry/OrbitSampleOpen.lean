import GaloisForLFunctions.HTGeometry.OrbitNodeGenericity

/-!
# Node distinctness is an open condition on the sample points

The nodes of one source at the sample points are pairwise distinct exactly outside finitely many
closed conditions, one per ordered pair of (member, sample point) with the same source.  So the good
sample tuples form a nonempty open set.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {L : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The sample tuples at which the nodes of each source are pairwise distinct. -/
def GoodSamples (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ) {K : ℕ}
    (t : Fin K → ℂ) : Prop :=
  ∀ p q : ι × Fin K, src p.1 = src q.1 → p ≠ q →
    orbNode lam src sh p.1 (t p.2) ≠ orbNode lam src sh q.1 (t q.2)

omit [Fintype ι] [DecidableEq ι] in
theorem goodSamples_of_injective (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ) {K : ℕ}
    {t : Fin K → ℂ}
    (h : ∀ (i i' : ι) (a b : Fin K), src i = src i' →
      orbNode lam src sh i (t a) = orbNode lam src sh i' (t b) → i = i' ∧ a = b) :
    GoodSamples lam src sh t := by
  intro p q hsrc hne hnode
  obtain ⟨h1, h2⟩ := h p.1 q.1 p.2 q.2 hsrc hnode
  exact hne (Prod.ext h1 h2)

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_orbNode_sample (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ) {K : ℕ}
    (i : ι) (a : Fin K) :
    Continuous fun t : Fin K → ℂ => orbNode lam src sh i (t a) := by
  unfold orbNode
  exact Complex.continuous_exp.comp
    ((continuous_const.mul (continuous_apply a)).add continuous_const)

/-- **Node distinctness is an open condition.** -/
theorem isOpen_goodSamples (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ) (K : ℕ) :
    IsOpen {t : Fin K → ℂ | GoodSamples lam src sh t} := by
  classical
  set bad : Set (Fin K → ℂ) :=
    ⋃ p ∈ (Finset.univ : Finset ((ι × Fin K) × (ι × Fin K))).filter
        (fun p => src p.1.1 = src p.2.1 ∧ p.1 ≠ p.2),
      {t : Fin K → ℂ | orbNode lam src sh p.1.1 (t p.1.2) = orbNode lam src sh p.2.1 (t p.2.2)}
    with hbad
  have hclosed : IsClosed bad := by
    rw [hbad]
    refine Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun p _ => ?_
    exact isClosed_eq (continuous_orbNode_sample lam src sh p.1.1 p.1.2)
      (continuous_orbNode_sample lam src sh p.2.1 p.2.2)
  have hcompl : {t : Fin K → ℂ | GoodSamples lam src sh t} = badᶜ := by
    ext t
    constructor
    · intro ht hmem
      rw [hbad] at hmem
      obtain ⟨p, hp, hmemp⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨-, hsrc, hne⟩ := Finset.mem_filter.mp hp
      exact ht p.1 p.2 hsrc hne hmemp
    · intro ht p q hsrc hne hnode
      refine ht ?_
      rw [hbad]
      refine Set.mem_iUnion₂.mpr ⟨(p, q), ?_, hnode⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsrc, hne⟩
  rw [hcompl]
  exact hclosed.isOpen_compl

/-- **Good sample tuples exist.** -/
theorem exists_goodSamples (lam : Fin L → ℂ) (hlam : ∀ j, lam j ≠ 0) (src : ι → Fin L)
    (sh : ι → ℂ)
    (hdist : ∀ i i' : ι, src i = src i' → i ≠ i' →
      Complex.exp (sh i) ≠ Complex.exp (sh i')) (K : ℕ) :
    ∃ t : Fin K → ℂ, GoodSamples lam src sh t := by
  obtain ⟨t, ht⟩ := exists_sample_orbNode_injective lam hlam src sh hdist K
  exact ⟨t, goodSamples_of_injective lam src sh ht⟩

end

end GaloisForLFunctions.HTGeometry
