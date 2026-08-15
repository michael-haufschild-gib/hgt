import GaloisForLFunctions.HTGeometry.OrbitFamilyJets
import GaloisForLFunctions.HTGeometry.DistinctDifferenceTuple

/-!
# Sample points with pairwise distinct nodes

Two members of one source have the same node at two sample points exactly when the difference of the
sample points lies in a fixed countable set determined by the frequency and the two shifts, and — at
one and the same sample point — exactly when the two shifts have the same exponential.  So distinct
translation classes and one scale avoiding a countable set give sample points at which all nodes of
each source are pairwise distinct.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {L : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The countable set of sample-point differences that would collide two nodes of one source. -/
def orbCollisionSet (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ) : Set ℂ :=
  ⋃ p : ι × ι × ℤ,
    {((p.2.2 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + sh p.2.1 - sh p.1) / lam (src p.1)}

omit [DecidableEq ι] in
theorem countable_orbCollisionSet (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ) :
    (orbCollisionSet lam src sh).Countable :=
  Set.countable_iUnion fun _ => Set.countable_singleton _

/-- **Sample points at which the nodes of each source are pairwise distinct.** -/
theorem exists_sample_orbNode_injective (lam : Fin L → ℂ) (hlam : ∀ j, lam j ≠ 0)
    (src : ι → Fin L) (sh : ι → ℂ)
    (hdist : ∀ i i' : ι, src i = src i' → i ≠ i' →
      Complex.exp (sh i) ≠ Complex.exp (sh i')) (K : ℕ) :
    ∃ t : Fin K → ℂ, ∀ (i i' : ι) (a b : Fin K), src i = src i' →
      orbNode lam src sh i (t a) = orbNode lam src sh i' (t b) → i = i' ∧ a = b := by
  classical
  obtain ⟨t₀, ht₀inj, ht₀⟩ :=
    exists_sample_diff_notMem (countable_orbCollisionSet lam src sh)
  refine ⟨fun a => t₀ (a : ℕ), ?_⟩
  intro i i' a b hsrc hnode
  rw [orbNode, orbNode, Complex.exp_eq_exp_iff_exists_int] at hnode
  obtain ⟨k, hk⟩ := hnode
  have hlam0 : lam (src i) ≠ 0 := hlam _
  have hdiff : t₀ (a : ℕ) - t₀ (b : ℕ) =
      ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + sh i' - sh i) / lam (src i) := by
    rw [eq_div_iff hlam0]
    rw [← hsrc] at hk
    linear_combination hk
  have hab : a = b := by
    by_contra hne
    have hmem : t₀ (a : ℕ) - t₀ (b : ℕ) ∈ orbCollisionSet lam src sh := by
      rw [hdiff, orbCollisionSet]
      exact Set.mem_iUnion.mpr ⟨(i, i', k), rfl⟩
    exact ht₀ (a : ℕ) (b : ℕ) (fun h => hne (Fin.ext h)) hmem
  subst hab
  refine ⟨?_, rfl⟩
  by_contra hii
  refine hdist i i' hsrc hii ?_
  rw [← hsrc] at hk
  have hsh : sh i = sh i' + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    linear_combination hk
  rw [hsh, Complex.exp_eq_exp_iff_exists_int]
  exact ⟨k, rfl⟩

end

end GaloisForLFunctions.HTGeometry
