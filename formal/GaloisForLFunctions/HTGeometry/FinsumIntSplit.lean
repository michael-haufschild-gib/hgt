import GaloisForLFunctions.HTGeometry.TripticOrbitResidueReciprocity

/-!
# Splitting a finitely supported sum over the integers

A finitely supported family on `ℤ` splits into its forward and backward rays:

`Σ_{k ∈ ℤ} A k = Σ_{k ≥ 0} A k + Σ_{j ≥ 1} A (−j)`.

Both sides are read as finite sums over a symmetric interval containing the support, and the
backward ray is reindexed by `j ↦ −(j+1)`.

* `finsum_int_split`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

/-- **The forward/backward split of a finitely supported integer sum.** -/
theorem finsum_int_split {A : ℤ → ℂ} (hfin : {n : ℤ | A n ≠ 0}.Finite) :
    ∑ᶠ k : ℤ, A k = (∑ᶠ k : ℕ, A (k : ℤ)) + ∑ᶠ j : ℕ, A (-((j : ℤ) + 1)) := by
  classical
  obtain ⟨N, hN⟩ := exists_symmetric_bound_of_finite_support hfin
  have hsuppZ : Function.support A ⊆ (Finset.Ico (-(N : ℤ)) (N : ℤ) : Finset ℤ) := by
    intro n hn
    simp only [Finset.coe_Ico, Set.mem_Ico]
    by_contra hcon
    exact hn (hN n (by omega))
  have hsuppF : Function.support (fun k : ℕ => A (k : ℤ)) ⊆ (Finset.range N : Finset ℕ) := by
    intro k hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    exact hk (hN (k : ℤ) (Or.inl (by omega)))
  have hsuppB : Function.support (fun j : ℕ => A (-((j : ℤ) + 1))) ⊆
      (Finset.range N : Finset ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    exact hj (hN (-((j : ℤ) + 1)) (Or.inr (by omega)))
  rw [finsum_eq_sum_of_support_subset A hsuppZ,
    finsum_eq_sum_of_support_subset _ hsuppF, finsum_eq_sum_of_support_subset _ hsuppB]
  have hsplit : ∑ i ∈ Finset.Ico (-(N : ℤ)) 0, A i + ∑ i ∈ Finset.Ico (0 : ℤ) (N : ℤ), A i
      = ∑ i ∈ Finset.Ico (-(N : ℤ)) (N : ℤ), A i := by
    have hdisj : Disjoint (Finset.Ico (-(N : ℤ)) 0) (Finset.Ico (0 : ℤ) (N : ℤ)) :=
      Finset.Ico_disjoint_Ico_consecutive _ _ _
    have hunion : Finset.Ico (-(N : ℤ)) 0 ∪ Finset.Ico (0 : ℤ) (N : ℤ)
        = Finset.Ico (-(N : ℤ)) (N : ℤ) := Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)
    rw [← hunion, Finset.sum_union hdisj]
  rw [← hsplit]
  have hfwd : ∑ i ∈ Finset.Ico (0 : ℤ) (N : ℤ), A i = ∑ k ∈ Finset.range N, A (k : ℤ) := by
    refine Finset.sum_nbij' (i := fun i => i.toNat) (j := fun k => (k : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Ico] at ha
      simp only [Finset.mem_range]
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ico]
      omega
    · intro a ha
      simp only [Finset.mem_Ico] at ha
      omega
    · intro k _
      simp
    · intro a ha
      simp only [Finset.mem_Ico] at ha
      congr 1
      omega
  have hbwd : ∑ i ∈ Finset.Ico (-(N : ℤ)) 0, A i
      = ∑ j ∈ Finset.range N, A (-((j : ℤ) + 1)) := by
    refine Finset.sum_nbij' (i := fun i => (-i - 1).toNat) (j := fun j => -((j : ℤ) + 1)) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Ico] at ha
      simp only [Finset.mem_range]
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_Ico]
      omega
    · intro a ha
      simp only [Finset.mem_Ico] at ha
      omega
    · intro j _
      omega
    · intro a ha
      simp only [Finset.mem_Ico] at ha
      congr 1
      omega
  rw [hfwd, hbwd]
  ring

end GaloisForLFunctions.HTGeometry
