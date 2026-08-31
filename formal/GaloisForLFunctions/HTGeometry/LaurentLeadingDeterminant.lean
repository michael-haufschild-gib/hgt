import Mathlib

/-!
# Leading coefficients of products and determinants of Laurent-series matrices

If every entry of a matrix over a Laurent-series field vanishes below a row-plus-column bound, then
the determinant vanishes below the total bound and its coefficient there is the determinant of the
matrix of boundary coefficients.  A nonzero boundary determinant therefore certifies a nonzero
determinant — the leading-term test used by a Newton-corner degeneration.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

/-- The boundary coefficient of a product is the product of the boundary coefficients. -/
theorem coeff_mul_of_vanishing_below {f g : LaurentSeries F} {m n : ℤ}
    (hf : ∀ i < m, f.coeff i = 0) (hg : ∀ j < n, g.coeff j = 0) :
    (f * g).coeff (m + n) = f.coeff m * g.coeff n := by
  classical
  rw [HahnSeries.coeff_mul]
  by_cases hmem : ((m, n) : ℤ × ℤ) ∈
      Finset.antidiagonal f.isPWO_support g.isPWO_support (m + n)
  · refine Finset.sum_eq_single ((m, n) : ℤ × ℤ) ?_ (fun hcon => absurd hmem hcon)
    rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    obtain ⟨hi, hj, hsum⟩ := hij
    rcases lt_trichotomy i m with hlt | heq | hgt
    · rw [hf i hlt, zero_mul]
    · exact absurd (Prod.ext heq (by omega)) hne
    · rw [hg j (by omega), mul_zero]
  · simp only [Finset.mem_antidiagonal, not_and] at hmem
    have hzero : f.coeff m * g.coeff n = 0 := by
      by_cases hfm : f.coeff m = 0
      · rw [hfm, zero_mul]
      · have hgn : g.coeff n = 0 := by
          by_contra hgn
          exact (hmem (by simpa using hfm) (by simpa using hgn)) trivial
        rw [hgn, mul_zero]
    rw [hzero]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    obtain ⟨hi, hj, hsum⟩ := hp
    rcases lt_trichotomy p.1 m with hlt | heq | hgt
    · rw [hf p.1 hlt, zero_mul]
    · have : p.2 = n := by omega
      rw [heq, this, hzero]
    · rw [hg p.2 (by omega), mul_zero]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

/-- A product vanishes below the sum of the bounds. -/
theorem coeff_mul_eq_zero_of_lt {f g : LaurentSeries F} {m n : ℤ}
    (hf : ∀ i < m, f.coeff i = 0) (hg : ∀ j < n, g.coeff j = 0) :
    ∀ k < m + n, (f * g).coeff k = 0 := by
  classical
  intro k hk
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  obtain ⟨-, -, hsum⟩ := hp
  by_cases h1 : p.1 < m
  · rw [hf p.1 h1, zero_mul]
  · rw [hg p.2 (by omega), mul_zero]

/-- The boundary coefficient of a finite product. -/
theorem coeff_prod_of_vanishing_below {ι : Type*} [DecidableEq ι] (f : ι → LaurentSeries F)
    (m : ι → ℤ) :
    ∀ s : Finset ι, (∀ i ∈ s, ∀ k < m i, (f i).coeff k = 0) →
      (∀ k < ∑ i ∈ s, m i, (∏ i ∈ s, f i).coeff k = 0) ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, m i) = ∏ i ∈ s, (f i).coeff (m i) := by
  intro s
  induction s using Finset.induction with
  | empty =>
      intro _
      refine ⟨fun k hk => ?_, ?_⟩
      · simp only [Finset.sum_empty] at hk
        simp only [Finset.prod_empty]
        rw [HahnSeries.coeff_one, if_neg (by omega)]
      · simp only [Finset.prod_empty, Finset.sum_empty]
        rw [HahnSeries.coeff_one, if_pos rfl]
  | insert a s ha ih =>
      intro hall
      obtain ⟨hzero, hlead⟩ := ih fun i hi => hall i (Finset.mem_insert_of_mem hi)
      have hfa := hall a (Finset.mem_insert_self a s)
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact ⟨coeff_mul_eq_zero_of_lt hfa hzero,
        by rw [coeff_mul_of_vanishing_below hfa hzero, hlead, Finset.prod_insert ha]⟩

/-- **The leading determinant.**  If every entry vanishes below its row-plus-column bound, the
determinant's coefficient at the total bound is the determinant of the boundary coefficients. -/
theorem det_coeff_of_vanishing_below {n : ℕ} (M : Matrix (Fin n) (Fin n) (LaurentSeries F))
    (a b : Fin n → ℤ) (hM : ∀ i j, ∀ k < a i + b j, (M i j).coeff k = 0) :
    (M.det).coeff ((∑ i, a i) + ∑ j, b j)
      = (Matrix.of fun i j => (M i j).coeff (a i + b j)).det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply]
  rw [HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hsum : (∑ i, (a (σ i) + b i)) = (∑ i, a i) + ∑ j, b j := by
    rw [Finset.sum_add_distrib]
    congr 1
    exact Fintype.sum_equiv σ _ _ fun i => rfl
  have hprod := (coeff_prod_of_vanishing_below (fun i => M (σ i) i) (fun i => a (σ i) + b i)
    Finset.univ (fun i _ => hM (σ i) i)).2
  rw [hsum] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul, one_smul, hprod]
    simp only [Matrix.of_apply]
  · rw [hs]
    have h1 : ((-1 : ℤˣ) • (∏ i, M (σ i) i)) = -(∏ i, M (σ i) i) := by simp
    have h2 : ((-1 : ℤˣ) •
        (∏ i, (Matrix.of (fun i j => (M i j).coeff (a i + b j))) (σ i) i))
        = -(∏ i, (M (σ i) i).coeff (a (σ i) + b i)) := by
      simp only [Matrix.of_apply]
      simp
    rw [h1, h2, HahnSeries.coeff_neg, hprod]

/-- **A nonzero leading determinant certifies a nonzero determinant.** -/
theorem det_ne_zero_of_leading_det_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) (LaurentSeries F))
    (a b : Fin n → ℤ) (hM : ∀ i j, ∀ k < a i + b j, (M i j).coeff k = 0)
    (hL : (Matrix.of fun i j => (M i j).coeff (a i + b j)).det ≠ 0) :
    M.det ≠ 0 := by
  intro hzero
  apply hL
  rw [← det_coeff_of_vanishing_below M a b hM, hzero]
  simp

end GaloisForLFunctions.HTGeometry
