import GaloisForLFunctions.HTGeometry.PermanentCoefficientIdentity

/-!
# Indexed complex permanent combinations

`PermanentCoefficientIdentity` shows that a complex combination of the cast permanent symbols
`(permSymbolPoly ν).map (ℤ → ℂ)` over a finset of pairwise distinct order tuples is a nonzero
polynomial.  Downstream the family is presented not by that finset but by an *injective assignment*
`ν : ι → (Fin r → ℕ)` from an arbitrary index type, and in two regimes:

* `combination_permSymbolPolyC_indexed_ne_zero` — every assigned tuple carries the same total
  order `O`, so the finset statement applies to the image after transporting the coefficients;
* `combination_permSymbolPolyC_maxorder_ne_zero` — the orders satisfy only an upper bound `O`, and
  the combination is tested against the top-order subfamily; the total-degree estimate
  `permSymbolPoly_totalDegree_le` annihilates every symbol of strictly smaller order.
-/

open PowerSeries Finset MvPolynomial
open scoped Nat

namespace GaloisForLFunctions

variable {r : ℕ}

/-- **Indexed complex permanent combination.**  A combination `∑_{i∈T} c i · permSymbolPolyℂ (ν i)`
indexed by a finset `T` through an injective, distinct-multiset assignment `ν` is a nonzero polynomial
whenever some `c i₀ ≠ 0`.  The representative coefficient at `X^{ν i₀}` reads off `c i₀` times the
positive stabiliser count. -/
theorem combination_permSymbolPolyC_indexed_ne_zero {ι : Type*} (T : Finset ι)
    (ν : ι → (Fin r → ℕ)) {O : ℕ} (hO : ∀ i ∈ T, ∑ t, ν i t = O)
    (hdist : ∀ i ∈ T, ∀ i' ∈ T,
      (∃ σ : Equiv.Perm (Fin r), ∀ j, ν i j = ν i' (σ j)) → ν i = ν i')
    (hinj : ∀ i ∈ T, ∀ i' ∈ T, ν i = ν i' → i = i')
    (c : ι → ℂ) {i₀ : ι} (hi₀ : i₀ ∈ T) (hc : c i₀ ≠ 0) :
    (∑ i ∈ T, MvPolynomial.C (c i) * (permSymbolPoly (ν i)).map (Int.castRingHom ℂ)) ≠ 0 := by
  classical
  intro hzero
  apply hc
  have hsum1 : ∑ j, (permMon (ν i₀) (1 : Equiv.Perm (Fin r))) j = ∑ t, ν i₀ t := by
    rw [← permMon_sum (ν i₀) 1]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    rw [Finsupp.mem_support_iff, not_not] at hj
    exact hj
  have hcoeff : MvPolynomial.coeff (permMon (ν i₀) (1 : Equiv.Perm (Fin r)))
        (∑ i ∈ T, MvPolynomial.C (c i) * (permSymbolPoly (ν i)).map (Int.castRingHom ℂ))
      = ∑ i ∈ T, c i *
          (((∑ π : Equiv.Perm (Fin r),
            (if permMon (ν i) π = permMon (ν i₀) (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0)) : ℤ) : ℂ) := by
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
      coeff_permSymbolPoly_eq_card (ν i) (permMon (ν i₀) 1) (by rw [hsum1, hO i₀ hi₀, hO i hi])]
    rfl
  rw [hzero, MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single i₀] at hcoeff
  · have hpos : (0 : ℤ) < ∑ π : Equiv.Perm (Fin r),
        (if permMon (ν i₀) π = permMon (ν i₀) (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0) := by
      apply Finset.sum_pos'
      · intro π _; positivity
      · exact ⟨1, Finset.mem_univ 1, by rw [if_pos rfl]; norm_num⟩
    have hcast : (((∑ π : Equiv.Perm (Fin r),
        (if permMon (ν i₀) π = permMon (ν i₀) (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0)) : ℤ) : ℂ) ≠ 0 :=
      Int.cast_ne_zero.mpr (ne_of_gt hpos)
    rcases mul_eq_zero.mp hcoeff.symm with h | h
    · exact h
    · exact absurd h hcast
  · intro i hi hine
    have hzero_count : (∑ π : Equiv.Perm (Fin r),
        (if permMon (ν i) π = permMon (ν i₀) (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro π _
      rw [if_neg]
      intro hpm
      apply hine
      apply hinj i hi i₀ hi₀
      apply hdist i hi i₀ hi₀
      refine ⟨π, fun j => ?_⟩
      have h1 := DFunLike.congr_fun hpm (π j)
      rw [permMon_apply, permMon_apply] at h1
      simpa using h1
    rw [hzero_count]
    simp
  · intro h
    exact absurd hi₀ h

/-- Total degree of `aeval (X j)` of a univariate polynomial is bounded by its degree. -/
theorem aeval_X_totalDegree_le {σ : Type*} (j : σ) (p : Polynomial ℤ) :
    (Polynomial.aeval (X j : MvPolynomial σ ℤ) p).totalDegree ≤ p.natDegree := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum]
  refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun k hk => ?_)
  calc (MvPolynomial.C (p.coeff k) * (X j) ^ k).totalDegree
      ≤ (MvPolynomial.C (p.coeff k)).totalDegree + ((X j : MvPolynomial σ ℤ) ^ k).totalDegree :=
        totalDegree_mul _ _
    _ ≤ k := by rw [totalDegree_C, zero_add, totalDegree_X_pow]
    _ ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp k hk

/-- **Permanent-symbol total degree.**  `permSymbolPoly ν` has total degree at most `∑ ν` — each
falling-factorial factor contributes its order. -/
theorem permSymbolPoly_totalDegree_le (ν : Fin r → ℕ) :
    (permSymbolPoly ν).totalDegree ≤ ∑ t, ν t := by
  rw [permSymbolPoly]
  refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun π _ => ?_)
  refine le_trans (totalDegree_finsetProd _ _) (Finset.sum_le_sum fun t _ => ?_)
  calc (Polynomial.aeval (X (π t)) (descPochhammer ℤ (ν t))).totalDegree
      ≤ (descPochhammer ℤ (ν t)).natDegree := aeval_X_totalDegree_le _ _
    _ = ν t := by rw [descPochhammer_natDegree]

/-- **Maximal-order complex combination.**  If `i₀` attains the maximal total order in `T` and the
assignment `ν` separates `i₀` from every other index under permutation, the combination
`∑_{i∈T} c i · permSymbolPolyℂ (ν i)` is nonzero (representative coefficient at `X^{ν i₀}`: the strictly
lower-order terms vanish there by total degree, and same-order terms other than `i₀` vanish by
distinctness). -/
theorem combination_permSymbolPolyC_maxorder_ne_zero {ι : Type*} (T : Finset ι)
    (ν : ι → (Fin r → ℕ)) (c : ι → ℂ) {i₀ : ι} (hi₀ : i₀ ∈ T)
    (hOle : ∀ i ∈ T, ∑ t, ν i t ≤ ∑ t, ν i₀ t)
    (hdist : ∀ i ∈ T, (∃ σ : Equiv.Perm (Fin r), ∀ j, ν i j = ν i₀ (σ j)) → i = i₀)
    (hc : c i₀ ≠ 0) :
    (∑ i ∈ T, MvPolynomial.C (c i) * (permSymbolPoly (ν i)).map (Int.castRingHom ℂ)) ≠ 0 := by
  classical
  intro hzero
  apply hc
  have hsum1 : ∑ j, (permMon (ν i₀) (1 : Equiv.Perm (Fin r))) j = ∑ t, ν i₀ t := by
    rw [← permMon_sum (ν i₀) 1]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    rw [Finsupp.mem_support_iff, not_not] at hj; exact hj
  have hsupsum : ∑ k ∈ (permMon (ν i₀) (1 : Equiv.Perm (Fin r))).support,
      (permMon (ν i₀) (1 : Equiv.Perm (Fin r))) k = ∑ t, ν i₀ t := by
    rw [← hsum1]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    rw [Finsupp.mem_support_iff, not_not] at hj; exact hj
  have hcoeff : MvPolynomial.coeff (permMon (ν i₀) 1)
        (∑ i ∈ T, MvPolynomial.C (c i) * (permSymbolPoly (ν i)).map (Int.castRingHom ℂ))
      = ∑ i ∈ T, c i * ((MvPolynomial.coeff (permMon (ν i₀) 1) (permSymbolPoly (ν i)) : ℤ) : ℂ) := by
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]; rfl
  rw [hzero, MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single i₀] at hcoeff
  · have hcard : MvPolynomial.coeff (permMon (ν i₀) 1) (permSymbolPoly (ν i₀))
        = ∑ π : Equiv.Perm (Fin r),
            (if permMon (ν i₀) π = permMon (ν i₀) 1 then (1 : ℤ) else 0) :=
      coeff_permSymbolPoly_eq_card (ν i₀) (permMon (ν i₀) 1) hsum1
    have hpos : (0 : ℤ) < ∑ π : Equiv.Perm (Fin r),
        (if permMon (ν i₀) π = permMon (ν i₀) 1 then (1 : ℤ) else 0) := by
      apply Finset.sum_pos'
      · intro π _; positivity
      · exact ⟨1, Finset.mem_univ 1, by rw [if_pos rfl]; norm_num⟩
    rw [hcard] at hcoeff
    have hcast : (((∑ π : Equiv.Perm (Fin r),
        (if permMon (ν i₀) π = permMon (ν i₀) 1 then (1 : ℤ) else 0)) : ℤ) : ℂ) ≠ 0 :=
      Int.cast_ne_zero.mpr (ne_of_gt hpos)
    rcases mul_eq_zero.mp hcoeff.symm with h | h
    · exact h
    · exact absurd h hcast
  · intro i hi hine
    have hczero : MvPolynomial.coeff (permMon (ν i₀) 1) (permSymbolPoly (ν i)) = 0 := by
      by_cases heq : ∑ t, ν i t = ∑ t, ν i₀ t
      · rw [coeff_permSymbolPoly_eq_card (ν i) (permMon (ν i₀) 1) (by rw [hsum1, heq])]
        apply Finset.sum_eq_zero
        intro π _
        rw [if_neg]
        intro hpm
        apply hine
        apply hdist i hi
        refine ⟨π, fun j => ?_⟩
        have h1 := DFunLike.congr_fun hpm (π j)
        rw [permMon_apply, permMon_apply] at h1
        simpa using h1
      · apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
        rw [hsupsum]
        exact lt_of_le_of_lt (permSymbolPoly_totalDegree_le (ν i))
          (lt_of_le_of_ne (hOle i hi) heq)
    rw [hczero]; simp
  · intro h; exact absurd hi₀ h

end GaloisForLFunctions
