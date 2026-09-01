import GaloisForLFunctions.RHTower.Sieve.StadlmannShiftedGreedy

/-!
# Type-II factor selection in Matomäki--Teräväinen Proposition 2.2

If a product of admissible block scales reaches `τ`, either one factor already lies in `[τ,z]`, or
all factors are below `τ`.  In the second branch, greedy accumulation of their logarithms selects a
subproduct in `[τ,τ²]`.  Thus the source conclusion follows from its numerical relation `τ² ≤ z`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Exact subset-product lemma used to create the short Type-II variable. -/
theorem exists_subset_product_between_threshold_and_cap
    {Q : ℕ → ℝ} {S : Finset ℕ} {τ z : ℝ}
    (hτ : 1 ≤ τ)
    (hQone : ∀ i ∈ S, 1 ≤ Q i)
    (hQcap : ∀ i ∈ S, Q i ≤ z)
    (htotal : τ ≤ ∏ i ∈ S, Q i)
    (hτsq : τ ^ 2 ≤ z) :
    ∃ I ⊆ S, τ ≤ ∏ i ∈ I, Q i ∧ ∏ i ∈ I, Q i ≤ z := by
  by_cases hlarge : ∃ i ∈ S, τ ≤ Q i
  · obtain ⟨i, hiS, hiτ⟩ := hlarge
    refine ⟨{i}, Finset.singleton_subset_iff.mpr hiS, ?_, ?_⟩
    · simpa using hiτ
    · simpa using hQcap i hiS
  · have hsmall : ∀ i ∈ S, Q i < τ := by
      intro i hi
      exact lt_of_not_ge (fun hiτ => hlarge ⟨i, hi, hiτ⟩)
    have hτpos : 0 < τ := zero_lt_one.trans_le hτ
    have hlogTotal : Real.log τ ≤ ∑ i ∈ S, Real.log (Q i) := by
      rw [← Real.log_prod (fun i hi => (zero_lt_one.trans_le (hQone i hi)).ne')]
      exact Real.log_le_log hτpos htotal
    let fill : RHTower.StadlmannShiftedFillData (fun i => Real.log (Q i)) S := {
      stepCap := Real.log τ
      lower := Real.log τ
      upper := Real.log τ + Real.log τ
      base := 0
      stepCap_nonneg := Real.log_nonneg hτ
      width := by ring_nf; exact le_rfl
      base_le_upper := by nlinarith [Real.log_nonneg hτ]
      step_nonneg := fun i hi => Real.log_nonneg (hQone i hi)
      step_le := fun i hi =>
        Real.log_le_log (zero_lt_one.trans_le (hQone i hi)) (hsmall i hi).le
      total := by simpa using hlogTotal
    }
    obtain ⟨I, hIS, hlo, hhi⟩ := fill.exists_subset_in_interval
    dsimp [fill] at hlo hhi
    simp only [zero_add] at hlo hhi
    have hprodPos : 0 < ∏ i ∈ I, Q i := by
      exact Finset.prod_pos fun i hi => zero_lt_one.trans_le (hQone i (hIS hi))
    refine ⟨I, hIS, ?_, ?_⟩
    · calc
        τ = Real.exp (Real.log τ) := (Real.exp_log hτpos).symm
        _ ≤ Real.exp (Real.log (∏ i ∈ I, Q i)) := by
          apply Real.exp_le_exp.mpr
          rw [Real.log_prod (fun i hi => (zero_lt_one.trans_le (hQone i (hIS hi))).ne')]
          exact hlo
        _ = ∏ i ∈ I, Q i := Real.exp_log hprodPos
    · calc
        ∏ i ∈ I, Q i = Real.exp (Real.log (∏ i ∈ I, Q i)) :=
          (Real.exp_log hprodPos).symm
        _ ≤ Real.exp (Real.log τ + Real.log τ) := by
          apply Real.exp_le_exp.mpr
          rw [Real.log_prod (fun i hi => (zero_lt_one.trans_le (hQone i (hIS hi))).ne')]
          exact hhi
        _ = τ ^ 2 := by rw [Real.exp_add, Real.exp_log hτpos]; ring
        _ ≤ z := hτsq

/-- Source exponents `τ = X^(ε/2)` and `z = X^(2/11)` satisfy the selection lemma whenever
`0 ≤ ε ≤ 2/11`. -/
theorem exists_subset_product_in_matomakiTeravainen_typeII_range
    {Q : ℕ → ℝ} {S : Finset ℕ} {X ε : ℝ}
    (hX : 1 ≤ X) (hε0 : 0 ≤ ε) (hε : ε ≤ 2 / 11)
    (hQone : ∀ i ∈ S, 1 ≤ Q i)
    (hQcap : ∀ i ∈ S, Q i ≤ X ^ (2 / 11 : ℝ))
    (htotal : X ^ (ε / 2) ≤ ∏ i ∈ S, Q i) :
    ∃ I ⊆ S,
      X ^ (ε / 2) ≤ ∏ i ∈ I, Q i ∧
        ∏ i ∈ I, Q i ≤ X ^ (2 / 11 : ℝ) := by
  apply exists_subset_product_between_threshold_and_cap
      (hτ := Real.one_le_rpow hX (div_nonneg hε0 (by norm_num))) hQone hQcap htotal
  calc
    (X ^ (ε / 2)) ^ 2 = (X ^ (ε / 2)) ^ (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    _ = X ^ ((ε / 2) * 2) :=
      (Real.rpow_mul (zero_le_one.trans hX) (ε / 2) 2).symm
    _ = X ^ ε := by congr 1; ring
    _ ≤ X ^ (2 / 11 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX hε

/-- Exact small-product/Type-II split in the last line of the proof of Proposition 2.2. -/
theorem matomakiTeravainen_primeBlockProduct_dichotomy
    {Q : ℕ → ℝ} {S : Finset ℕ} {X ε : ℝ}
    (hX : 1 < X) (hε0 : 0 < ε) (hε : ε ≤ 2 / 11)
    (hQone : ∀ i ∈ S, 1 ≤ Q i)
    (hQcap : ∀ i ∈ S, Q i ≤ X ^ (2 / 11 : ℝ)) :
    (∏ i ∈ S, Q i) < X ^ (ε / 2) ∨
      ∃ I ⊆ S, I.Nonempty ∧
        X ^ (ε / 2) ≤ ∏ i ∈ I, Q i ∧
          ∏ i ∈ I, Q i ≤ X ^ (2 / 11 : ℝ) := by
  by_cases hsmall : (∏ i ∈ S, Q i) < X ^ (ε / 2)
  · exact Or.inl hsmall
  · right
    obtain ⟨I, hIS, hlo, hhi⟩ :=
      exists_subset_product_in_matomakiTeravainen_typeII_range
        hX.le hε0.le hε hQone hQcap (le_of_not_gt hsmall)
    have hthreshold : (1 : ℝ) < X ^ (ε / 2) :=
      Real.one_lt_rpow hX (div_pos hε0 (by norm_num))
    have hI : I.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hlo
      simp at hlo
      linarith
    exact ⟨I, hIS, hI, hlo, hhi⟩

end

end RHTower.Sieve
