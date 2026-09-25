import GaloisForLFunctions.RHTower.RouteEPositiveQuotientParent

/-!
# Source-specific quotient-parent sign dominance for Route E

For every cofactor and every finite quotient cutoff, the weighted Möbius
sum over coprime quotients `q≥3` is nonpositive with kernel weight
`1/((q+1)(q+2))`. Every positive squarefree quotient has an odd negative
least-prime parent. Charging all possible children to each parent costs at
most `115/126` of its weight, so cutoff and coprimality are preserved without
an analytic Möbius estimate. This is the cross-quotient sign law needed to
control the parity-paired integer-ratio edge family at exponent one; it does
not estimate the remaining noninteger-ratio covariance.
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower

noncomputable section

private def positiveQuotients (d Q : ℕ) : Finset ℕ :=
  (Finset.Icc 3 Q).filter (fun q => d.Coprime q ∧ moebius q = 1)

private def negativeOddQuotients (d Q : ℕ) : Finset ℕ :=
  (Finset.Icc 3 Q).filter (fun u => Odd u ∧ d.Coprime u ∧ moebius u = -1)

private def oddChildFactors (Q : ℕ) : Finset ℕ :=
  (Finset.Icc 3 Q).filter Odd

private def quotientChildren (Q u : ℕ) : Finset ℕ :=
  ({2} ∪ oddChildFactors Q).image (fun p => p * u)

private theorem positiveQuotients_subset_children (d Q : ℕ) :
    positiveQuotients d Q ⊆
      (negativeOddQuotients d Q).biUnion (quotientChildren Q) := by
  intro q hq
  obtain ⟨hqI, hcop, hμ⟩ := Finset.mem_filter.mp hq
  have hq3 := (Finset.mem_Icc.mp hqI).1
  have hqQ := (Finset.mem_Icc.mp hqI).2
  obtain ⟨p, u, hp, hu3, huodd, hqu, hμu, _hmin⟩ :=
    positive_mobius_quotient_has_negative_odd_parent hq3 hμ
  have hudu : u ∣ q := by
    rw [hqu]
    exact dvd_mul_left u p
  have huQ : u ≤ Q :=
    (Nat.le_of_dvd (by omega : 0 < q) hudu).trans hqQ
  have hcopu : d.Coprime u := hcop.coprime_dvd_right hudu
  have huU : u ∈ negativeOddQuotients d Q := by
    simp only [negativeOddQuotients, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hu3, huQ⟩, huodd, hcopu, hμu⟩
  have hpC : p ∈ ({2} ∪ oddChildFactors Q) := by
    by_cases hp2 : p = 2
    · simp [hp2]
    · have hpodd : Odd p := hp.odd_of_ne_two hp2
      have hpQ : p ≤ Q := by
        have hp_dvd : p ∣ q := by rw [hqu]; exact dvd_mul_right p u
        exact (Nat.le_of_dvd (by omega : 0 < q) hp_dvd).trans hqQ
      have hp3 : 3 ≤ p := (hp.odd_iff.mp hpodd)
      simp only [Finset.mem_union, Finset.mem_singleton, oddChildFactors,
        Finset.mem_filter, Finset.mem_Icc]
      exact Or.inr ⟨⟨hp3, hpQ⟩, hpodd⟩
  refine Finset.mem_biUnion.mpr ⟨u, huU, ?_⟩
  exact Finset.mem_image.mpr ⟨p, hpC, hqu.symm⟩

private theorem sum_biUnion_le_of_nonneg
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Finset ℕ)
    (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s.biUnion t, f i ≤ ∑ p ∈ s, ∑ i ∈ t p, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hun : ∑ i ∈ t a ∪ s.biUnion t, f i
        ≤ ∑ i ∈ t a, f i + ∑ i ∈ s.biUnion t, f i := by
      have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have hnn : (0 : ℝ) ≤ ∑ i ∈ t a ∩ s.biUnion t, f i :=
        Finset.sum_nonneg fun i _ => hf i
      linarith
    linarith [hun, ih]

private theorem child_sum_le_parent (w : ℕ → ℝ)
    (hload : ∀ (u : ℕ), 3 ≤ u → (s : Finset ℕ) →
      (∀ p ∈ s, 3 ≤ p ∧ ¬ 2 ∣ p) →
      w (2 * u) + ∑ p ∈ s, w (p * u) ≤ w u)
    (Q u : ℕ) (hu : 3 ≤ u) :
    ∑ q ∈ quotientChildren Q u, w q ≤ w u := by
  classical
  let s := oddChildFactors Q
  have hs : ∀ p ∈ s, 3 ≤ p ∧ ¬ 2 ∣ p := by
    intro p hp
    obtain ⟨hpI, hpodd⟩ := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_Icc.mp hpI).1, Nat.not_even_iff_odd.mpr hpodd ∘ even_iff_two_dvd.mpr⟩
  have h2not : 2 ∉ s := by
    simp [s, oddChildFactors]
  have hinj : Set.InjOn (fun p : ℕ => p * u)
      (↑(({2} : Finset ℕ) ∪ s) : Set ℕ) := by
    intro a ha b hb hab
    exact mul_right_cancel₀ (by omega : u ≠ 0) hab
  calc
    ∑ q ∈ quotientChildren Q u, w q =
        ∑ p ∈ ({2} ∪ s), w (p * u) := by
          simpa [quotientChildren, s] using
            (Finset.sum_image (s := (({2} : Finset ℕ) ∪ s)) (g := fun p => p * u)
              (f := w) hinj)
    _ = w (2 * u) + ∑ p ∈ s, w (p * u) := by
          rw [Finset.sum_union (Finset.disjoint_singleton_left.mpr h2not)]
          simp
    _ ≤ w u := hload u hu s hs

theorem positiveQuotient_mass_le_negativeOdd_of_load (w : ℕ → ℝ)
    (hw : ∀ q, 0 ≤ w q)
    (hload : ∀ (u : ℕ), 3 ≤ u → (s : Finset ℕ) →
      (∀ p ∈ s, 3 ≤ p ∧ ¬ 2 ∣ p) →
      w (2 * u) + ∑ p ∈ s, w (p * u) ≤ w u)
    (d Q : ℕ) :
    ∑ q ∈ positiveQuotients d Q, w q ≤
      ∑ u ∈ negativeOddQuotients d Q, w u := by
  classical
  calc
    _ ≤ ∑ q ∈ (negativeOddQuotients d Q).biUnion (quotientChildren Q), w q :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (positiveQuotients_subset_children d Q) (fun q _ _ => hw q)
    _ ≤ ∑ u ∈ negativeOddQuotients d Q,
          ∑ q ∈ quotientChildren Q u, w q :=
      sum_biUnion_le_of_nonneg _ _ _ hw
    _ ≤ ∑ u ∈ negativeOddQuotients d Q, w u := by
      apply Finset.sum_le_sum
      intro u hu
      exact child_sum_le_parent w hload Q u
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).1

theorem positiveQuotient_mass_le_negativeOdd (d Q : ℕ) :
    ∑ q ∈ positiveQuotients d Q, quotientEdgeWeight q ≤
      ∑ u ∈ negativeOddQuotients d Q, quotientEdgeWeight u :=
  positiveQuotient_mass_le_negativeOdd_of_load quotientEdgeWeight
    quotientEdgeWeight_nonneg
    (fun _u hu s hs => quotientEdgeWeight_parent_load_le_self hu s hs) d Q

/-- Every coprime quotient section beyond 2 has nonpositive signed kernel weight. -/
theorem signedQuotientWeight_le_zero_of_load (w : ℕ → ℝ)
    (hw : ∀ q, 0 ≤ w q)
    (hload : ∀ (u : ℕ), 3 ≤ u → (s : Finset ℕ) →
      (∀ p ∈ s, 3 ≤ p ∧ ¬ 2 ∣ p) →
      w (2 * u) + ∑ p ∈ s, w (p * u) ≤ w u)
    (d Q : ℕ) :
    (∑ q ∈ (Finset.Icc 3 Q).filter (fun q => d.Coprime q),
      (moebius q : ℝ) * w q) ≤ 0 := by
  classical
  let S := Finset.Icc 3 Q
  have hterm (q : ℕ) (hq : q ∈ S) :
      (if d.Coprime q then (moebius q : ℝ) * w q else 0) ≤
        (if d.Coprime q ∧ moebius q = 1 then w q else 0) -
          (if Odd q ∧ d.Coprime q ∧ moebius q = -1 then w q else 0) := by
    by_cases hcop : d.Coprime q
    · by_cases h1 : moebius q = 1
      · simp [h1]
      · by_cases hm : moebius q = -1
        · by_cases hodd : Odd q
          · have hPnot : ¬(d.Coprime q ∧ moebius q = 1) := by simp [h1]
            have hUyes : Odd q ∧ d.Coprime q ∧ moebius q = -1 :=
              ⟨hodd, hcop, hm⟩
            simp only [if_pos hcop, if_neg hPnot, if_pos hUyes]
            rw [hm]
            norm_num
          · have hwq := hw q
            have hPnot : ¬(d.Coprime q ∧ moebius q = 1) := by simp [h1]
            have hUnot : ¬(Odd q ∧ d.Coprime q ∧ moebius q = -1) := by
              simp [hodd]
            simp only [if_pos hcop, if_neg hPnot, if_neg hUnot]
            rw [hm]
            norm_num
            linarith
        · have hzero : moebius q = 0 := by
            by_contra hz
            rcases moebius_ne_zero_iff_eq_or.mp hz with h | h
            · exact h1 h
            · exact hm h
          simp [hzero]
    · simp [hcop]
  have hsum := Finset.sum_le_sum hterm
  have hP : (∑ q ∈ S,
      if d.Coprime q ∧ moebius q = 1 then w q else 0) =
      ∑ q ∈ positiveQuotients d Q, w q := by
    simp [S, positiveQuotients, Finset.sum_filter]
  have hU : (∑ q ∈ S,
      if Odd q ∧ d.Coprime q ∧ moebius q = -1 then w q else 0) =
      ∑ q ∈ negativeOddQuotients d Q, w q := by
    simp [S, negativeOddQuotients, Finset.sum_filter]
  have hsource : (∑ q ∈ S,
      if d.Coprime q then (moebius q : ℝ) * w q else 0) =
      ∑ q ∈ (Finset.Icc 3 Q).filter (fun q => d.Coprime q),
        (moebius q : ℝ) * w q := by
    simp [S, Finset.sum_filter]
  rw [Finset.sum_sub_distrib, hP, hU, hsource] at hsum
  have hmass := positiveQuotient_mass_le_negativeOdd_of_load w hw hload d Q
  linarith

theorem signedQuotientWeight_le_zero (d Q : ℕ) :
    (∑ q ∈ (Finset.Icc 3 Q).filter (fun q => d.Coprime q),
      (moebius q : ℝ) * quotientEdgeWeight q) ≤ 0 :=
  signedQuotientWeight_le_zero_of_load quotientEdgeWeight
    quotientEdgeWeight_nonneg
    (fun _u hu s hs => quotientEdgeWeight_parent_load_le_self hu s hs) d Q

end
end RHTower
