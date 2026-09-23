import GaloisForLFunctions.RHTower.VonMangoldtConvHarmonicSummatory

/-!
# Block masses of the fiber-averaged Selberg weight

Two bookkeeping primitives for the Erdős–Selberg contraction:

* `abs_sum_selbergWeight_div_sub_le`: the combined evaluation
  `|∑_{m ≤ N} (Λ(m)log m + (Λ*Λ)(m))/m − log²N| ≤ 45·log N + 121`;
* `abs_selbergWeight_block_sub_le`: on a block `(M, M']` the mass is
  `log²M' − log²M` up to `90·log M' + 242`;
* `filter_fiber_eq_Ioc`: the fiber-block identity — the set of `m ≤ N`
  whose fiber `⌊N/m⌋` lies in `(c, c']` is exactly the interval
  `(⌊N/(c'+1)⌋, ⌊N/(c+1)⌋]`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- Fiber-averaged Selberg weight:
`|∑_{m ≤ N} (Λ(m)log m + (Λ*Λ)(m))/m − log²N| ≤ 45 log N + 121`. -/
theorem abs_sum_selbergWeight_div_sub_le (N : ℕ) (hN : 1 ≤ N) :
    |(∑ m ∈ Finset.Icc 1 N,
        (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m) / m)
        - Real.log N ^ (2 : ℕ)| ≤ 45 * Real.log N + 121 := by
  have hsplit : ∀ m ∈ Finset.Icc 1 N,
      (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m) / m
        = vonMangoldt m * Real.log m / m
          + (vonMangoldt * vonMangoldt) m / m := by
    intro m _
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have h1 := abs_le.1 (abs_sum_vonMangoldt_log_div_sub_le N hN)
  have h2 := abs_le.1 (abs_sum_vonMangoldt_conv_div_sub_le N hN)
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rw [abs_le]
  constructor
  · nlinarith [h1.1, h2.1]
  · nlinarith [h1.2, h2.2]

/-- Block mass of the fiber-averaged Selberg weight:
`|∑_{M < m ≤ M'} W(m)/m − (log²M' − log²M)| ≤ 90 log M' + 242`. -/
theorem abs_selbergWeight_block_sub_le {M M' : ℕ} (hM : 1 ≤ M)
    (hMM : M ≤ M') :
    |(∑ m ∈ Finset.Ioc M M',
        (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m) / m)
        - (Real.log M' ^ (2 : ℕ) - Real.log M ^ (2 : ℕ))|
      ≤ 90 * Real.log M' + 242 := by
  have hu : Finset.Icc 1 M' = Finset.Icc 1 M ∪ Finset.Ioc M M' := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 M) (Finset.Ioc M M') := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_Ioc] at hx'
    omega
  have hsum := Finset.sum_union
    (f := fun m => (vonMangoldt m * Real.log m
      + (vonMangoldt * vonMangoldt) m) / (m : ℝ)) hdisj
  rw [← hu] at hsum
  have h1 := abs_le.1 (abs_sum_selbergWeight_div_sub_le M' (le_trans hM hMM))
  have h2 := abs_le.1 (abs_sum_selbergWeight_div_sub_le M hM)
  have hmono : Real.log M ≤ Real.log M' :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < M))
      (by exact_mod_cast hMM)
  have hlM0 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  rw [abs_le]
  constructor
  · nlinarith [h1.1, h2.2, hsum]
  · nlinarith [h1.2, h2.1, hsum]

/-- **Fiber-block identity**: `{m ∈ [1,N] : c < ⌊N/m⌋ ≤ c'}` is the
interval `(⌊N/(c'+1)⌋, ⌊N/(c+1)⌋]`. -/
theorem filter_fiber_eq_Ioc (N c c' : ℕ) :
    (Finset.Icc 1 N).filter (fun m => c < N / m ∧ N / m ≤ c')
      = Finset.Ioc (N / (c' + 1)) (N / (c + 1)) := by
  ext m
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hm1, hmN⟩, hc, hc'⟩
    have hm0 : 0 < m := by omega
    constructor
    · by_contra hcon
      rw [not_lt] at hcon
      have h2 : m * (c' + 1) ≤ N :=
        (Nat.le_div_iff_mul_le (by omega : 0 < c' + 1)).1 hcon
      have h3 : (c' + 1) * m ≤ N := by
        rw [Nat.mul_comm]
        exact h2
      have h4 : c' + 1 ≤ N / m :=
        (Nat.le_div_iff_mul_le hm0).2 h3
      omega
    · have h1 : c + 1 ≤ N / m := by omega
      have h2 : (c + 1) * m ≤ N :=
        (Nat.le_div_iff_mul_le hm0).1 h1
      have h3 : m * (c + 1) ≤ N := by
        rw [Nat.mul_comm]
        exact h2
      exact (Nat.le_div_iff_mul_le (by omega : 0 < c + 1)).2 h3
  · rintro ⟨hlow, hhigh⟩
    have hm0 : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hlow
    have hmN : m ≤ N := le_trans hhigh (Nat.div_le_self N (c + 1))
    have h1 : m * (c + 1) ≤ N :=
      (Nat.le_div_iff_mul_le (by omega : 0 < c + 1)).1 hhigh
    have h1' : (c + 1) * m ≤ N := by
      rw [Nat.mul_comm]
      exact h1
    have h2 : c + 1 ≤ N / m := (Nat.le_div_iff_mul_le hm0).2 h1'
    have h3 : N / m ≤ c' := by
      by_contra hcon
      rw [not_le] at hcon
      have h4 : c' + 1 ≤ N / m := by omega
      have h5 : (c' + 1) * m ≤ N :=
        (Nat.le_div_iff_mul_le hm0).1 h4
      have h5' : m * (c' + 1) ≤ N := by
        rw [Nat.mul_comm]
        exact h5
      have h6 : m ≤ N / (c' + 1) :=
        (Nat.le_div_iff_mul_le (by omega : 0 < c' + 1)).2 h5'
      omega
    exact ⟨⟨by omega, hmN⟩, by omega, h3⟩

end RHTower
