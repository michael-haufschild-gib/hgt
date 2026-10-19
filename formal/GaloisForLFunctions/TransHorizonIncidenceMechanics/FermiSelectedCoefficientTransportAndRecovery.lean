import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiValuationSamplingAndPronicObservability

/-!
# Coefficient transport behind selected Fermi readings

Odd boundaries and doubled even arguments retain every admitted coefficient.
Their normalized readings form a divisor sieve after an explicit dyadic
coefficient transport. The transport's inverse energy is bounded by `3/2`;
an exact square completion records the residual on each valuation chain.
-/

open Finset
open RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- Coefficient transport induced by selecting odd and four-divisible boundaries. -/
def fermiSelectedCoefficient (N : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  if 2 ∣ d then
    (if 4 ∣ d then 2 else 1) * c d - (if 2 * d ≤ N then c (2 * d) else 0)
  else c d

/-- Valuation residual in the inverse coefficient-energy identity. -/
def fermiAliasResidual (N : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  if 2 ∣ d then
    (if 4 ∣ d then 2 else 1) * c d - 3 * (if 2 * d ≤ N then c (2 * d) else 0)
  else c d

/-- The positive sieve argument `n+1` selects an odd boundary or its even double. -/
def fermiSelectedReading (N : ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 2 ∣ n + 1 then fermiBoundaryJump N c (2 * (n + 1))
  else -fermiBoundaryJump N c (n + 1)

private theorem even_dilation_sieve (N n : ℕ) (f : ℕ → ℝ) :
    sieveSeq N (fun d => if 2 ∣ d ∧ 2 * d ≤ N then f (2 * d) else 0) n =
      sieveSeq N (fun d => if 4 ∣ d then f d else 0) (2 * n) := by
  unfold sieveSeq
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun d _ => 2 * d)
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
    obtain ⟨⟨⟨hdpos, _⟩, hdn⟩, hd2, hdN⟩ := hd
    refine ⟨⟨⟨by omega, hdN⟩, Nat.mul_dvd_mul_left 2 hdn⟩, ?_⟩
    obtain ⟨k, hk⟩ := hd2
    exact ⟨k, by omega⟩
  · intro a _ b _ h
    omega
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_Icc] at he
    obtain ⟨⟨⟨hepos, heN⟩, hen⟩, he4⟩ := he
    obtain ⟨k, hk⟩ := he4
    have heq : e = 2 * (2 * k) := by omega
    rw [heq] at hen
    have hkn : 2 * k ∣ n := (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp hen
    refine ⟨2 * k, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨by omega, by omega⟩, hkn⟩, ⟨k, rfl⟩, by omega⟩
  · intro d _
    rfl

private theorem coefficient_square_completion (N : ℕ) (c : ℕ → ℝ) (d : ℕ) :
    3 * fermiSelectedCoefficient N c d ^ 2 - 2 * c d ^ 2 -
        fermiAliasResidual N c d ^ 2 =
      6 * (if 4 ∣ d then c d ^ 2 else 0) -
        6 * (if 2 ∣ d ∧ 2 * d ≤ N then c (2 * d) ^ 2 else 0) := by
  unfold fermiSelectedCoefficient fermiAliasResidual
  split_ifs <;> first | omega | ring

/-- Exact positive residual of the inverse coefficient-energy estimate. -/
theorem fermiSelectedCoefficient_energy_slack (N : ℕ) (c : ℕ → ℝ) :
    3 * (∑ d ∈ Finset.Icc 1 N, fermiSelectedCoefficient N c d ^ 2) -
        2 * (∑ d ∈ Finset.Icc 1 N, c d ^ 2) =
      ∑ d ∈ Finset.Icc 1 N, fermiAliasResidual N c d ^ 2 := by
  have hd : (∑ d ∈ Finset.Icc 1 N,
      if 2 ∣ d ∧ 2 * d ≤ N then c (2 * d) ^ 2 else 0) =
      ∑ d ∈ Finset.Icc 1 N, if 4 ∣ d then c d ^ 2 else 0 := by
    simpa [sieveSeq] using even_dilation_sieve N 0 (fun d => c d ^ 2)
  have hsum := Finset.sum_congr (s₁ := Finset.Icc 1 N) rfl
    (fun d _ => coefficient_square_completion N c d)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [hd] at hsum
  linarith

/-- Arithmetic inversion of the selected readings loses at most a factor `3/2` in coefficient energy. -/
theorem fermiSelectedCoefficient_energy_bound (N : ℕ) (c : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 N, c d ^ 2) ≤
      (3 / 2 : ℝ) * ∑ d ∈ Finset.Icc 1 N, fermiSelectedCoefficient N c d ^ 2 := by
  have h := fermiSelectedCoefficient_energy_slack N c
  have hn : 0 ≤ ∑ d ∈ Finset.Icc 1 N, fermiAliasResidual N c d ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

/-- No nonzero admitted coefficient vector is erased by the dyadic transport. -/
theorem fermiSelectedCoefficient_zero_iff (N : ℕ) (c : ℕ → ℝ) :
    (∀ d ∈ Finset.Icc 1 N, fermiSelectedCoefficient N c d = 0) ↔
      ∀ d ∈ Finset.Icc 1 N, c d = 0 := by
  constructor
  · intro hb
    have hbs : (∑ d ∈ Finset.Icc 1 N, fermiSelectedCoefficient N c d ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [hb d hd]
      norm_num
    have h := fermiSelectedCoefficient_energy_bound N c
    rw [hbs] at h
    have hn : 0 ≤ ∑ d ∈ Finset.Icc 1 N, c d ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hz : (∑ d ∈ Finset.Icc 1 N, c d ^ 2) = 0 := by linarith
    have hp := (Finset.sum_eq_zero_iff_of_nonneg (fun d _ => sq_nonneg (c d))).mp hz
    intro d hd
    have := hp d hd
    nlinarith
  · intro hc d hd
    unfold fermiSelectedCoefficient
    rw [hc d hd]
    by_cases hN : 2 * d ≤ N
    · have h2d : 2 * d ∈ Finset.Icc 1 N :=
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega, hN⟩
      rw [hc (2 * d) h2d]
      split_ifs <;> ring
    · simp [hN]

private theorem coefficient_decomposition (N : ℕ) (c : ℕ → ℝ) (d : ℕ) :
    fermiSelectedCoefficient N c d =
      c d + (if 4 ∣ d then c d else 0) -
        (if 2 ∣ d ∧ 2 * d ≤ N then c (2 * d) else 0) := by
  unfold fermiSelectedCoefficient
  split_ifs <;> first | omega | ring

private theorem transported_sieve (N n : ℕ) (c : ℕ → ℝ) :
    sieveSeq N (fermiSelectedCoefficient N c) n =
      sieveSeq N c n + sieveSeq N (fun d => if 4 ∣ d then c d else 0) n -
        sieveSeq N (fun d => if 4 ∣ d then c d else 0) (2 * n) := by
  have h : sieveSeq N (fermiSelectedCoefficient N c) n =
      sieveSeq N c n + sieveSeq N (fun d => if 4 ∣ d then c d else 0) n -
        sieveSeq N (fun d => if 2 ∣ d ∧ 2 * d ≤ N then c (2 * d) else 0) n := by
    simp only [sieveSeq, coefficient_decomposition, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
  rw [h, even_dilation_sieve]

private theorem sieve_four_split (N n : ℕ) (c : ℕ → ℝ) :
    sieveSeq N c n = sieveSeq N (fermiFourFreeWeight c) n +
      sieveSeq N (fun d => if 4 ∣ d then c d else 0) n := by
  unfold sieveSeq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simp only [fermiFourFreeWeight]
  split_ifs <;> ring

private theorem sieve_four_part_zero (N : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : ¬4 ∣ n) :
    sieveSeq N (fun d => if 4 ∣ d then c d else 0) n = 0 := by
  unfold sieveSeq
  apply Finset.sum_eq_zero
  intro d hd
  exact if_neg (fun h4 => hn (h4.trans (Finset.mem_filter.mp hd).2))

/-- The physical selected trace is the literal sieve of its transported coefficients. -/
theorem fermiSelectedReading_eq_sieveSeq (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    fermiSelectedReading N c n = sieveSeq N (fermiSelectedCoefficient N c) (n + 1) := by
  have ht := transported_sieve N (n + 1) c
  unfold fermiSelectedReading
  by_cases h2 : 2 ∣ n + 1
  · rw [if_pos h2]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n + 1 = 2 * m + 2 :=
      ⟨(n + 1) / 2 - 1, by omega⟩
    have hs : sieveSeq N (fermiFourFreeWeight c) (2 * (n + 1)) =
        sieveSeq N (fermiFourFreeWeight c) (n + 1) := by
      have h := fermiBoundaryJump_four_sub_eq_sieve_difference N (fermiFourFreeWeight c) m
      rw [fermiBoundaryJump_four_fourFreeWeight] at h
      rw [hm, show 2 * (2 * m + 2) = 4 * m + 4 by omega]
      linarith
    have h1 := sieve_four_split N (n + 1) c
    have h2n := sieve_four_split N (2 * (n + 1)) c
    rw [hs] at h2n
    have hj := fermiBoundaryJump_even N c n
    rw [← show 2 * (n + 1) = 2 * n + 2 by omega] at hj
    linarith
  · rw [if_neg h2]
    have hj : -fermiBoundaryJump N c (n + 1) = sieveSeq N c (n + 1) := by
      rw [show n + 1 = 2 * (n / 2) + 1 by omega, fermiBoundaryJump_odd, neg_neg]
    have h1 := sieve_four_part_zero N c (by omega : ¬4 ∣ n + 1)
    have h2n := sieve_four_part_zero N c (by omega : ¬4 ∣ 2 * (n + 1))
    rw [hj]
    rw [h1, h2n] at ht
    linarith

/-- The first `N` selected readings detect every admitted coefficient, without a support premise. -/
theorem fermiSelectedReading_zero_iff (N : ℕ) (c : ℕ → ℝ) :
    (∀ n < N, fermiSelectedReading N c n = 0) ↔
      ∀ d ∈ Finset.Icc 1 N, c d = 0 := by
  constructor
  · intro hr
    have hs : ∀ d ∈ Finset.Icc 1 N, sieveSeq N (fermiSelectedCoefficient N c) d = 0 := by
      intro d hd
      have hdpos := (Finset.mem_Icc.mp hd).1
      have hdN := (Finset.mem_Icc.mp hd).2
      have h := hr (d - 1) (by omega)
      rw [fermiSelectedReading_eq_sieveSeq, show d - 1 + 1 = d by omega] at h
      exact h
    apply (fermiSelectedCoefficient_zero_iff N c).mp
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro hd
      have hdpos := (Finset.mem_Icc.mp hd).1
      have hsum : sieveSeq N (fermiSelectedCoefficient N c) d =
          fermiSelectedCoefficient N c d := by
        unfold sieveSeq
        apply Finset.sum_eq_single d
        · intro k hk hkd
          have hkN := (Finset.mem_filter.mp hk).1
          have hkle := Nat.le_of_dvd (by omega : 0 < d) (Finset.mem_filter.mp hk).2
          exact ih k (by omega) hkN
        · intro hn
          exact (hn (Finset.mem_filter.mpr ⟨hd, dvd_refl d⟩)).elim
      rw [← hsum]
      exact hs d hd
  · intro hc n hn
    rw [fermiSelectedReading_eq_sieveSeq]
    unfold sieveSeq
    apply Finset.sum_eq_zero
    intro d hd
    exact (fermiSelectedCoefficient_zero_iff N c).mpr hc d (Finset.mem_filter.mp hd).1

private theorem selected_coefficient_sub (N : ℕ) (c b : ℕ → ℝ) (d : ℕ) :
    fermiSelectedCoefficient N (fun d => c d - b d) d =
      fermiSelectedCoefficient N c d - fermiSelectedCoefficient N b d := by
  unfold fermiSelectedCoefficient
  split_ifs <;> ring

private theorem selected_reading_sub (N : ℕ) (c b : ℕ → ℝ) (n : ℕ) :
    fermiSelectedReading N (fun d => c d - b d) n =
      fermiSelectedReading N c n - fermiSelectedReading N b n := by
  simp only [fermiSelectedReading_eq_sieveSeq, sieveSeq, selected_coefficient_sub,
    Finset.sum_sub_distrib]

/-- Equality of the finite physical traces is exactly equality of the admitted coefficients. -/
theorem fermiSelectedReading_eq_iff (N : ℕ) (c b : ℕ → ℝ) :
    (∀ n < N, fermiSelectedReading N c n = fermiSelectedReading N b n) ↔
      ∀ d ∈ Finset.Icc 1 N, c d = b d := by
  have h := fermiSelectedReading_zero_iff N (fun d => c d - b d)
  simpa only [selected_reading_sub, sub_eq_zero] using h

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
