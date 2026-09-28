import GaloisForLFunctions.RHTower.MobiusDivisorSectionSignLaw

/-!
# The divisor-comparable Möbius section is nonpositive against every monotone kernel

For `N, K : ℕ` let `C_N(K)` be the Möbius-signed number of divisor pairs `m ∣ n`, `m < n ≤ N`,
below the anti-diagonal `m + n ≤ K`.  Then `C_N(K) ≤ 0` for all `N` and `K`; more precisely, with
`N' = min N (K - 1)`, `C_N(K)` is at most minus the number of squarefree integers in `(N'/2, N']`.

*Proof.*  Only rows `n ≤ K - 1` meet the half-plane, so assume `N < K`.  A row with `2n ≤ K`
contains all proper divisors and equals `-μ(n)²`.  For squarefree `n` with `2n > K`, the complement
`e = n/m` turns the row into `-∑_{e ∣ n, n/e + n > K} μ(e)`.  Terms with `e = 1` are `-1`.  A term
with `e ≥ 2` is sent to its cofactor `j = n/e`; this map is injective, because two admissible
`e < e'` for the same `j` would give `j(e+1) ≤ je' ≤ N < K < j(e+1)`, and its image consists of
squarefree `2 ≤ j ≤ N/2`.  Those `j` are already rows with `2j ≤ K`, each contributing `-1`.

By Abel summation, for every nonincreasing nonnegative weight `w`,

`∑_{m ∣ n, m < n ≤ N} μ(m)μ(n) w(m+n) ≤ 0`.

In particular the divisor section of the Gamma--Hankel covariance is nonpositive at every exponent
`r > 0`, and `∑_{m ∣ n, m < n ≤ N} μ(m)μ(n) q^{m+n} ≤ 0` for every `0 ≤ q ≤ 1`.

The anti-diagonal is essential: `m + n = j(e+1)` is the next multiple of `j = m` after `n = je`,
which is what makes the complement map injective.
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Möbius-signed divisor pairs of the row `n` below the anti-diagonal `m + n ≤ K`. -/
def divisorPairRowBelow (K n : ℕ) : ℝ :=
  ∑ m ∈ n.properDivisors.filter (fun m => m + n ≤ K),
    mobiusRealCoefficient m * mobiusRealCoefficient n

/-- The signed divisor-pair count `C_N(K)`. -/
def divisorPairCountBelow (N K : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, divisorPairRowBelow K n

private theorem mobiusRealCoefficient_sq_of_squarefree {n : ℕ} (hn : Squarefree n) :
    mobiusRealCoefficient n ^ 2 = 1 := by
  have hne : moebius n ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hn
  rcases moebius_ne_zero_iff_eq_or.mp hne with hm | hm <;>
    simp [mobiusRealCoefficient, hm]

private theorem mobiusRealCoefficient_eq_zero_of_not_squarefree {n : ℕ} (hn : ¬Squarefree n) :
    mobiusRealCoefficient n = 0 := by
  simp [mobiusRealCoefficient, moebius_eq_zero_of_not_squarefree hn]

private theorem abs_mobiusRealCoefficient_le_one (n : ℕ) : |mobiusRealCoefficient n| ≤ 1 := by
  unfold mobiusRealCoefficient
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- Proper-divisor Möbius sum: `∑_{m ∣ n, m < n} μ(m) = -μ(n)` for `n ≥ 2`. -/
private theorem sum_properDivisors_mobius {n : ℕ} (hn : 2 ≤ n) :
    (∑ m ∈ n.properDivisors, mobiusRealCoefficient m) = -mobiusRealCoefficient n := by
  have hn0 : n ≠ 0 := by omega
  have htot := sum_divisors_mobiusRealCoefficient_eq_zero (show n ≠ 1 by omega)
  rw [← Nat.cons_self_properDivisors hn0, Finset.sum_cons] at htot
  linarith

/-- Full row: if `2n ≤ K` the row is `-μ(n)²`. -/
theorem divisorPairRowBelow_of_two_mul_le {K n : ℕ} (hn : 2 ≤ n) (hK : 2 * n ≤ K) :
    divisorPairRowBelow K n = -mobiusRealCoefficient n ^ 2 := by
  unfold divisorPairRowBelow
  have hfilter : n.properDivisors.filter (fun m => m + n ≤ K) = n.properDivisors := by
    apply Finset.filter_true_of_mem
    intro m hm
    have := Nat.mem_properDivisors.mp hm
    omega
  rw [hfilter, ← Finset.sum_mul, sum_properDivisors_mobius hn]
  ring

/-- Partial row: for squarefree `n` with `K < 2n`, the complement `e = n/m` rewrites the row. -/
theorem divisorPairRowBelow_eq_complement {K n : ℕ} (hsf : Squarefree n) (hn : 2 ≤ n)
    (hK : K < 2 * n) :
    divisorPairRowBelow K n =
      -∑ e ∈ n.divisors.filter (fun e => K < n / e + n), mobiusRealCoefficient e := by
  have hn0 : n ≠ 0 := by omega
  unfold divisorPairRowBelow
  -- below the anti-diagonal every divisor is proper
  have hfilter : n.properDivisors.filter (fun m => m + n ≤ K) =
      n.divisors.filter (fun m => m + n ≤ K) := by
    ext m
    simp only [Finset.mem_filter, Nat.mem_properDivisors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdvd, _⟩, hle⟩
      exact ⟨⟨hdvd, hn0⟩, hle⟩
    · rintro ⟨⟨hdvd, _⟩, hle⟩
      exact ⟨⟨hdvd, by omega⟩, hle⟩
  rw [hfilter, ← Finset.sum_mul]
  -- the full divisor sum vanishes
  have htot := sum_divisors_mobiusRealCoefficient_eq_zero (show n ≠ 1 by omega)
  have hsplit := Finset.sum_filter_add_sum_filter_not n.divisors (fun m => m + n ≤ K)
    mobiusRealCoefficient
  rw [htot] at hsplit
  have hbelow : (∑ m ∈ n.divisors.filter (fun m => m + n ≤ K), mobiusRealCoefficient m) =
      -∑ m ∈ n.divisors.filter (fun m => ¬(m + n ≤ K)), mobiusRealCoefficient m := by
    linarith
  rw [hbelow]
  -- complement reindexing `m = n / e`
  have hflip : (∑ m ∈ n.divisors.filter (fun m => ¬(m + n ≤ K)),
        mobiusRealCoefficient m * mobiusRealCoefficient n) =
      ∑ e ∈ n.divisors.filter (fun e => K < n / e + n), mobiusRealCoefficient e := by
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [← Nat.sum_div_divisors n (fun m =>
      if ¬(m + n ≤ K) then mobiusRealCoefficient m * mobiusRealCoefficient n else 0)]
    apply Finset.sum_congr rfl
    intro e he
    have hdvd := Nat.dvd_of_mem_divisors he
    have hepos := Nat.pos_of_mem_divisors he
    obtain ⟨j, hj⟩ := hdvd
    have hsq : Squarefree (e * j) := hj ▸ hsf
    have hcop : e.Coprime j := (Nat.squarefree_mul_iff.mp hsq).1
    have hsqj : Squarefree j := (Nat.squarefree_mul_iff.mp hsq).2.2
    have hdiv : n / e = j := by rw [hj, Nat.mul_div_cancel_left j hepos]
    have hμn : mobiusRealCoefficient n = mobiusRealCoefficient e * mobiusRealCoefficient j := by
      rw [hj]
      unfold mobiusRealCoefficient
      rw [Sieve.moebius_mul_of_coprime hcop]
      push_cast
      ring
    rw [hdiv]
    by_cases hc : K < j + n
    · rw [if_pos (by omega), if_pos hc, hμn]
      have := mobiusRealCoefficient_sq_of_squarefree hsqj
      linear_combination (mobiusRealCoefficient e) * this
    · rw [if_neg (by omega), if_neg hc]
  rw [neg_mul, Finset.sum_mul, hflip]

/-- **Discrete sign law with drift.**  With `N' = min N (K - 1)`,
`C_N(K) ≤ -(#{squarefree n ∈ [2, N']} - #{squarefree n ∈ [2, N'/2]})`, a negative multiple of the
number of squarefree integers in `(N'/2, N']`. -/
theorem divisorPairCountBelow_le (N K : ℕ) :
    divisorPairCountBelow N K ≤
      -((((Finset.Icc 2 (min N (K - 1))).filter Squarefree).card : ℝ) -
        (((Finset.Icc 2 (min N (K - 1) / 2)).filter Squarefree).card : ℝ)) := by
  -- rows with `n ≥ K` are empty below the anti-diagonal
  have hempty : ∀ n, K ≤ n → divisorPairRowBelow K n = 0 := by
    intro n hn
    unfold divisorPairRowBelow
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2
    have hm1 : 1 ≤ m := Nat.pos_of_mem_properDivisors (Finset.mem_filter.mp hm).1
    omega
  -- reduce to `N < K`
  set N' : ℕ := min N (K - 1) with hN'
  have hreduce : divisorPairCountBelow N K = divisorPairCountBelow N' K := by
    unfold divisorPairCountBelow
    by_cases hNK : N ≤ K - 1
    · rw [hN', min_eq_left hNK]
    · have hsub : Finset.Icc 1 N' ⊆ Finset.Icc 1 N := by
        apply Finset.Icc_subset_Icc le_rfl
        rw [hN']
        exact min_le_left _ _
      rw [← Finset.sum_subset hsub]
      intro n hn hn'
      apply hempty
      simp only [Finset.mem_Icc] at hn hn'
      rw [hN'] at hn'
      omega
  rw [hreduce]
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · have hN'0 : N' = 0 := by rw [hN']; omega
    have hC : divisorPairCountBelow N' K = 0 := by
      unfold divisorPairCountBelow
      apply Finset.sum_eq_zero
      intro n hn
      exact hempty n (by omega)
    rw [hC, hN'0, Nat.zero_div, Finset.Icc_eq_empty (by norm_num)]
    simp
  have hNK : N' < K := by rw [hN']; omega
  -- split into full and partial rows
  unfold divisorPairCountBelow
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N') (fun n => 2 * n ≤ K)]
  set Full : Finset ℕ := (Finset.Icc 2 N').filter (fun n => 2 * n ≤ K ∧ Squarefree n)
    with hFull
  set Half : Finset ℕ := (Finset.Icc 2 (N' / 2)).filter Squarefree with hHalf
  -- full rows sum to `-#Full`
  have hfullRows : (∑ n ∈ (Finset.Icc 1 N').filter (fun n => 2 * n ≤ K),
      divisorPairRowBelow K n) = -(Full.card : ℝ) := by
    have hrow : ∀ n ∈ (Finset.Icc 1 N').filter (fun n => 2 * n ≤ K),
        divisorPairRowBelow K n = -(if n ∈ Full then (1 : ℝ) else 0) := by
      intro n hn
      obtain ⟨hnI, hn2K⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnI
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · have : n = 1 := by omega
        subst this
        have hnot : (1 : ℕ) ∉ Full := by simp [hFull]
        simp [divisorPairRowBelow, hnot]
      · rw [divisorPairRowBelow_of_two_mul_le hge hn2K]
        by_cases hsf : Squarefree n
        · have hmem : n ∈ Full := by
            simp only [hFull, Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨hge, hnN⟩, hn2K, hsf⟩
          rw [if_pos hmem, mobiusRealCoefficient_sq_of_squarefree hsf]
        · have hmem : n ∉ Full := by
            simp only [hFull, Finset.mem_filter, Finset.mem_Icc]
            tauto
          rw [if_neg hmem, mobiusRealCoefficient_eq_zero_of_not_squarefree hsf]
          ring
    rw [Finset.sum_congr rfl hrow, Finset.sum_neg_distrib, ← Finset.sum_filter]
    congr 1
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    congr 1
    ext n
    simp only [hFull, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨_, hnN⟩, hn2K⟩, ⟨hge, _⟩, _, hsf⟩
      exact ⟨⟨hge, hnN⟩, hn2K, hsf⟩
    · rintro ⟨⟨hge, hnN⟩, hn2K, hsf⟩
      exact ⟨⟨⟨by omega, hnN⟩, hn2K⟩, ⟨hge, hnN⟩, hn2K, hsf⟩
  -- partial rows are bounded by `#Half`
  set E1 : Finset ℕ := (Finset.Icc 1 N').filter (fun n => ¬(2 * n ≤ K) ∧ Squarefree n)
    with hE1
  set S : Finset (Σ _ : ℕ, ℕ) :=
    E1.sigma (fun n => n.divisors.filter (fun e => K < n / e + n)) with hS
  have hpartialEq : (∑ n ∈ (Finset.Icc 1 N').filter (fun n => ¬(2 * n ≤ K)),
      divisorPairRowBelow K n) = -∑ p ∈ S, mobiusRealCoefficient p.2 := by
    rw [hS, hE1, Finset.sum_sigma, ← Finset.sum_neg_distrib]
    rw [← Finset.sum_filter_add_sum_filter_not
      ((Finset.Icc 1 N').filter (fun n => ¬(2 * n ≤ K))) Squarefree]
    have hnonsf : (∑ n ∈ ((Finset.Icc 1 N').filter (fun n => ¬(2 * n ≤ K))).filter
        (fun n => ¬Squarefree n), divisorPairRowBelow K n) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hsf := (Finset.mem_filter.mp hn).2
      unfold divisorPairRowBelow
      apply Finset.sum_eq_zero
      intro m _
      rw [mobiusRealCoefficient_eq_zero_of_not_squarefree hsf, mul_zero]
    rw [hnonsf, add_zero, Finset.filter_filter]
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hnI, hn2K, hsf⟩ := Finset.mem_filter.mp hn
    have hn2 : 2 ≤ n := by
      have h1 := (Finset.mem_Icc.mp hnI).1
      have h2 := (Finset.mem_Icc.mp hnI).2
      omega
    exact divisorPairRowBelow_eq_complement hsf hn2 (by omega)
  have hpartialLe : -∑ p ∈ S, mobiusRealCoefficient p.2 ≤ -(E1.card : ℝ) + (Half.card : ℝ) := by
    -- each partial row has exactly one term with `e = 1`; the others inject into `Half`
    have hcardOne : (S.filter (fun p => p.2 = 1)).card = E1.card := by
      apply Finset.card_bij (fun p _ => p.1)
      · intro p hp
        have hpS := (Finset.mem_filter.mp hp).1
        rw [hS, Finset.mem_sigma] at hpS
        exact hpS.1
      · intro p hp q hq hpq
        have hp1 := (Finset.mem_filter.mp hp).2
        have hq1 := (Finset.mem_filter.mp hq).2
        exact Sigma.ext hpq (heq_of_eq (hp1.trans hq1.symm))
      · intro n hn
        refine ⟨⟨n, 1⟩, ?_, rfl⟩
        have hn' := hn
        rw [hE1, Finset.mem_filter, Finset.mem_Icc] at hn'
        refine Finset.mem_filter.mpr ⟨?_, rfl⟩
        rw [hS, Finset.mem_sigma]
        refine ⟨hn, Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (show n ≠ 0 by omega), ?_⟩⟩
        show K < n / 1 + n
        rw [Nat.div_one]
        omega
    rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p.2 = 1)]
    have hone : (∑ p ∈ S.filter (fun p => p.2 = 1), mobiusRealCoefficient p.2) =
        ((S.filter (fun p => p.2 = 1)).card : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
      simp [mobiusRealCoefficient]
    have hrest : -(∑ p ∈ S.filter (fun p => ¬p.2 = 1), mobiusRealCoefficient p.2) ≤
        ((S.filter (fun p => ¬p.2 = 1)).card : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro p _
      have := abs_mobiusRealCoefficient_le_one p.2
      push_cast
      linarith [neg_abs_le (mobiusRealCoefficient p.2)]
    have hinj : (S.filter (fun p => ¬p.2 = 1)).card ≤ Half.card := by
      apply Finset.card_le_card_of_injOn (fun p => p.1 / p.2)
      · intro p hp
        obtain ⟨hpS, hpe⟩ := Finset.mem_filter.mp hp
        simp only [hS, hE1, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hpS
        obtain ⟨⟨⟨hn1, hnN⟩, hn2K, hsf⟩, he, hKlt⟩ := hpS
        have hdvd := Nat.dvd_of_mem_divisors he
        have hepos := Nat.pos_of_mem_divisors he
        have he2 : 2 ≤ p.2 := by omega
        obtain ⟨j, hj⟩ := hdvd
        have hdiv : p.1 / p.2 = j := by rw [hj, Nat.mul_div_cancel_left j hepos]
        have hsq : Squarefree (p.2 * j) := hj ▸ hsf
        have hsqj : Squarefree j := (Nat.squarefree_mul_iff.mp hsq).2.2
        show p.1 / p.2 ∈ Half
        rw [hHalf, hdiv]
        rw [hdiv] at hKlt
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hsqj⟩
        · -- `j ≤ 1` would force `n ≥ K > N'`
          by_contra hj2
          rcases (show j = 0 ∨ j = 1 by omega) with h0 | h1
          · rw [h0, mul_zero] at hj
            omega
          · rw [h1, mul_one] at hj
            rw [h1] at hKlt
            omega
        · rw [Nat.le_div_iff_mul_le (by norm_num)]
          have h2j : 2 * j ≤ p.2 * j := Nat.mul_le_mul_right j he2
          omega
      · intro p hp q hq hpq
        obtain ⟨hpS, hpe⟩ := Finset.mem_filter.mp hp
        obtain ⟨hqS, hqe⟩ := Finset.mem_filter.mp hq
        simp only [hS, hE1, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hpS hqS
        obtain ⟨⟨⟨_, hpN⟩, _, _⟩, hpd, hpK⟩ := hpS
        obtain ⟨⟨⟨_, hqN⟩, _, _⟩, hqd, hqK⟩ := hqS
        simp only at hpq
        obtain ⟨j, hj⟩ := Nat.dvd_of_mem_divisors hpd
        obtain ⟨j', hj'⟩ := Nat.dvd_of_mem_divisors hqd
        have hppos := Nat.pos_of_mem_divisors hpd
        have hqpos := Nat.pos_of_mem_divisors hqd
        have hdp : p.1 / p.2 = j := by rw [hj, Nat.mul_div_cancel_left j hppos]
        have hdq : q.1 / q.2 = j' := by rw [hj', Nat.mul_div_cancel_left j' hqpos]
        rw [hdp, hdq] at hpq
        subst hpq
        rw [hdp] at hpK
        rw [hdq] at hqK
        have he : p.2 = q.2 := by
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
          · -- `j (e+1) ≤ j e' = q.1 ≤ N' < K < j + p.1 = j (e+1)`
            have : j * (p.2 + 1) ≤ j * q.2 := Nat.mul_le_mul_left _ hlt
            nlinarith
          · have : j * (q.2 + 1) ≤ j * p.2 := Nat.mul_le_mul_left _ hlt
            nlinarith
        have h1 : p.1 = q.1 := by rw [hj, hj', he]
        exact Sigma.ext h1 (heq_of_eq he)
    have hcard : ((S.filter (fun p => ¬p.2 = 1)).card : ℝ) ≤ (Half.card : ℝ) := by
      exact_mod_cast hinj
    rw [neg_add, hone, hcardOne]
    linarith
  -- full and partial squarefree rows together are the squarefree integers of `[2, N']`
  have hsplit : (Full.card : ℝ) + (E1.card : ℝ) =
      (((Finset.Icc 2 N').filter Squarefree).card : ℝ) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.Icc 2 N').filter Squarefree) (fun n => 2 * n ≤ K)
    have hF : Full = ((Finset.Icc 2 N').filter Squarefree).filter (fun n => 2 * n ≤ K) := by
      rw [hFull]
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      tauto
    have hE : E1 = ((Finset.Icc 2 N').filter Squarefree).filter (fun n => ¬(2 * n ≤ K)) := by
      rw [hE1]
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, h4⟩
        exact ⟨⟨⟨by omega, h2⟩, h4⟩, h3⟩
      · rintro ⟨⟨⟨_, h2⟩, h4⟩, h3⟩
        exact ⟨⟨by omega, h2⟩, h3, h4⟩
    rw [hF, hE]
    exact_mod_cast h
  rw [hfullRows, hpartialEq]
  linarith

/-- **Discrete sign law.**  `C_N(K) ≤ 0` for all `N` and `K`. -/
theorem divisorPairCountBelow_nonpos (N K : ℕ) : divisorPairCountBelow N K ≤ 0 := by
  refine (divisorPairCountBelow_le N K).trans ?_
  have hsub : (Finset.Icc 2 (min N (K - 1) / 2)).filter Squarefree ⊆
      (Finset.Icc 2 (min N (K - 1))).filter Squarefree :=
    Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl (Nat.div_le_self _ _))
  have hcard : (((Finset.Icc 2 (min N (K - 1) / 2)).filter Squarefree).card : ℝ) ≤
      (((Finset.Icc 2 (min N (K - 1))).filter Squarefree).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  linarith

/-- Layer-cake summation against a weight on `ℕ`: for `g ≤ L` on `s`,
`∑ f(a) w(g a) = w L ∑ f + ∑_{K < L} (w K - w (K+1)) ∑_{g a ≤ K} f(a)`. -/
theorem sum_mul_weight_eq_layerCake {α : Type*} (s : Finset α) (f : α → ℝ) (g : α → ℕ)
    (w : ℕ → ℝ) (L : ℕ) (hg : ∀ a ∈ s, g a ≤ L) :
    ∑ a ∈ s, f a * w (g a) =
      w L * ∑ a ∈ s, f a +
        ∑ K ∈ Finset.range L, (w K - w (K + 1)) * ∑ a ∈ s.filter (fun a => g a ≤ K), f a := by
  have hlayer : ∀ k, k ≤ L → w k =
      w L + ∑ K ∈ Finset.range L, (if k ≤ K then w K - w (K + 1) else 0) := by
    intro k hk
    have htel : (∑ K ∈ Finset.Ico k L, (w K - w (K + 1))) = w k - w L := by
      rw [Finset.sum_Ico_eq_sum_range]
      have := Finset.sum_range_sub' (fun i => w (k + i)) (L - k)
      simp only [add_zero, Nat.add_sub_cancel' hk] at this
      exact this
    have hfilt : (∑ K ∈ Finset.range L, (if k ≤ K then w K - w (K + 1) else 0)) =
        ∑ K ∈ Finset.Ico k L, (w K - w (K + 1)) := by
      rw [← Finset.sum_filter]
      congr 1
      ext K
      simp [Finset.mem_Ico, and_comm]
    rw [hfilt, htel]
    ring
  simp_rw [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range L), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hlayer (g a) (hg a ha), mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro K _
    split_ifs <;> ring

/-- **Monotone-kernel sign law.**  For every nonincreasing nonnegative weight `w`, the
divisor-comparable Möbius section `∑_{m ∣ n, m < n ≤ N} μ(m)μ(n) w(m+n)` is nonpositive. -/
theorem sum_divisorPairs_antitone_weight_nonpos (N : ℕ) {w : ℕ → ℝ}
    (hw : Antitone w) (hw0 : ∀ k, 0 ≤ w k) :
    (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ n.properDivisors,
      mobiusRealCoefficient m * mobiusRealCoefficient n * w (m + n)) ≤ 0 := by
  set L : ℕ := 2 * N with hL
  have hpairLe : ∀ n ∈ Finset.Icc 1 N, ∀ m ∈ n.properDivisors, m + n ≤ L := by
    intro n hn m hm
    have := Nat.mem_properDivisors.mp hm
    have := (Finset.mem_Icc.mp hn).2
    omega
  have hfull : (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ n.properDivisors,
      mobiusRealCoefficient m * mobiusRealCoefficient n) = divisorPairCountBelow N L := by
    unfold divisorPairCountBelow divisorPairRowBelow
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.filter_true_of_mem (hpairLe n hn)]
  calc
    (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ n.properDivisors,
        mobiusRealCoefficient m * mobiusRealCoefficient n * w (m + n)) =
      ∑ n ∈ Finset.Icc 1 N,
        (w L * ∑ m ∈ n.properDivisors, mobiusRealCoefficient m * mobiusRealCoefficient n +
          ∑ K ∈ Finset.range L, (w K - w (K + 1)) * divisorPairRowBelow K n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact sum_mul_weight_eq_layerCake _ _ (fun m => m + n) w L (hpairLe n hn)
    _ = w L * divisorPairCountBelow N L +
        ∑ K ∈ Finset.range L, (w K - w (K + 1)) * divisorPairCountBelow N K := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfull, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro K _
      rw [divisorPairCountBelow, Finset.mul_sum]
    _ ≤ 0 := by
      have h1 : w L * divisorPairCountBelow N L ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (hw0 L) (divisorPairCountBelow_nonpos N L)
      have h2 : ∑ K ∈ Finset.range L, (w K - w (K + 1)) * divisorPairCountBelow N K ≤ 0 := by
        apply Finset.sum_nonpos
        intro K _
        exact mul_nonpos_of_nonneg_of_nonpos
          (sub_nonneg.mpr (hw (Nat.le_succ K))) (divisorPairCountBelow_nonpos N K)
      linarith

/-- **All exponents.**  The divisor-comparable section of the Gamma--Hankel Möbius covariance is
nonpositive for every real exponent `r > 0`. -/
theorem gammaHankel_divisorSection_nonpos (N : ℕ) {r : ℝ} (hr : 0 < r) :
    (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ n.properDivisors,
      2 * Real.Gamma r * mobiusRealCoefficient m * mobiusRealCoefficient n /
        (((m + n : ℕ) : ℝ) ^ r)) ≤ 0 := by
  have hGamma : 0 ≤ 2 * Real.Gamma r := by
    have := Real.Gamma_pos_of_pos hr
    linarith
  let w : ℕ → ℝ := fun k => 2 * Real.Gamma r / ((max k 1 : ℕ) : ℝ) ^ r
  have hpos : ∀ k : ℕ, 0 < ((max k 1 : ℕ) : ℝ) ^ r := fun k =>
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < max k 1 by omega)) r
  have hw0 : ∀ k, 0 ≤ w k := fun k => div_nonneg hGamma (hpos k).le
  have hw : Antitone w := by
    intro a b hab
    apply div_le_div_of_nonneg_left hGamma (hpos a)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast max_le_max hab le_rfl) hr.le
  have := sum_divisorPairs_antitone_weight_nonpos N hw hw0
  calc
    _ = (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ n.properDivisors,
          mobiusRealCoefficient m * mobiusRealCoefficient n * w (m + n)) := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro m _
      have hmax : max (m + n) 1 = m + n := by
        have := Nat.pos_of_mem_properDivisors ‹m ∈ n.properDivisors›
        omega
      simp only [w, hmax]
      ring
    _ ≤ 0 := this

/-- **Power-series form.**  For `0 ≤ q ≤ 1`,
`∑_{n ≤ N} μ(n) qⁿ ∑_{m ∣ n, m < n} μ(m) q^m ≤ 0`. -/
theorem sum_divisorPairs_pow_nonpos (N : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ n.properDivisors,
      mobiusRealCoefficient m * mobiusRealCoefficient n * q ^ (m + n)) ≤ 0 :=
  sum_divisorPairs_antitone_weight_nonpos N (fun _ _ hab => pow_le_pow_of_le_one hq0 hq1 hab)
    (fun k => pow_nonneg hq0 k)

end
end RHTower
