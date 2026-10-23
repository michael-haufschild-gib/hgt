import GaloisForLFunctions.BezoutValuationIncidence.CentredChainEntryBoundsAboveHalfDamping

/-!
# The centred damping chain is bounded in the receiver norm above half damping

The receiver norm of the damping chain is `ℓ²` on the chain coordinate
(`SignedArithmeticEnergyIncidence.TheReceiverIsTheChainOrbitOfTheReciprocal`). Above damping one the
chain is Hilbert–Schmidt (`SignedArithmeticEnergyIncidence.centeredOperator_l2_le`), and between half
damping and one the size of the source alone does not decide boundedness. This module decides it:

* `centeredOperator_l2_le_of_half_lt`: for every `η > ½` there is `C` with
  `Σ_{n<T} (C_η b)(n)² ≤ C Σ_k b_k²` for all finitely supported `b` and all horizons `T`.

Mechanism: a Schur test with the weight `w(n) = (n+1)^{−1/2}`. The entry bounds of
`CentredChainEntryBoundsAboveHalfDamping` split an entry `C(N, K)` into a derivative part
`O((K/N) K^{−1−η} (N/K)^β)`, a ramp `ρ K^{−1−η}`, a jump `(K/N) K^{−η} (⌊N/K⌋ − ⌊N/(K+1)⌋)`, a
short-interval part `(K/N) K^{−η} (N/K²)^β`, and the large-divisor part `(K/N) K^{−η} J`. Each has
weighted row sums `O(N^{−1/2})` and weighted column sums `O(K^{−1/2})`: the jumps telescope in `K`
and sit at `j = ⌊N/K⌋`, `jK ≤ N < j(K+1)`, in `N`; the large divisors `d > L` of `j` satisfy
`j² < 2dN` (rows) and `j < d(K+1)` (columns), so they cost `√N Σ_d d^{−1/2−η}` and
`√K Σ_d d^{−1/2−η}`. Every series converges exactly because `η > ½`.

Below half damping `ℓ²`-boundedness of `C_η` would admit the reciprocal orbit, hence the receiver;
nothing here bears on that range. At `η ≤ ½` the chain is not Hilbert–Schmidt: its diagonal is
`≍ n^{−η}`.
-/

open Finset Filter Topology RHTower ArithmeticFunction
open scoped ZeroAtInfty
open GaloisForLFunctions.SignedArithmeticEnergyIncidence

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### Generic sums -/

/-- An indicator sum is dominated by the plain sum over a range containing its support. -/
theorem sum_range_ite_le_sum_range {p : ℕ → Prop} [DecidablePred p] {f : ℕ → ℝ} {M B : ℕ}
    (hp : ∀ k, p k → k < B) (hf : ∀ k, 0 ≤ f k) :
    ∑ k ∈ range M, (if p k then f k else 0) ≤ ∑ k ∈ range B, f k := by
  rw [← sum_filter]
  exact sum_le_sum_of_subset_of_nonneg (fun k hk => mem_range.mpr (hp k (mem_filter.mp hk).2))
    fun k _ _ => hf k

/-- `Σ_{k < M} (k+1)^{−s} ≤ ζ(s)` for `s > 1`. -/
theorem sum_range_rpow_le_zeta {s : ℝ} (hs : 1 < s) (M : ℕ) :
    ∑ k ∈ range M, ((k + 1 : ℕ) : ℝ) ^ (-s) ≤ realZetaSeries s := by
  have h := summable_realZetaTerm hs
  refine le_trans (le_of_eq (sum_congr rfl fun k _ => ?_))
    (h.sum_le_tsum (range M) fun k _ => Real.rpow_nonneg (by positivity) _)
  push_cast; ring_nf

theorem realZetaSeries_nonneg (s : ℝ) : 0 ≤ realZetaSeries s :=
  tsum_nonneg fun _ => Real.rpow_nonneg (by positivity) _

/-- Tails from index `m`: `Σ_{m ≤ n < T} (n+1)^{−s} ≤ (s/(s−1)) (m+1)^{1−s}` for `s > 1`. -/
theorem sum_range_ite_rpow_tail_le {s : ℝ} (hs : 1 < s) (m T : ℕ) :
    ∑ n ∈ range T, (if m ≤ n then ((n + 1 : ℕ) : ℝ) ^ (-s) else 0) ≤
      s / (s - 1) * ((m + 1 : ℕ) : ℝ) ^ (1 - s) := by
  have hr : 0 < s - 1 := by linarith
  set X : ℝ := ((m + 1 : ℕ) : ℝ) with hX
  have hX0 : 0 < X := by positivity
  have hfilter : ∑ n ∈ range T, (if m ≤ n then ((n + 1 : ℕ) : ℝ) ^ (-s) else 0) =
      ∑ i ∈ range (T - m), ((m + i + 1 : ℕ) : ℝ) ^ (-s) := by
    rw [← sum_filter, show (range T).filter (m ≤ ·) = Ico m T by
      ext n; simp only [mem_filter, mem_range, mem_Ico]; omega, sum_Ico_eq_sum_range]
  rw [hfilter]
  have hsplit : ∑ i ∈ range (T - m), ((m + i + 1 : ℕ) : ℝ) ^ (-s) ≤
      X ^ (-s) + ∑ i ∈ range (T - m), (X + 1 + i) ^ (-s) := by
    have e0 : ((m + 0 + 1 : ℕ) : ℝ) ^ (-s) = X ^ (-s) := by simp [hX]
    have e1 : ∀ i : ℕ, ((m + (i + 1) + 1 : ℕ) : ℝ) ^ (-s) = (X + 1 + i) ^ (-s) := fun i => by
      rw [hX]; push_cast; ring_nf
    calc ∑ i ∈ range (T - m), ((m + i + 1 : ℕ) : ℝ) ^ (-s)
        ≤ ∑ i ∈ range (T - m + 1), ((m + i + 1 : ℕ) : ℝ) ^ (-s) :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.le_succ _))
            fun _ _ _ => Real.rpow_nonneg (by positivity) _
      _ = _ := by rw [sum_range_succ', e0, sum_congr rfl fun i _ => e1 i, add_comm]
  have htail := sum_range_rpow_neg_tail_le hs hX0 (T - m)
  have hXs : X ^ (-s) ≤ X ^ (1 - s) :=
    Real.rpow_le_rpow_of_exponent_le (by rw [hX]; exact_mod_cast Nat.succ_pos m) (by linarith)
  have e : s / (s - 1) * X ^ (1 - s) = X ^ (1 - s) + X ^ (1 - s) / (s - 1) := by
    field_simp; ring
  rw [e]
  linarith

/-- Telescoping of nested intervals along an antitone map. -/
theorem sum_range_sum_Ioc_antitone (f : ℕ → ℕ) (hf : Antitone f) (G : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range (n + 1), ∑ j ∈ Ioc (f (k + 1)) (f k), G j = ∑ j ∈ Ioc (f (n + 1)) (f 0), G j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, add_comm]
    exact sum_Ioc_consecutive _ (hf (by omega)) (hf (by omega))

/-- Telescoping of floor differences: `Σ_{m ≤ k < p} (⌊N/(k+1)⌋ − ⌊N/(k+2)⌋) = ⌊N/(m+1)⌋ − ⌊N/(p+1)⌋`. -/
theorem sum_Ico_div_sub_div (N m p : ℕ) (hmp : m ≤ p) :
    ∑ k ∈ Ico m p, ((N / (k + 1) - N / (k + 1 + 1) : ℕ) : ℝ) =
      ((N / (m + 1) : ℕ) : ℝ) - ((N / (p + 1) : ℕ) : ℝ) := by
  induction p, hmp using Nat.le_induction with
  | base => simp
  | succ p hmp ih =>
    rw [sum_Ico_succ_top hmp, ih, Nat.cast_sub (Nat.div_le_div_left (by omega) (by omega))]
    ring

/-- Multiples of `d` up to `N` with `j² < 2dN` number at most `√(2N/d)`. -/
theorem card_filter_dvd_sq_lt_le (N d : ℕ) (hd : 1 ≤ d) :
    (#{j ∈ Ioc 0 N | d ∣ j ∧ j ^ 2 < 2 * d * N} : ℝ) ≤ Real.sqrt (2 * N / d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set X := ⌊Real.sqrt (2 * N / d)⌋₊
  have hsub : (#{j ∈ Ioc 0 N | d ∣ j ∧ j ^ 2 < 2 * d * N} : ℝ) ≤ X := by
    have hmap : ∀ j ∈ {j ∈ Ioc 0 N | d ∣ j ∧ j ^ 2 < 2 * d * N}, j / d ∈ Icc 1 X := by
      intro j hj
      simp only [mem_filter, mem_Ioc] at hj
      obtain ⟨⟨hj0, -⟩, ⟨t, rfl⟩, hsq⟩ := hj
      have ht : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with rfl | ht
        · simp at hj0
        · exact ht
      rw [Nat.mul_div_cancel_left t (by omega)]
      refine mem_Icc.mpr ⟨ht, Nat.le_floor ?_⟩
      rw [Real.le_sqrt (Nat.cast_nonneg _) (by positivity), le_div_iff₀ hd0]
      have : d * (d * t ^ 2) < d * (2 * N) := by nlinarith
      have h2 : d * t ^ 2 < 2 * N := Nat.lt_of_mul_lt_mul_left this
      have : ((d * t ^ 2 : ℕ) : ℝ) < ((2 * N : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this; nlinarith
    have hinj : Set.InjOn (· / d) ({j ∈ Ioc 0 N | d ∣ j ∧ j ^ 2 < 2 * d * N} : Finset ℕ) := by
      intro j hj j' hj' h
      simp only [coe_filter, Set.mem_setOf_eq, mem_Ioc] at hj hj'
      obtain ⟨-, ⟨t, rfl⟩, -⟩ := hj
      obtain ⟨-, ⟨t', rfl⟩, -⟩ := hj'
      simp only [Nat.mul_div_cancel_left _ (by omega : 0 < d)] at h
      rw [h]
    have := card_le_card_of_injOn _ hmap hinj
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this
  exact hsub.trans (Nat.floor_le (Real.sqrt_nonneg _))

/-- `Σ_{1 ≤ d ≤ m} d^{−(1/2+η)} ≤ ζ(1/2 + η)` for `η > ½`. -/
theorem sum_Icc_rpow_le_zeta_half {η : ℝ} (hη : 1 / 2 < η) (m : ℕ) :
    ∑ d ∈ Icc 1 m, (d : ℝ) ^ (-(1 / 2 + η)) ≤ realZetaSeries (1 / 2 + η) := by
  have h := ArithmeticContinuationAndCriticalEnergy.sum_Icc_rpow_le_realZetaSeries
    (ε := η - 1 / 2) (by linarith) m
  rwa [show 1 + (η - 1 / 2) = 1 / 2 + η by ring] at h

/-- `d^{−η} √(2N/d) = √2 √N d^{−(1/2+η)}`. -/
private theorem rpow_mul_sqrt_div (η : ℝ) {N d : ℕ} (hd : 1 ≤ d) :
    (d : ℝ) ^ (-η) * Real.sqrt (2 * N / d) =
      Real.sqrt 2 * Real.sqrt N * (d : ℝ) ^ (-(1 / 2 + η)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.sqrt_div' _ hd0.le, Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (d : ℝ),
    show -(1 / 2 + η) = -η + -(1 / 2) by ring, Real.rpow_add hd0, Real.rpow_neg hd0.le (1 / 2)]
  field_simp

/-- In a row, a large divisor of a jump index is large against `N`: if `j ∈ (N/(K+1), N/K]` and
`d > ⌊N/K⌋ − ⌊N/(K+1)⌋` then `j² < 2dN`. -/
private theorem sq_lt_of_large_divisor_row {N K j d : ℕ} (hK : 1 ≤ K)
    (hj : j ∈ Ioc (N / (K + 1)) (N / K)) (hd : N / K - N / (K + 1) < d) : j ^ 2 < 2 * d * N := by
  obtain ⟨hj1, hj2⟩ := mem_Ioc.mp hj
  set q := N / K
  set r := N / (K + 1)
  have hrq : r ≤ q := Nat.div_le_div_left (by omega) hK
  have h1 : N < (q + 1) * K := by
    have := Nat.lt_div_mul_add (a := N) hK; rw [add_mul, one_mul]; exact this
  have h2 : r * (K + 1) ≤ N := Nat.div_mul_le_self N (K + 1)
  have hjK : j * K ≤ N := (Nat.le_div_iff_mul_le hK).mp hj2
  have hNd : N < d * (K * (K + 1)) := by
    have hd' : q - r + 1 ≤ d := by omega
    have : N * (K + 1) < (q + 1) * K * (K + 1) := by nlinarith
    have : r * (K + 1) * K ≤ N * K := Nat.mul_le_mul_right K h2
    have hlt : N < (q - r + 1) * (K * (K + 1)) := by
      have e : (q - r + 1) * (K * (K + 1)) + r * (K + 1) * K = (q + 1) * K * (K + 1) := by
        have : q - r + r = q := Nat.sub_add_cancel hrq
        nlinarith
      nlinarith
    calc N < (q - r + 1) * (K * (K + 1)) := hlt
      _ ≤ d * (K * (K + 1)) := Nat.mul_le_mul_right _ hd'
  have hK2 : K * (K + 1) ≤ 2 * (K * K) := by
    have : K ≤ K * K := Nat.le_mul_self K
    calc K * (K + 1) = K * K + K := by ring
      _ ≤ K * K + K * K := Nat.add_le_add_left this _
      _ = 2 * (K * K) := by ring
  have hN2 : N < 2 * d * (K * K) := lt_of_lt_of_le hNd (by
    calc d * (K * (K + 1)) ≤ d * (2 * (K * K)) := Nat.mul_le_mul_left d hK2
      _ = 2 * d * (K * K) := by ring)
  have hj0 : 0 < j := lt_of_le_of_lt (Nat.zero_le _) hj1
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.mul_pos hj0 hK) hjK
  have : j ^ 2 * N < 2 * d * N * N := by
    calc j ^ 2 * N < j ^ 2 * (2 * d * (K * K)) := by
          exact Nat.mul_lt_mul_of_pos_left hN2 (by positivity)
      _ = 2 * d * ((j * K) * (j * K)) := by ring
      _ ≤ 2 * d * (N * N) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hjK hjK)
      _ = 2 * d * N * N := by ring
  exact Nat.lt_of_mul_lt_mul_right this

/-- **Row large-divisor sums.** `Σ_{k ≤ n} J(⌊N/(K+1)⌋, ⌊N/K⌋) ≤ √2 ζ(½+η) √N`, `N = n+1`. -/
theorem sum_range_largeDivisorSum_le {η : ℝ} (hη : 1 / 2 < η) (n : ℕ) :
    ∑ k ∈ range (n + 1), largeDivisorSum η ((n + 1) / (k + 1 + 1)) ((n + 1) / (k + 1)) ≤
      Real.sqrt 2 * realZetaSeries (1 / 2 + η) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  set N := n + 1 with hN
  set G : ℕ → ℝ := fun j => ∑ d ∈ j.divisors with j ^ 2 < 2 * d * N, (d : ℝ) ^ (-η)
  have hG0 : ∀ j, 0 ≤ G j := fun j => sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- large divisors of jump indices satisfy `j² < 2dN`
  have hstep : ∀ k ∈ range (n + 1), largeDivisorSum η (N / (k + 1 + 1)) (N / (k + 1)) ≤
      ∑ j ∈ Ioc (N / (k + 1 + 1)) (N / (k + 1)), G j := by
    intro k _
    refine sum_le_sum fun j hj => sum_le_sum_of_subset_of_nonneg ?_
      fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
    intro d hd
    simp only [mem_filter] at hd ⊢
    exact ⟨hd.1, sq_lt_of_large_divisor_row (by omega) hj hd.2⟩
  have hanti : Antitone fun k : ℕ => N / (k + 1) := fun a b hab =>
    Nat.div_le_div_left (by omega) (by omega)
  have htel := sum_range_sum_Ioc_antitone (fun k => N / (k + 1)) hanti G n
  simp only [Nat.div_one, zero_add] at htel
  have hsub : ∑ j ∈ Ioc (N / (n + 1 + 1)) N, G j ≤ ∑ j ∈ Ioc 0 N, G j :=
    sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le _)) fun j _ _ => hG0 j
  -- swap to divisors
  have hswap : ∑ j ∈ Ioc 0 N, G j =
      ∑ d ∈ Icc 1 N, ∑ j ∈ Ioc 0 N with d ∣ j ∧ j ^ 2 < 2 * d * N, (d : ℝ) ^ (-η) := by
    refine sum_comm' fun j d => ?_
    simp only [mem_Ioc, mem_filter, Nat.mem_divisors, mem_Icc]
    constructor
    · rintro ⟨⟨hj0, hjN⟩, ⟨hdj, -⟩, hsq⟩
      exact ⟨⟨⟨hj0, hjN⟩, hdj, hsq⟩, Nat.pos_of_dvd_of_pos hdj hj0,
        (Nat.le_of_dvd hj0 hdj).trans hjN⟩
    · rintro ⟨⟨⟨hj0, hjN⟩, hdj, hsq⟩, -, -⟩
      exact ⟨⟨hj0, hjN⟩, ⟨hdj, by omega⟩, hsq⟩
  have hcount : ∑ d ∈ Icc 1 N, ∑ j ∈ Ioc 0 N with d ∣ j ∧ j ^ 2 < 2 * d * N, (d : ℝ) ^ (-η) ≤
      Real.sqrt 2 * Real.sqrt N * ∑ d ∈ Icc 1 N, (d : ℝ) ^ (-(1 / 2 + η)) := by
    rw [mul_sum]
    refine sum_le_sum fun d hd => ?_
    have hd1 := (mem_Icc.mp hd).1
    rw [sum_const, nsmul_eq_mul, ← rpow_mul_sqrt_div η hd1, mul_comm]
    exact mul_le_mul_of_nonneg_left (card_filter_dvd_sq_lt_le N d hd1)
      (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hz := sum_Icc_rpow_le_zeta_half hη N
  calc ∑ k ∈ range (n + 1), largeDivisorSum η (N / (k + 1 + 1)) (N / (k + 1))
      ≤ ∑ k ∈ range (n + 1), ∑ j ∈ Ioc (N / (k + 1 + 1)) (N / (k + 1)), G j := sum_le_sum hstep
    _ = ∑ j ∈ Ioc (N / (n + 1 + 1)) N, G j := htel
    _ ≤ ∑ j ∈ Ioc 0 N, G j := hsub
    _ = _ := hswap
    _ ≤ Real.sqrt 2 * Real.sqrt N * ∑ d ∈ Icc 1 N, (d : ℝ) ^ (-(1 / 2 + η)) := hcount
    _ ≤ Real.sqrt 2 * Real.sqrt N * realZetaSeries (1 / 2 + η) :=
        mul_le_mul_of_nonneg_left hz (by positivity)
    _ = _ := by ring

/-- In a column, a large divisor of a jump index is large against `K`: if `j ∈ (N/(K+1), N/K]`
and `d > ⌊N/K⌋ − ⌊N/(K+1)⌋` then `j < d(K+1)`. -/
private theorem lt_of_large_divisor_col {N K j d : ℕ} (hK : 1 ≤ K)
    (hj : j ∈ Ioc (N / (K + 1)) (N / K)) (hd : N / K - N / (K + 1) < d) : j < d * (K + 1) := by
  obtain ⟨hj1, hj2⟩ := mem_Ioc.mp hj
  set q := N / K
  set r := N / (K + 1)
  have hrq : r ≤ q := Nat.div_le_div_left (by omega) hK
  have h1 : N < (q + 1) * K := by
    have := Nat.lt_div_mul_add (a := N) hK; rw [add_mul, one_mul]; exact this
  have h2 : r * (K + 1) ≤ N := Nat.div_mul_le_self N (K + 1)
  have hjK : j * K ≤ N := (Nat.le_div_iff_mul_le hK).mp hj2
  have hd' : q - r + 1 ≤ d := by omega
  have : N * (K + 1) < (q + 1) * K * (K + 1) := by nlinarith
  have : r * (K + 1) * K ≤ N * K := Nat.mul_le_mul_right K h2
  have e : (q - r + 1) * (K * (K + 1)) + r * (K + 1) * K = (q + 1) * K * (K + 1) := by
    have : q - r + r = q := Nat.sub_add_cancel hrq
    nlinarith
  have hlt : N < (q - r + 1) * (K * (K + 1)) := by nlinarith
  have : j * K < (q - r + 1) * (K + 1) * K := by nlinarith
  have h3 : j < (q - r + 1) * (K + 1) := Nat.lt_of_mul_lt_mul_right this
  exact lt_of_lt_of_le h3 (Nat.mul_le_mul_right _ hd')

/-- `#{n < T : jK ≤ n + 1 < j(K+1)} ≤ j`. -/
private theorem card_filter_window_le (T j K : ℕ) :
    #{n ∈ range T | j * K ≤ n + 1 ∧ n + 1 < j * (K + 1)} ≤ j := by
  have hsub : {n ∈ range T | j * K ≤ n + 1 ∧ n + 1 < j * (K + 1)} ⊆ Ico (j * K - 1) (j * K - 1 + j) := by
    intro n hn
    simp only [mem_filter, mem_range, mem_Ico] at hn ⊢
    have e : j * (K + 1) = j * K + j := by ring
    omega
  calc _ ≤ #(Ico (j * K - 1) (j * K - 1 + j)) := card_le_card hsub
    _ = j := by rw [Nat.card_Ico]; omega

/-- **Column large-divisor sums.** For fixed `K = k + 1`:
`Σ_{n < T} K^{1−η} N^{−3/2} J(⌊N/(K+1)⌋, ⌊N/K⌋) ≤ 2 ζ(½+η) K^{−η}`. -/
theorem sum_range_col_largeDivisorSum_le {η : ℝ} (hη : 1 / 2 < η) (k T : ℕ) :
    ∑ n ∈ range T, ((k + 1 : ℕ) : ℝ) ^ (1 - η) * ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
        largeDivisorSum η ((n + 1) / (k + 1 + 1)) ((n + 1) / (k + 1)) ≤
      2 * realZetaSeries (1 / 2 + η) * ((k + 1 : ℕ) : ℝ) ^ (-η) := by
  set K := k + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  set G : ℕ → ℝ := fun j => ∑ d ∈ j.divisors with j < d * (K + 1), (d : ℝ) ^ (-η)
  have hG0 : ∀ j, 0 ≤ G j := fun j => sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set H : ℕ → ℝ := fun j => (K : ℝ) ^ (1 - η) * ((j * K : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * G j
  have hH0 : ∀ j, 0 ≤ H j := fun j => mul_nonneg (mul_nonneg (Real.rpow_nonneg hK0.le _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hG0 j)
  -- pointwise: each column entry is dominated by the `j`-indexed weights
  have hpt : ∀ n ∈ range T, (K : ℝ) ^ (1 - η) * ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
      largeDivisorSum η ((n + 1) / (K + 1)) ((n + 1) / K) ≤
      ∑ j ∈ Ioc ((n + 1) / (K + 1)) ((n + 1) / K), H j := by
    intro n _
    unfold largeDivisorSum
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    have hjK : j * K ≤ n + 1 := (Nat.le_div_iff_mul_le hK1).mp (mem_Ioc.mp hj).2
    have hj0 : 0 < j := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hj).1
    have hpow : ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ ((j * K : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hjK) (by norm_num)
    have hsub : ∑ d ∈ j.divisors with (n + 1) / K - (n + 1) / (K + 1) < d, (d : ℝ) ^ (-η) ≤ G j :=
      sum_le_sum_of_subset_of_nonneg (fun d hd => by
        simp only [mem_filter] at hd ⊢
        exact ⟨hd.1, lt_of_large_divisor_col hK1 hj hd.2⟩)
        fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hS0 : 0 ≤ ∑ d ∈ j.divisors with (n + 1) / K - (n + 1) / (K + 1) < d, (d : ℝ) ^ (-η) :=
      sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc (K : ℝ) ^ (1 - η) * ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
          ∑ d ∈ j.divisors with (n + 1) / K - (n + 1) / (K + 1) < d, (d : ℝ) ^ (-η)
        ≤ (K : ℝ) ^ (1 - η) * ((j * K : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * G j :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hK0.le _)) hsub hS0
            (mul_nonneg (Real.rpow_nonneg hK0.le _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      _ = H j := rfl
  -- swap the window index `n` and the jump index `j`
  have hswap : ∑ n ∈ range T, ∑ j ∈ Ioc ((n + 1) / (K + 1)) ((n + 1) / K), H j =
      ∑ j ∈ Icc 1 T, ∑ n ∈ range T with j * K ≤ n + 1 ∧ n + 1 < j * (K + 1), H j := by
    refine sum_comm' fun n j => ?_
    simp only [mem_range, mem_Ioc, mem_filter, mem_Icc]
    rw [Nat.div_lt_iff_lt_mul (by omega), Nat.le_div_iff_mul_le hK1]
    constructor
    · rintro ⟨hn, h1, h2⟩
      refine ⟨⟨hn, h2, h1⟩, ?_, ?_⟩
      · by_contra h0; push Not at h0; interval_cases j; simp at h1
      · have : j ≤ j * K := Nat.le_mul_of_pos_right j hK1
        omega
    · rintro ⟨⟨hn, h2, h1⟩, -, -⟩
      exact ⟨hn, h1, h2⟩
  have hcount : ∑ j ∈ Icc 1 T, ∑ n ∈ range T with j * K ≤ n + 1 ∧ n + 1 < j * (K + 1), H j ≤
      ∑ j ∈ Icc 1 T, (j : ℝ) * H j := by
    refine sum_le_sum fun j _ => ?_
    rw [sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_window_le T j K) (hH0 j)
  -- evaluate the `j`-weights
  have hjH : ∀ j ∈ Icc 1 T, (j : ℝ) * H j =
      (K : ℝ) ^ (-(1 / 2 : ℝ) - η) * ((j : ℝ) ^ (-(1 / 2 : ℝ)) * G j) := by
    intro j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
    simp only [H]
    rw [Nat.cast_mul, Real.mul_rpow hj0.le hK0.le]
    have e1 : (j : ℝ) * (j : ℝ) ^ (-(3 / 2 : ℝ)) = (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [show -(1 / 2 : ℝ) = 1 + -(3 / 2) by norm_num, Real.rpow_add hj0, Real.rpow_one]
    have e2 : (K : ℝ) ^ (1 - η) * (K : ℝ) ^ (-(3 / 2 : ℝ)) = (K : ℝ) ^ (-(1 / 2 : ℝ) - η) := by
      rw [← Real.rpow_add hK0]; ring_nf
    calc (j : ℝ) * ((K : ℝ) ^ (1 - η) * ((j : ℝ) ^ (-(3 / 2 : ℝ)) * (K : ℝ) ^ (-(3 / 2 : ℝ))) * G j)
        = ((K : ℝ) ^ (1 - η) * (K : ℝ) ^ (-(3 / 2 : ℝ))) *
            (((j : ℝ) * (j : ℝ) ^ (-(3 / 2 : ℝ))) * G j) := by ring
      _ = _ := by rw [e1, e2]
  -- swap `j` and the divisor `d`
  have hdiv : ∑ j ∈ Icc 1 T, (j : ℝ) ^ (-(1 / 2 : ℝ)) * G j =
      ∑ d ∈ Icc 1 T, ∑ j ∈ Icc 1 T with d ∣ j ∧ j < d * (K + 1),
        (j : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-η) := by
    simp only [G, mul_sum]
    refine sum_comm' fun j d => ?_
    simp only [mem_Icc, mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hj1, hjT⟩, ⟨hdj, -⟩, hlt⟩
      exact ⟨⟨⟨hj1, hjT⟩, hdj, hlt⟩, Nat.pos_of_dvd_of_pos hdj hj1,
        (Nat.le_of_dvd hj1 hdj).trans hjT⟩
    · rintro ⟨⟨⟨hj1, hjT⟩, hdj, hlt⟩, -, -⟩
      exact ⟨⟨hj1, hjT⟩, ⟨hdj, by omega⟩, hlt⟩
  have hinner : ∀ d ∈ Icc 1 T, ∑ j ∈ Icc 1 T with d ∣ j ∧ j < d * (K + 1),
      (j : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-η) ≤
      (d : ℝ) ^ (-(1 / 2 + η)) * (2 * (K : ℝ) ^ (1 / 2 : ℝ)) := by
    intro d hd
    have hd1 := (mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hsub : {j ∈ Icc 1 T | d ∣ j ∧ j < d * (K + 1)} ⊆ (Icc 1 K).image (d * ·) := by
      intro j hj
      simp only [mem_filter, mem_Icc] at hj
      obtain ⟨⟨hj1, -⟩, ⟨t, rfl⟩, hlt⟩ := hj
      refine mem_image.mpr ⟨t, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos t with rfl | ht
        · simp at hj1
        · exact ht
      · have := Nat.lt_of_mul_lt_mul_left hlt; omega
    have hinj : Set.InjOn (d * ·) (Icc 1 K : Finset ℕ) := fun a _ b _ h =>
      Nat.eq_of_mul_eq_mul_left (by omega) h
    have hdd : (d : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-η) = (d : ℝ) ^ (-(1 / 2 + η)) := by
      rw [← Real.rpow_add hd0]; ring_nf
    calc ∑ j ∈ Icc 1 T with d ∣ j ∧ j < d * (K + 1), (j : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-η)
        ≤ ∑ j ∈ (Icc 1 K).image (d * ·), (j : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-η) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
            mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hd0.le _)
      _ = ∑ t ∈ Icc 1 K, ((d * t : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-η) := sum_image hinj
      _ = (d : ℝ) ^ (-(1 / 2 + η)) * ∑ t ∈ Icc 1 K, (t : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [mul_sum]
          refine sum_congr rfl fun t _ => ?_
          rw [Nat.cast_mul, Real.mul_rpow hd0.le (Nat.cast_nonneg _), ← hdd]
          ring
      _ ≤ (d : ℝ) ^ (-(1 / 2 + η)) * (2 * (K : ℝ) ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hd0.le _)
          have := sum_Icc_rpow_neg_le_div (s := 1 / 2) (by norm_num) (by norm_num) K
          rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at this
          linarith
  have hz := sum_Icc_rpow_le_zeta_half hη T
  have hfinal : ∑ d ∈ Icc 1 T, ∑ j ∈ Icc 1 T with d ∣ j ∧ j < d * (K + 1),
      (j : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-η) ≤
      2 * (K : ℝ) ^ (1 / 2 : ℝ) * realZetaSeries (1 / 2 + η) := by
    calc _ ≤ ∑ d ∈ Icc 1 T, (d : ℝ) ^ (-(1 / 2 + η)) * (2 * (K : ℝ) ^ (1 / 2 : ℝ)) :=
          sum_le_sum hinner
      _ = 2 * (K : ℝ) ^ (1 / 2 : ℝ) * ∑ d ∈ Icc 1 T, (d : ℝ) ^ (-(1 / 2 + η)) := by
          rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hz (by positivity)
  have hKpow : (K : ℝ) ^ (-(1 / 2 : ℝ) - η) * (2 * (K : ℝ) ^ (1 / 2 : ℝ) *
      realZetaSeries (1 / 2 + η)) = 2 * realZetaSeries (1 / 2 + η) * (K : ℝ) ^ (-η) := by
    have : (K : ℝ) ^ (-(1 / 2 : ℝ) - η) * (K : ℝ) ^ (1 / 2 : ℝ) = (K : ℝ) ^ (-η) := by
      rw [← Real.rpow_add hK0]; ring_nf
    calc _ = 2 * realZetaSeries (1 / 2 + η) *
          ((K : ℝ) ^ (-(1 / 2 : ℝ) - η) * (K : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [this]
  have hKpos : 0 ≤ (K : ℝ) ^ (-(1 / 2 : ℝ) - η) := Real.rpow_nonneg hK0.le _
  calc ∑ n ∈ range T, ((k + 1 : ℕ) : ℝ) ^ (1 - η) * ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
        largeDivisorSum η ((n + 1) / (k + 1 + 1)) ((n + 1) / (k + 1))
      ≤ ∑ n ∈ range T, ∑ j ∈ Ioc ((n + 1) / (K + 1)) ((n + 1) / K), H j := sum_le_sum hpt
    _ = _ := hswap
    _ ≤ ∑ j ∈ Icc 1 T, (j : ℝ) * H j := hcount
    _ = (K : ℝ) ^ (-(1 / 2 : ℝ) - η) * ∑ j ∈ Icc 1 T, (j : ℝ) ^ (-(1 / 2 : ℝ)) * G j := by
        rw [mul_sum]; exact sum_congr rfl hjH
    _ = (K : ℝ) ^ (-(1 / 2 : ℝ) - η) * ∑ d ∈ Icc 1 T, ∑ j ∈ Icc 1 T with d ∣ j ∧ j < d * (K + 1),
          (j : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-η) := by rw [hdiv]
    _ ≤ (K : ℝ) ^ (-(1 / 2 : ℝ) - η) * (2 * (K : ℝ) ^ (1 / 2 : ℝ) * realZetaSeries (1 / 2 + η)) :=
        mul_le_mul_of_nonneg_left hfinal hKpos
    _ = _ := hKpow

/-! ### The pieces of an entry -/

/-- Derivative part `(K/N) η K^{−1−η} (ρ + c_P (N/K)^β)`. -/
def chainDerivativeTerm (η : ℝ) (n k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) *
    (η * ((k + 1 : ℕ) : ℝ) ^ (-1 - η) * ((pmPowerDampedDivisorDensity η).re +
      chainSourceConstant η * (((n + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ (1 - chainSourceExponent η)))

/-- Short-interval part `(K/N) K^{−η} (2ρ + c_P (2N/K²)^β + J)`. -/
def chainShortTerm (η : ℝ) (n k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) *
    (((k + 1 : ℕ) : ℝ) ^ (-η) * (2 * (pmPowerDampedDivisorDensity η).re +
      chainSourceConstant η *
        (2 * ((n + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) ^ (1 - chainSourceExponent η) +
      largeDivisorSum η ((n + 1) / (k + 1 + 1)) ((n + 1) / (k + 1))))

/-- Jump-and-ramp part `(K/N) K^{−η} ((1 + 2ρ)(⌊N/K⌋ − ⌊N/(K+1)⌋) + ρ N/K²)`. -/
def chainJumpTerm (η : ℝ) (n k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) *
    (((k + 1 : ℕ) : ℝ) ^ (-η) * ((1 + 2 * (pmPowerDampedDivisorDensity η).re) *
        ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ)) +
      (pmPowerDampedDivisorDensity η).re * ((n + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2))

/-- The weight `w(i) = (i+1)^{−1/2}`. -/
def chainWeight (i : ℕ) : ℝ := ((i + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

theorem chainWeight_pos (i : ℕ) : 0 < chainWeight i := Real.rpow_pos_of_pos (by positivity) _

/-- The small-`K` regime `(k+1)(k+2) ≤ n+1`. -/
def chainSmall (n k : ℕ) : Prop := (k + 1) * (k + 1 + 1) ≤ n + 1

instance (n k : ℕ) : Decidable (chainSmall n k) := by unfold chainSmall; infer_instance

theorem chainSmall_le {n k : ℕ} (h : chainSmall n k) : k ≤ n := by unfold chainSmall at h; nlinarith

section Pieces

variable {η : ℝ} (h1 : 1 / 2 < η) (h2 : η ≤ 1)
include h1 h2

theorem abs_centeredRow_le_pieces (n k : ℕ) :
    |arithmeticDampingCenteredRow η n k| ≤
      (if n < k then (1 + η) * (pmPowerDampedDivisorDensity η).re * ((k + 1 : ℕ) : ℝ) ^ (-1 - η)
        else 0) +
      (if k ≤ n then chainDerivativeTerm η n k else 0) +
      (if chainSmall n k then chainShortTerm η n k else 0) +
      (if k ≤ n ∧ ¬ chainSmall n k then chainJumpTerm η n k else 0) := by
  have hη : 0 < η := by linarith
  by_cases hnk : n < k
  · have hs : ¬ chainSmall n k := fun h => absurd (chainSmall_le h) (by omega)
    rw [if_pos hnk, if_neg (by omega), if_neg hs, if_neg (by tauto)]
    simpa using abs_centeredRow_le_entrance hη hnk
  · have hkn : k ≤ n := by omega
    rw [if_neg hnk, if_pos hkn, zero_add]
    by_cases hs : chainSmall n k
    · rw [if_pos hs, if_neg (by tauto), add_zero]
      have := abs_centeredRow_le_small h1 h2 hs
      unfold chainDerivativeTerm chainShortTerm
      rw [← mul_add]; exact this
    · rw [if_neg hs, if_pos ⟨hkn, hs⟩, add_zero]
      have := abs_centeredRow_le_large h1 h2 hkn
      unfold chainDerivativeTerm chainJumpTerm
      rw [← mul_add]; exact this

end Pieces

end

end GaloisForLFunctions.BezoutValuationIncidence
