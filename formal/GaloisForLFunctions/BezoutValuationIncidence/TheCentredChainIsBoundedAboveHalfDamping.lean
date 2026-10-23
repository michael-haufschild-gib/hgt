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
    rw [if_pos hnk, if_neg (by omega), if_neg hs, if_neg (fun h => absurd h.1 (by omega))]
    simpa using abs_centeredRow_le_entrance hη hnk
  · have hkn : k ≤ n := by omega
    rw [if_neg hnk, if_pos hkn, zero_add]
    by_cases hs : chainSmall n k
    · rw [if_pos hs, if_neg (fun h => h.2 hs), add_zero]
      have := abs_centeredRow_le_small h1 h2 hs
      unfold chainDerivativeTerm chainShortTerm
      rw [← mul_add]; exact this
    · rw [if_neg hs, if_pos ⟨hkn, hs⟩, add_zero]
      have := abs_centeredRow_le_large h1 h2 hkn
      unfold chainDerivativeTerm chainJumpTerm
      rw [← mul_add]; exact this

end Pieces

/-! ### Weighted row sums -/

/-- `K^{−1} ≤ N^{−1/2}` for `1 ≤ N ≤ K`. -/
private theorem rpow_neg_one_le_of_le {N K : ℝ} (hN : 1 ≤ N) (hNK : N ≤ K) :
    K ^ (-1 : ℝ) ≤ N ^ (-(1 / 2 : ℝ)) :=
  (Real.rpow_le_rpow_of_nonpos (by linarith) hNK (by norm_num)).trans
    (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))

/-- `K^{−1} ≤ √2 N^{−1/2}` for `0 < N ≤ 2K²`. -/
private theorem rpow_neg_one_le_sqrt_two {N K : ℝ} (hN : 0 < N) (hK : 0 < K)
    (h : N ≤ 2 * K ^ 2) : K ^ (-1 : ℝ) ≤ Real.sqrt 2 * N ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg_one, Real.rpow_neg hN.le, ← Real.sqrt_eq_rpow]
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hs : Real.sqrt N ≤ Real.sqrt 2 * K := by
    calc Real.sqrt N ≤ Real.sqrt (2 * K ^ 2) := Real.sqrt_le_sqrt h
      _ = Real.sqrt 2 * K := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hK.le]
  calc K⁻¹ = (Real.sqrt N / K) * (Real.sqrt N)⁻¹ := by field_simp
    _ ≤ Real.sqrt 2 * (Real.sqrt N)⁻¹ :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hK).mpr (by linarith)) (inv_nonneg.mpr hsN.le)

/-- `√N / N = N^{−1/2}`. -/
private theorem sqrt_div_self_eq {N : ℝ} (hN : 0 < N) : Real.sqrt N / N = N ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hN.le, div_eq_iff hN.ne', inv_mul_eq_div,
    eq_div_iff (Real.rpow_pos_of_pos hN _).ne', ← Real.rpow_add hN]
  norm_num

/-- The exponent `s₂ = 1/2 − η − 2β` of the short-interval row sums. -/
def chainShortExponent (η : ℝ) : ℝ := 1 / 2 - η - 2 * (1 - chainSourceExponent η)

/-- The row constant of the Schur test. -/
def chainRowConstant (η : ℝ) : ℝ :=
  (1 + η) * (pmPowerDampedDivisorDensity η).re * realZetaSeries (1 / 2 + η) +
    η * ((pmPowerDampedDivisorDensity η).re + chainSourceConstant η) * realZetaSeries (1 / 2 + η) +
    (2 * (pmPowerDampedDivisorDensity η).re +
      chainSourceConstant η * 2 ^ (1 - chainSourceExponent η) / (1 + chainShortExponent η) +
      Real.sqrt 2 * realZetaSeries (1 / 2 + η)) +
    (2 * (1 + 2 * (pmPowerDampedDivisorDensity η).re) +
      Real.sqrt 2 * (pmPowerDampedDivisorDensity η).re * realZetaSeries (1 / 2 + η))

section Rows

variable {η : ℝ} (h1 : 1 / 2 < η) (h2 : η ≤ 1)
include h1 h2

omit h2 in
private theorem half_add_gt_one : 1 < 1 / 2 + η := by linarith

omit h2 in
private theorem row_entrance (n M : ℕ) :
    ∑ k ∈ range M, (if n < k then (1 + η) * (pmPowerDampedDivisorDensity η).re *
        ((k + 1 : ℕ) : ℝ) ^ (-1 - η) else 0) * chainWeight k ≤
      (1 + η) * (pmPowerDampedDivisorDensity η).re * realZetaSeries (1 / 2 + η) * chainWeight n := by
  have hη : 0 < η := by linarith
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hη
  have hc : 0 ≤ (1 + η) * (pmPowerDampedDivisorDensity η).re := by positivity
  have hpt : ∀ k ∈ range M, (if n < k then (1 + η) * (pmPowerDampedDivisorDensity η).re *
      ((k + 1 : ℕ) : ℝ) ^ (-1 - η) else 0) * chainWeight k ≤
      (1 + η) * (pmPowerDampedDivisorDensity η).re * chainWeight n *
        ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + η)) := by
    intro k _
    have hK0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    split_ifs with hnk
    · unfold chainWeight
      have e : ((k + 1 : ℕ) : ℝ) ^ (-1 - η) * ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
          ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + η)) * ((k + 1 : ℕ) : ℝ) ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]; ring_nf
      have hle := rpow_neg_one_le_of_le (N := ((n + 1 : ℕ) : ℝ)) (K := ((k + 1 : ℕ) : ℝ))
        (by exact_mod_cast Nat.succ_pos n) (by exact_mod_cast (by omega : n + 1 ≤ k + 1))
      have hp : 0 ≤ ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + η)) := Real.rpow_nonneg hK0.le _
      calc (1 + η) * (pmPowerDampedDivisorDensity η).re * ((k + 1 : ℕ) : ℝ) ^ (-1 - η) *
            ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
          = (1 + η) * (pmPowerDampedDivisorDensity η).re *
              (((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + η)) * ((k + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
            rw [← e]; ring
        _ ≤ (1 + η) * (pmPowerDampedDivisorDensity η).re *
              (((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + η)) * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hp) hc
        _ = _ := by ring
    · rw [zero_mul]
      exact mul_nonneg (mul_nonneg hc (chainWeight_pos n).le) (Real.rpow_nonneg hK0.le _)
  calc _ ≤ ∑ k ∈ range M, (1 + η) * (pmPowerDampedDivisorDensity η).re * chainWeight n *
        ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + η)) := sum_le_sum hpt
    _ = (1 + η) * (pmPowerDampedDivisorDensity η).re * chainWeight n *
        ∑ k ∈ range M, ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + η)) := by rw [mul_sum]
    _ ≤ (1 + η) * (pmPowerDampedDivisorDensity η).re * chainWeight n * realZetaSeries (1 / 2 + η) :=
        mul_le_mul_of_nonneg_left (sum_range_rpow_le_zeta (half_add_gt_one h1) M)
          (mul_nonneg hc (chainWeight_pos n).le)
    _ = _ := by ring

private theorem row_derivative (n M : ℕ) :
    ∑ k ∈ range M, (if k ≤ n then chainDerivativeTerm η n k else 0) * chainWeight k ≤
      η * ((pmPowerDampedDivisorDensity η).re + chainSourceConstant η) *
        realZetaSeries (1 / 2 + η) * chainWeight n := by
  have hη : 0 < η := by linarith
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hη
  have hcP := chainSourceConstant_pos h1 h2
  set β := 1 - chainSourceExponent η with hβ
  have hβ0 : 0 ≤ β := by have := chainSourceExponent_lt_one h2; linarith
  have hβ1 : β - 1 ≤ -(1 / 2 : ℝ) := by have := chainSourceExponent_gt_half h1; linarith
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast Nat.succ_pos n
  have hN0 : (0 : ℝ) < N := by linarith
  have hc : 0 ≤ η * ((pmPowerDampedDivisorDensity η).re + chainSourceConstant η) := by positivity
  have hpt : ∀ k ∈ range M, (if k ≤ n then chainDerivativeTerm η n k else 0) * chainWeight k ≤
      η * ((pmPowerDampedDivisorDensity η).re + chainSourceConstant η) * chainWeight n *
        ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + η)) := by
    intro k _
    set K : ℝ := ((k + 1 : ℕ) : ℝ) with hK
    have hK1 : (1 : ℝ) ≤ K := by rw [hK]; exact_mod_cast Nat.succ_pos k
    have hK0 : (0 : ℝ) < K := by linarith
    split_ifs with hkn
    · unfold chainDerivativeTerm chainWeight
      rw [← hN, ← hK, ← hβ]
      have e : K * K ^ (-1 - η) * K ^ (-(1 / 2 : ℝ)) = K ^ (-(1 / 2 + η)) := by
        calc K * K ^ (-1 - η) * K ^ (-(1 / 2 : ℝ)) = K ^ (-1 - η + 1) * K ^ (-(1 / 2 : ℝ)) := by
              rw [Real.rpow_add_one hK0.ne']; ring
          _ = K ^ (-1 - η + 1 + -(1 / 2 : ℝ)) := (Real.rpow_add hK0 (-1 - η + 1) (-(1 / 2))).symm
          _ = K ^ (-(1 / 2 + η)) := by ring_nf
      have hNK : N / K ≤ N := div_le_self hN0.le hK1
      have hX : (pmPowerDampedDivisorDensity η).re + chainSourceConstant η * (N / K) ^ β ≤
          ((pmPowerDampedDivisorDensity η).re + chainSourceConstant η) * N ^ β := by
        have hNb : 1 ≤ N ^ β := Real.one_le_rpow hN1 hβ0
        have : (N / K) ^ β ≤ N ^ β := Real.rpow_le_rpow (by positivity) hNK hβ0
        nlinarith
      have hNb : N ^ β / N ≤ N ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_sub_one hN0.ne']; exact Real.rpow_le_rpow_of_exponent_le hN1 hβ1
      have hp : 0 ≤ K ^ (-(1 / 2 + η)) := Real.rpow_nonneg hK0.le _
      calc K / N * (η * K ^ (-1 - η) * ((pmPowerDampedDivisorDensity η).re +
            chainSourceConstant η * (N / K) ^ β)) * K ^ (-(1 / 2 : ℝ))
          = η * (K * K ^ (-1 - η) * K ^ (-(1 / 2 : ℝ))) *
              (((pmPowerDampedDivisorDensity η).re + chainSourceConstant η * (N / K) ^ β) / N) := by
            ring
        _ ≤ η * K ^ (-(1 / 2 + η)) *
              (((pmPowerDampedDivisorDensity η).re + chainSourceConstant η) * N ^ β / N) := by
            rw [e]
            exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hX hN0.le) (by positivity)
        _ = η * ((pmPowerDampedDivisorDensity η).re + chainSourceConstant η) * K ^ (-(1 / 2 + η)) *
              (N ^ β / N) := by ring
        _ ≤ η * ((pmPowerDampedDivisorDensity η).re + chainSourceConstant η) * K ^ (-(1 / 2 + η)) *
              N ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hNb (mul_nonneg hc hp)
        _ = _ := by ring
    · rw [zero_mul]
      exact mul_nonneg (mul_nonneg hc (chainWeight_pos n).le) (Real.rpow_nonneg hK0.le _)
  calc _ ≤ ∑ k ∈ range M, η * ((pmPowerDampedDivisorDensity η).re + chainSourceConstant η) *
        chainWeight n * ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + η)) := sum_le_sum hpt
    _ = η * ((pmPowerDampedDivisorDensity η).re + chainSourceConstant η) * chainWeight n *
        ∑ k ∈ range M, ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + η)) := by rw [mul_sum]
    _ ≤ η * ((pmPowerDampedDivisorDensity η).re + chainSourceConstant η) * chainWeight n *
        realZetaSeries (1 / 2 + η) :=
        mul_le_mul_of_nonneg_left (sum_range_rpow_le_zeta (half_add_gt_one h1) M)
          (mul_nonneg hc (chainWeight_pos n).le)
    _ = _ := by ring

end Rows

/-- An indicator sum is dominated by the plain sum over an interval containing its support. -/
theorem sum_range_ite_le_sum_Ico {p : ℕ → Prop} [DecidablePred p] {f : ℕ → ℝ} {M a b : ℕ}
    (hp : ∀ k, p k → a ≤ k ∧ k < b) (hf : ∀ k, 0 ≤ f k) :
    ∑ k ∈ range M, (if p k then f k else 0) ≤ ∑ k ∈ Ico a b, f k := by
  rw [← sum_filter]
  exact sum_le_sum_of_subset_of_nonneg (fun k hk => mem_Ico.mpr (hp k (mem_filter.mp hk).2))
    fun k _ _ => hf k

/-- `2 ⌊√N⌋ ≥ √N` for `N ≥ 1`. -/
private theorem sqrt_le_two_mul_natSqrt {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt N ≤ 2 * (Nat.sqrt N : ℝ) := by
  have h1 : 1 ≤ Nat.sqrt N := Nat.sqrt_pos.mpr hN
  have h2 := Real.real_sqrt_lt_nat_sqrt_succ (a := N)
  have : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast h1
  linarith

/-- Small moduli lie below `⌊√N⌋`. -/
private theorem lt_natSqrt_of_small {n k : ℕ} (h : chainSmall n k) : k < Nat.sqrt (n + 1) := by
  unfold chainSmall at h
  have : (k + 1) ^ 2 ≤ n + 1 := by nlinarith
  exact Nat.lt_of_succ_le (Nat.le_sqrt'.mpr this)

/-- Large moduli lie at or above `⌊√N⌋ − 1`. -/
private theorem natSqrt_sub_one_le_of_not_small {n k : ℕ} (h : ¬ chainSmall n k) :
    Nat.sqrt (n + 1) - 1 ≤ k := by
  unfold chainSmall at h
  by_contra hk
  push Not at hk
  have hs : k + 2 ≤ Nat.sqrt (n + 1) := by omega
  have := Nat.sqrt_le' (n + 1)
  have : (k + 1) * (k + 1 + 1) ≤ Nat.sqrt (n + 1) ^ 2 := by nlinarith
  omega

section RowsTwo

variable {η : ℝ} (h1 : 1 / 2 < η) (h2 : η ≤ 1)
include h1 h2

omit h1 h2 in
private theorem chainShortExponent_eq : chainShortExponent η = η / 2 - 5 / 4 := by
  unfold chainShortExponent chainSourceExponent; ring

private theorem row_short (n M : ℕ) :
    ∑ k ∈ range M, (if chainSmall n k then chainShortTerm η n k else 0) * chainWeight k ≤
      (2 * (pmPowerDampedDivisorDensity η).re +
        chainSourceConstant η * 2 ^ (1 - chainSourceExponent η) / (1 + chainShortExponent η) +
        Real.sqrt 2 * realZetaSeries (1 / 2 + η)) * chainWeight n := by
  have hη : 0 < η := by linarith
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hη
  have hcP := chainSourceConstant_pos h1 h2
  set ρ := (pmPowerDampedDivisorDensity η).re
  set cP := chainSourceConstant η
  set β := 1 - chainSourceExponent η with hβ
  set s2 := chainShortExponent η with hs2
  have hs2e : s2 = η / 2 - 5 / 4 := chainShortExponent_eq
  have hβe : β = 7 / 8 - 3 * η / 4 := by rw [hβ]; unfold chainSourceExponent; ring
  have hβ0 : 0 ≤ β := by rw [hβe]; linarith
  have hs21 : 0 < 1 + s2 := by rw [hs2e]; linarith
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast Nat.succ_pos n
  have hN0 : (0 : ℝ) < N := by linarith
  set S := Nat.sqrt (n + 1)
  have hz := realZetaSeries_nonneg (1 / 2 + η)
  -- pointwise split of a short entry
  have hpt : ∀ k ∈ range M, (if chainSmall n k then chainShortTerm η n k else 0) * chainWeight k ≤
      (if k < S then 2 * ρ / N else 0) +
      (if k < S then cP * 2 ^ β * N ^ (β - 1) * ((k + 1 : ℕ) : ℝ) ^ s2 else 0) +
      (if k < n + 1 then largeDivisorSum η ((n + 1) / (k + 1 + 1)) ((n + 1) / (k + 1)) / N
        else 0) := by
    intro k _
    set K : ℝ := ((k + 1 : ℕ) : ℝ) with hK
    have hK1 : (1 : ℝ) ≤ K := by rw [hK]; exact_mod_cast Nat.succ_pos k
    have hK0 : (0 : ℝ) < K := by linarith
    have hJ0 := largeDivisorSum_nonneg η ((n + 1) / (k + 1 + 1)) ((n + 1) / (k + 1))
    by_cases hs : chainSmall n k
    · have hkS := lt_natSqrt_of_small hs
      have hkn := Nat.lt_succ_of_le (chainSmall_le hs)
      rw [if_pos hs, if_pos hkS, if_pos hkS, if_pos hkn]
      unfold chainShortTerm chainWeight
      rw [← hN, ← hK, ← hβ]
      have hu : K * K ^ (-η) * K ^ (-(1 / 2 : ℝ)) = K ^ (1 / 2 - η) := by
        calc K * K ^ (-η) * K ^ (-(1 / 2 : ℝ)) = K ^ (-η + 1) * K ^ (-(1 / 2 : ℝ)) := by
              rw [Real.rpow_add_one hK0.ne']; ring
          _ = K ^ (-η + 1 + -(1 / 2 : ℝ)) := (Real.rpow_add hK0 (-η + 1) (-(1 / 2))).symm
          _ = K ^ (1 / 2 - η) := by ring_nf
      have hu1 : K ^ (1 / 2 - η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK1 (by linarith)
      have hu0 : 0 ≤ K ^ (1 / 2 - η) := Real.rpow_nonneg hK0.le _
      have hpow : K ^ (1 / 2 - η) * (2 * N / K ^ 2) ^ β = 2 ^ β * N ^ β * K ^ s2 := by
        have e1 : (2 * N / K ^ 2) ^ β = 2 ^ β * N ^ β * K ^ (-(2 * β)) := by
          rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) hN0.le,
            show K ^ 2 = K ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hK0.le, Real.rpow_neg hK0.le]
          ring
        have e2 : K ^ (1 / 2 - η) * K ^ (-(2 * β)) = K ^ s2 := by
          rw [← Real.rpow_add hK0, hs2]
          unfold chainShortExponent
          rw [← hβ]; ring_nf
        rw [e1]
        calc K ^ (1 / 2 - η) * (2 ^ β * N ^ β * K ^ (-(2 * β)))
            = 2 ^ β * N ^ β * (K ^ (1 / 2 - η) * K ^ (-(2 * β))) := by ring
          _ = _ := by rw [e2]
      have hNb : N ^ β / N = N ^ (β - 1) := (Real.rpow_sub_one hN0.ne' β).symm
      calc K / N * (K ^ (-η) * (2 * ρ + cP * (2 * N / K ^ 2) ^ β +
              largeDivisorSum η ((n + 1) / (k + 1 + 1)) ((n + 1) / (k + 1)))) * K ^ (-(1 / 2 : ℝ))
          = (K * K ^ (-η) * K ^ (-(1 / 2 : ℝ))) * (2 * ρ) / N +
              cP * ((K * K ^ (-η) * K ^ (-(1 / 2 : ℝ))) * (2 * N / K ^ 2) ^ β) / N +
              (K * K ^ (-η) * K ^ (-(1 / 2 : ℝ))) *
                largeDivisorSum η ((n + 1) / (k + 1 + 1)) ((n + 1) / (k + 1)) / N := by ring
        _ = K ^ (1 / 2 - η) * (2 * ρ) / N + cP * (2 ^ β * N ^ β * K ^ s2) / N +
              K ^ (1 / 2 - η) * largeDivisorSum η ((n + 1) / (k + 1 + 1)) ((n + 1) / (k + 1)) / N := by
            rw [hu, hpow]
        _ ≤ 1 * (2 * ρ) / N + cP * 2 ^ β * (N ^ β / N) * K ^ s2 +
              1 * largeDivisorSum η ((n + 1) / (k + 1 + 1)) ((n + 1) / (k + 1)) / N := by
            have e2 : cP * (2 ^ β * N ^ β * K ^ s2) / N = cP * 2 ^ β * (N ^ β / N) * K ^ s2 := by ring
            rw [e2]
            have a1 : K ^ (1 / 2 - η) * (2 * ρ) / N ≤ 1 * (2 * ρ) / N :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu1 (by positivity)) hN0.le
            have a3 : K ^ (1 / 2 - η) * largeDivisorSum η ((n + 1) / (k + 1 + 1)) ((n + 1) / (k + 1)) / N ≤
                1 * largeDivisorSum η ((n + 1) / (k + 1 + 1)) ((n + 1) / (k + 1)) / N :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu1 hJ0) hN0.le
            linarith
        _ = _ := by rw [hNb]; ring
    · rw [if_neg hs, zero_mul]
      have hA0 : 0 ≤ (if k < S then 2 * ρ / N else 0) := by split_ifs <;> positivity
      have hB0 : 0 ≤ (if k < S then cP * 2 ^ β * N ^ (β - 1) * ((k + 1 : ℕ) : ℝ) ^ s2 else 0) := by
        split_ifs
        · exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
        · exact le_rfl
      have hC0 : 0 ≤ (if k < n + 1 then largeDivisorSum η ((n + 1) / (k + 1 + 1))
          ((n + 1) / (k + 1)) / N else 0) := by
        split_ifs
        · exact div_nonneg hJ0 hN0.le
        · exact le_rfl
      linarith
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib, sum_add_distrib]
  -- the constant part
  have hA : ∑ k ∈ range M, (if k < S then 2 * ρ / N else 0) ≤ 2 * ρ * N ^ (-(1 / 2 : ℝ)) := by
    refine (sum_range_ite_le_sum_range (B := S) (fun k hk => hk) fun _ => by positivity).trans ?_
    rw [sum_const, card_range, nsmul_eq_mul]
    have hS : (S : ℝ) ≤ Real.sqrt N := by rw [hN]; exact Real.nat_sqrt_le_real_sqrt
    calc (S : ℝ) * (2 * ρ / N) ≤ Real.sqrt N * (2 * ρ / N) :=
          mul_le_mul_of_nonneg_right hS (by positivity)
      _ = 2 * ρ * (Real.sqrt N / N) := by ring
      _ = _ := by rw [sqrt_div_self_eq hN0]
  -- the short-interval part
  have hB : ∑ k ∈ range M, (if k < S then cP * 2 ^ β * N ^ (β - 1) * ((k + 1 : ℕ) : ℝ) ^ s2
      else 0) ≤ cP * 2 ^ β / (1 + s2) * N ^ (-(1 / 2 : ℝ)) := by
    refine (sum_range_ite_le_sum_range (B := S) (fun k hk => hk) fun k =>
      mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)).trans ?_
    rw [← mul_sum]
    have hsum : ∑ k ∈ range S, ((k + 1 : ℕ) : ℝ) ^ s2 ≤ (S : ℝ) ^ (1 + s2) / (1 + s2) := by
      have h := sum_Icc_rpow_neg_le_div (s := -s2) (by rw [hs2e]; linarith)
        (by rw [hs2e]; linarith) S
      rw [RHTower.sum_Icc_eq_sum_range_shift, neg_neg, show 1 - -s2 = 1 + s2 by ring] at h
      refine le_trans (le_of_eq (sum_congr rfl fun k _ => ?_)) h
      push_cast; ring_nf
    have hS : (S : ℝ) ^ (1 + s2) ≤ N ^ ((1 + s2) / 2) := by
      have hSq : (S : ℝ) ≤ Real.sqrt N := by rw [hN]; exact Real.nat_sqrt_le_real_sqrt
      calc (S : ℝ) ^ (1 + s2) ≤ (Real.sqrt N) ^ (1 + s2) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hSq hs21.le
        _ = N ^ ((1 + s2) / 2) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; ring_nf
    have hexp : N ^ (β - 1) * N ^ ((1 + s2) / 2) ≤ N ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by rw [hβe, hs2e]; linarith)
    calc cP * 2 ^ β * N ^ (β - 1) * ∑ k ∈ range S, ((k + 1 : ℕ) : ℝ) ^ s2
        ≤ cP * 2 ^ β * N ^ (β - 1) * ((S : ℝ) ^ (1 + s2) / (1 + s2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ cP * 2 ^ β * N ^ (β - 1) * (N ^ ((1 + s2) / 2) / (1 + s2)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hS hs21.le) (by positivity)
      _ = cP * 2 ^ β / (1 + s2) * (N ^ (β - 1) * N ^ ((1 + s2) / 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
  -- the large-divisor part
  have hC : ∑ k ∈ range M, (if k < n + 1 then largeDivisorSum η ((n + 1) / (k + 1 + 1))
      ((n + 1) / (k + 1)) / N else 0) ≤ Real.sqrt 2 * realZetaSeries (1 / 2 + η) *
        N ^ (-(1 / 2 : ℝ)) := by
    refine (sum_range_ite_le_sum_range (B := n + 1) (fun k hk => hk) fun k =>
      div_nonneg (largeDivisorSum_nonneg _ _ _) hN0.le).trans ?_
    rw [← sum_div]
    have := sum_range_largeDivisorSum_le h1 n
    rw [← hN] at this
    calc (∑ k ∈ range (n + 1), largeDivisorSum η ((n + 1) / (k + 1 + 1)) ((n + 1) / (k + 1))) / N
        ≤ Real.sqrt 2 * realZetaSeries (1 / 2 + η) * Real.sqrt N / N :=
          div_le_div_of_nonneg_right this hN0.le
      _ = Real.sqrt 2 * realZetaSeries (1 / 2 + η) * (Real.sqrt N / N) := by ring
      _ = _ := by rw [sqrt_div_self_eq hN0]
  unfold chainWeight
  rw [← hN]
  have := add_le_add (add_le_add hA hB) hC
  calc _ ≤ _ := this
    _ = _ := by ring

omit h2 in
private theorem row_jump (n M : ℕ) :
    ∑ k ∈ range M, (if k ≤ n ∧ ¬ chainSmall n k then chainJumpTerm η n k else 0) * chainWeight k ≤
      (2 * (1 + 2 * (pmPowerDampedDivisorDensity η).re) +
        Real.sqrt 2 * (pmPowerDampedDivisorDensity η).re * realZetaSeries (1 / 2 + η)) *
          chainWeight n := by
  have hη : 0 < η := by linarith
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hη
  set ρ := (pmPowerDampedDivisorDensity η).re
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast Nat.succ_pos n
  have hN0 : (0 : ℝ) < N := by linarith
  set s0 := Nat.sqrt (n + 1) - 1
  have hz := realZetaSeries_nonneg (1 / 2 + η)
  have hpt : ∀ k ∈ range M,
      (if k ≤ n ∧ ¬ chainSmall n k then chainJumpTerm η n k else 0) * chainWeight k ≤
      (if s0 ≤ k ∧ k < n + 1 then (1 + 2 * ρ) *
          ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ)) / N else 0) +
        Real.sqrt 2 * ρ * N ^ (-(1 / 2 : ℝ)) * ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + η)) := by
    intro k _
    set K : ℝ := ((k + 1 : ℕ) : ℝ) with hK
    have hK1 : (1 : ℝ) ≤ K := by rw [hK]; exact_mod_cast Nat.succ_pos k
    have hK0 : (0 : ℝ) < K := by linarith
    have hp0 : 0 ≤ Real.sqrt 2 * ρ * N ^ (-(1 / 2 : ℝ)) * K ^ (-(1 / 2 + η)) := by positivity
    by_cases hc : k ≤ n ∧ ¬ chainSmall n k
    · rw [if_pos hc, if_pos ⟨natSqrt_sub_one_le_of_not_small hc.2, Nat.lt_succ_of_le hc.1⟩]
      unfold chainJumpTerm chainWeight
      rw [← hN, ← hK]
      set D : ℝ := ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ))
      have hD0 : 0 ≤ D := Nat.cast_nonneg _
      have hu : K * K ^ (-η) * K ^ (-(1 / 2 : ℝ)) = K ^ (1 / 2 - η) := by
        calc K * K ^ (-η) * K ^ (-(1 / 2 : ℝ)) = K ^ (-η + 1) * K ^ (-(1 / 2 : ℝ)) := by
              rw [Real.rpow_add_one hK0.ne']; ring
          _ = K ^ (-η + 1 + -(1 / 2 : ℝ)) := (Real.rpow_add hK0 (-η + 1) (-(1 / 2))).symm
          _ = K ^ (1 / 2 - η) := by ring_nf
      have hu1 : K ^ (1 / 2 - η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK1 (by linarith)
      have hramp : K ^ (1 / 2 - η) / K ^ 2 = K ^ (-(1 / 2 + η)) * K ^ (-1 : ℝ) := by
        rw [show K ^ 2 = K ^ (2 : ℝ) by norm_cast, ← Real.rpow_sub hK0, ← Real.rpow_add hK0]
        ring_nf
      have hsq : N ≤ 2 * K ^ 2 := by
        have := hc.2
        unfold chainSmall at this
        push Not at this
        have h' : ((n + 1 : ℕ) : ℝ) < (((k + 1) * (k + 1 + 1) : ℕ) : ℝ) := by exact_mod_cast this
        rw [hN, hK]; push_cast at h' ⊢; nlinarith
      have hK1' := rpow_neg_one_le_sqrt_two hN0 hK0 hsq
      have hKp : 0 ≤ K ^ (-(1 / 2 + η)) := Real.rpow_nonneg hK0.le _
      calc K / N * (K ^ (-η) * ((1 + 2 * ρ) * D + ρ * N / K ^ 2)) * K ^ (-(1 / 2 : ℝ))
          = (K * K ^ (-η) * K ^ (-(1 / 2 : ℝ))) * ((1 + 2 * ρ) * D) / N +
              ρ * ((K * K ^ (-η) * K ^ (-(1 / 2 : ℝ))) / K ^ 2) := by field_simp
        _ = K ^ (1 / 2 - η) * ((1 + 2 * ρ) * D) / N +
              ρ * (K ^ (-(1 / 2 + η)) * K ^ (-1 : ℝ)) := by rw [hu, hramp]
        _ ≤ 1 * ((1 + 2 * ρ) * D) / N +
              ρ * (K ^ (-(1 / 2 + η)) * (Real.sqrt 2 * N ^ (-(1 / 2 : ℝ)))) := by
            gcongr
        _ = _ := by ring
    · rw [if_neg hc, zero_mul]
      refine le_trans ?_ (le_add_of_nonneg_left (by split_ifs <;> positivity))
      exact hp0
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib]
  have hA : ∑ k ∈ range M, (if s0 ≤ k ∧ k < n + 1 then (1 + 2 * ρ) *
      ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ)) / N else 0) ≤
      2 * (1 + 2 * ρ) * N ^ (-(1 / 2 : ℝ)) := by
    refine (sum_range_ite_le_sum_Ico (a := s0) (b := n + 1) (fun k hk => hk)
      fun k => by positivity).trans ?_
    rw [← sum_div, ← mul_sum]
    have hs0 : s0 ≤ n + 1 := by
      have := Nat.sqrt_le_self (n + 1); omega
    rw [sum_Ico_div_sub_div (n + 1) s0 (n + 1) hs0]
    have hS1 : 1 ≤ Nat.sqrt (n + 1) := Nat.sqrt_pos.mpr (Nat.succ_pos n)
    have hs01 : s0 + 1 = Nat.sqrt (n + 1) := by omega
    have hdiv : (((n + 1) / (s0 + 1) : ℕ) : ℝ) ≤ 2 * Real.sqrt N := by
      rw [hs01]
      have hc := Nat.cast_div_le (m := n + 1) (n := Nat.sqrt (n + 1)) (α := ℝ)
      have hsq := sqrt_le_two_mul_natSqrt (Nat.succ_pos n)
      have hSpos : (0 : ℝ) < (Nat.sqrt (n + 1) : ℝ) := by exact_mod_cast hS1
      rw [← hN] at hc hsq
      refine hc.trans ?_
      rw [div_le_iff₀ hSpos]
      have : N = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hN0.le).symm
      nlinarith [Real.sqrt_nonneg N]
    have hlast : (0 : ℝ) ≤ (((n + 1) / (n + 1 + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (1 + 2 * ρ) * ((((n + 1) / (s0 + 1) : ℕ) : ℝ) - (((n + 1) / (n + 1 + 1) : ℕ) : ℝ)) / N
        ≤ (1 + 2 * ρ) * (2 * Real.sqrt N) / N := by
          apply div_le_div_of_nonneg_right _ hN0.le
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * (1 + 2 * ρ) * (Real.sqrt N / N) := by ring
      _ = _ := by rw [sqrt_div_self_eq hN0]
  have hB : ∑ k ∈ range M, Real.sqrt 2 * ρ * N ^ (-(1 / 2 : ℝ)) * ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + η)) ≤
      Real.sqrt 2 * ρ * realZetaSeries (1 / 2 + η) * N ^ (-(1 / 2 : ℝ)) := by
    rw [← mul_sum]
    calc Real.sqrt 2 * ρ * N ^ (-(1 / 2 : ℝ)) * ∑ k ∈ range M, ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + η))
        ≤ Real.sqrt 2 * ρ * N ^ (-(1 / 2 : ℝ)) * realZetaSeries (1 / 2 + η) :=
          mul_le_mul_of_nonneg_left (sum_range_rpow_le_zeta (half_add_gt_one h1) M) (by positivity)
      _ = _ := by ring
  unfold chainWeight
  rw [← hN]
  have := add_le_add hA hB
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **The weighted row bound** `Σ_k |C(n,k)| w(k) ≤ R w(n)`. -/
theorem sum_range_abs_centeredRow_mul_weight_le (n M : ℕ) :
    ∑ k ∈ range M, |arithmeticDampingCenteredRow η n k| * chainWeight k ≤
      chainRowConstant η * chainWeight n := by
  have hpt : ∀ k ∈ range M, |arithmeticDampingCenteredRow η n k| * chainWeight k ≤
      (if n < k then (1 + η) * (pmPowerDampedDivisorDensity η).re * ((k + 1 : ℕ) : ℝ) ^ (-1 - η)
        else 0) * chainWeight k +
      (if k ≤ n then chainDerivativeTerm η n k else 0) * chainWeight k +
      (if chainSmall n k then chainShortTerm η n k else 0) * chainWeight k +
      (if k ≤ n ∧ ¬ chainSmall n k then chainJumpTerm η n k else 0) * chainWeight k := by
    intro k _
    have := mul_le_mul_of_nonneg_right (abs_centeredRow_le_pieces h1 h2 n k) (chainWeight_pos k).le
    linarith
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib]
  have hE := row_entrance h1 n M
  have hA := row_derivative h1 h2 n M
  have hS := row_short h1 h2 n M
  have hL := row_jump h1 n M
  unfold chainRowConstant
  nlinarith [chainWeight_pos n]

end RowsTwo

end

end GaloisForLFunctions.BezoutValuationIncidence
