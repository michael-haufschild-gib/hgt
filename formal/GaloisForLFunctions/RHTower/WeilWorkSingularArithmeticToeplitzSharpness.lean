import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

/-!
# Sharpness of the logarithmic multiplicative Toeplitz relaxation

An unconditional nonnegative, prime-supported weight system satisfies every
finite multiplicative Toeplitz ceiling with budget `log N`, yet has prime
spikes arbitrarily close to the full normalized square-mass constant one.
This is a limitation of the extracted ceilings, not a Weil-positive source.
The construction retains every cutoff and every complex test vector.
-/

noncomputable section

open Finset
open scoped ComplexConjugate

namespace RHTower.WeilSingularArithmetic

private def shiftForm (N p : ℕ) (c : ℕ → ℂ) : ℝ :=
  2 * ∑ m ∈ Icc 1 N, (c (p * m) * conj (c m)).re

private def vectorMass (N : ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ m ∈ Icc 1 N, ‖c m‖ ^ 2

private theorem twice_re_mul_conj_le (z w : ℂ) :
    2 * (z * conj w).re ≤ ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  have h := Complex.re_le_norm (z * conj w)
  rw [norm_mul, Complex.norm_conj] at h
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

private theorem shiftForm_le (N p : ℕ) (hp : 2 ≤ p) (c : ℕ → ℂ)
    (hc : ∀ m, N < m → c m = 0) :
    shiftForm N p c ≤ 2 * vectorMass N c ∧
      (N < p ^ 2 → shiftForm N p c ≤ vectorMass N c) := by
  let S := (Icc 1 N).filter fun m => p * m ≤ N
  have hsub : S ⊆ Icc 1 N := filter_subset _ _
  have hi : S.image (p * ·) ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    obtain ⟨hm, hpm⟩ := mem_filter.mp hm
    exact mem_Icc.mpr ⟨by have := (mem_Icc.mp hm).1; nlinarith, hpm⟩
  have hinj : Set.InjOn (p * ·) (S : Set ℕ) := by
    intro x _ y _ h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h
  have heq : shiftForm N p c =
      ∑ m ∈ S, 2 * (c (p * m) * conj (c m)).re := by
    unfold shiftForm
    rw [mul_sum]
    apply (sum_subset hsub ?_).symm
    intro m hm hn
    have hpm : N < p * m := by
      by_contra h
      exact hn (mem_filter.mpr ⟨hm, by omega⟩)
    simp [hc _ hpm]
  have hbound : shiftForm N p c ≤
      (∑ m ∈ S.image (p * ·), ‖c m‖ ^ 2) + ∑ m ∈ S, ‖c m‖ ^ 2 := by
    rw [heq, sum_image hinj, ← sum_add_distrib]
    exact sum_le_sum fun m _ => twice_re_mul_conj_le _ _
  have hleft : (∑ m ∈ S.image (p * ·), ‖c m‖ ^ 2) ≤ vectorMass N c :=
    sum_le_sum_of_subset_of_nonneg hi fun _ _ _ => sq_nonneg _
  have hright : (∑ m ∈ S, ‖c m‖ ^ 2) ≤ vectorMass N c :=
    sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  refine ⟨by linarith, fun hN => ?_⟩
  have hd : Disjoint (S.image (p * ·)) S := by
    apply disjoint_left.mpr
    intro n hn hnS
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    have hm1 := (mem_Icc.mp (hsub hm)).1
    have hpp := (mem_filter.mp hnS).2
    nlinarith
  have hu : S.image (p * ·) ∪ S ⊆ Icc 1 N := union_subset hi hsub
  rw [← sum_union hd] at hbound
  exact hbound.trans (sum_le_sum_of_subset_of_nonneg hu fun _ _ _ => sq_nonneg _)

/-- A recursively chosen sequence of primes with growing logarithmic gaps. -/
private def spikePrime : ℕ → ℕ
  | 0 => 2
  | j + 1 => (Nat.exists_infinite_primes
      (spikePrime j ^ (2 * (j + 1) * (j + 3)) + 1)).choose

private theorem spikePrime_prime (j : ℕ) : (spikePrime j).Prime := by
  cases j with
  | zero => exact Nat.prime_two
  | succ j => exact (Nat.exists_infinite_primes _).choose_spec.2

private theorem spikePrime_step (j : ℕ) :
    spikePrime j ^ (2 * (j + 1) * (j + 3)) < spikePrime (j + 1) := by
  exact (Nat.exists_infinite_primes _).choose_spec.1

private theorem spikePrime_strictMono : StrictMono spikePrime := by
  apply strictMono_nat_of_lt_succ
  intro j
  exact (Nat.le_self_pow (by positivity : 2 * (j + 1) * (j + 3) ≠ 0) _).trans_lt
    (spikePrime_step j)

private theorem spikePrime_log_nonneg (j : ℕ) : 0 ≤ Real.log (spikePrime j) :=
  Real.log_nonneg (by exact_mod_cast (spikePrime_prime j).one_le)

private theorem spikePrime_log_budget (j : ℕ) :
    2 * (j + 2 : ℝ) * (∑ i ∈ range j, Real.log (spikePrime i)) ≤
      Real.log (spikePrime j) := by
  cases j with
  | zero => simpa using spikePrime_log_nonneg 0
  | succ j =>
    have hsum : (∑ i ∈ range (j + 1), Real.log (spikePrime i)) ≤
        (j + 1 : ℝ) * Real.log (spikePrime j) := by
      calc
        _ ≤ ∑ _i ∈ range (j + 1), Real.log (spikePrime j) := by
          apply sum_le_sum
          intro i hi
          exact Real.log_le_log (by exact_mod_cast (spikePrime_prime i).pos)
            (by exact_mod_cast spikePrime_strictMono.monotone (by simpa using mem_range.mp hi))
        _ = _ := by simp
    have hpos : (0 : ℝ) < spikePrime j := by exact_mod_cast (spikePrime_prime j).pos
    have hle : (spikePrime j : ℝ) ^ (2 * (j + 1) * (j + 3)) ≤ spikePrime (j + 1) :=
      by exact_mod_cast (spikePrime_step j).le
    have hlog := Real.log_le_log (pow_pos hpos _) hle
    rw [Real.log_pow] at hlog
    push_cast at hlog ⊢
    nlinarith [mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * (j + 3 : ℝ))]

private def spikeAmplitude (j : ℕ) : ℝ :=
  ((j + 1 : ℝ) / (j + 2)) * Real.log (spikePrime j)

private theorem spikeAmplitude_nonneg (j : ℕ) : 0 ≤ spikeAmplitude j := by
  exact mul_nonneg (by positivity) (spikePrime_log_nonneg j)

private theorem spikeAmplitude_le (j : ℕ) : spikeAmplitude j ≤ Real.log (spikePrime j) := by
  apply mul_le_of_le_one_left (spikePrime_log_nonneg j)
  exact (div_le_one (by positivity : 0 < (j : ℝ) + 2)).mpr (by linarith)

private theorem spikeAmplitude_budget (j : ℕ) :
    spikeAmplitude j + 2 * (∑ i ∈ range j, spikeAmplitude i) ≤
      Real.log (spikePrime j) := by
  have hsum := sum_le_sum (s := range j) (fun i _ => spikeAmplitude_le i)
  have hbudget := spikePrime_log_budget j
  have hden : 0 < (j : ℝ) + 2 := by positivity
  have hdivide : 2 * (∑ i ∈ range j, spikeAmplitude i) ≤
      Real.log (spikePrime j) / (j + 2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsum hden.le]
  change ((j + 1 : ℝ) / (j + 2)) * Real.log (spikePrime j) +
    2 * (∑ i ∈ range j, spikeAmplitude i) ≤ _
  have hid : ((j + 1 : ℝ) / (j + 2)) * Real.log (spikePrime j) +
      Real.log (spikePrime j) / (j + 2) = Real.log (spikePrime j) := by
    field_simp
    ring
  linarith

/-- Sparse weights used only to test the strength of the Toeplitz relaxation. -/
def sparseToeplitzWeight (n : ℕ) : ℝ := by
  classical
  exact if h : ∃ j, spikePrime j = n then Real.sqrt n * spikeAmplitude (Nat.find h) else 0

private theorem sparseToeplitzWeight_at (j : ℕ) :
    sparseToeplitzWeight (spikePrime j) = Real.sqrt (spikePrime j) * spikeAmplitude j := by
  classical
  have h : ∃ i, spikePrime i = spikePrime j := ⟨j, rfl⟩
  have heq : Nat.find h = j := spikePrime_strictMono.injective (Nat.find_spec h)
  simp only [sparseToeplitzWeight, dif_pos h, heq]

/-- The construction has nonnegative weights. -/
theorem sparseToeplitzWeight_nonneg (n : ℕ) : 0 ≤ sparseToeplitzWeight n := by
  classical
  unfold sparseToeplitzWeight
  split_ifs
  · exact mul_nonneg (Real.sqrt_nonneg _) (spikeAmplitude_nonneg _)
  · rfl

/-- Its support consists entirely of primes. -/
theorem sparseToeplitzWeight_eq_zero_of_not_prime {n : ℕ} (hn : ¬ n.Prime) :
    sparseToeplitzWeight n = 0 := by
  classical
  unfold sparseToeplitzWeight
  apply dif_neg
  rintro ⟨j, rfl⟩
  exact hn (spikePrime_prime j)

private theorem sparse_sum_eq (N k : ℕ)
    (hk : ∀ i, spikePrime i ≤ N ↔ i < k) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 2 N, sparseToeplitzWeight n / Real.sqrt n * f n) =
      ∑ i ∈ range k, spikeAmplitude i * f (spikePrime i) := by
  classical
  have hs : (range k).image spikePrime ⊆ Icc 2 N := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    exact mem_Icc.mpr ⟨(spikePrime_prime i).two_le, (hk i).mpr (mem_range.mp hi)⟩
  rw [← sum_subset hs]
  · rw [sum_image (spikePrime_strictMono.injective.injOn)]
    apply sum_congr rfl
    intro i _
    rw [sparseToeplitzWeight_at]
    have hp : (0 : ℝ) < spikePrime i := by exact_mod_cast (spikePrime_prime i).pos
    field_simp [ne_of_gt (Real.sqrt_pos.2 hp)]
  · intro n hn hnot
    have hz : ¬ ∃ i, spikePrime i = n := by
      rintro ⟨i, rfl⟩
      exact hnot (mem_image.mpr ⟨i, mem_range.mpr ((hk i).mp (mem_Icc.mp hn).2), rfl⟩)
    simp [sparseToeplitzWeight, hz]

/-- The exact family of ceilings extracted from Weil positivity, with no
additive constant. No converse to Weil positivity is built into this definition. -/
def HasLogarithmicToeplitzCeiling (lam : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ c : ℕ → ℂ, (∀ m, N < m → c m = 0) →
    2 * ∑ n ∈ Icc 2 N, lam n / Real.sqrt n *
        (∑ m ∈ Icc 1 N, c (n * m) * conj (c m)).re ≤
      Real.log N * ∑ m ∈ Icc 1 N, ‖c m‖ ^ 2

private theorem exists_spike_cutoff (N : ℕ) :
    ∃ k, ∀ i, spikePrime i ≤ N ↔ i < k := by
  classical
  have hex : ∃ i, N < spikePrime i :=
    ⟨N + 1, (Nat.lt_succ_self N).trans_le (spikePrime_strictMono.id_le _)⟩
  let k := Nat.find hex
  refine ⟨k, ?_⟩
  intro i
  constructor
  · intro hi
    by_contra h
    have hki : k ≤ i := by omega
    have hge := spikePrime_strictMono.monotone hki
    have hlast : N < spikePrime k := Nat.find_spec hex
    omega
  · intro hi
    have hnot := Nat.find_min hex hi
    omega

/-- Every cutoff and every complex test vector obey the logarithmic ceiling. -/
theorem sparseToeplitzWeight_ceiling : HasLogarithmicToeplitzCeiling sparseToeplitzWeight := by
  classical
  intro N hN c hc
  obtain ⟨k, hk⟩ := exists_spike_cutoff N
  rw [sparse_sum_eq N k hk]
  have heq : 2 * (∑ i ∈ range k, spikeAmplitude i *
      (∑ m ∈ Icc 1 N, c (spikePrime i * m) * conj (c m)).re) =
      ∑ i ∈ range k, spikeAmplitude i * shiftForm N (spikePrime i) c := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [Complex.re_sum]
    unfold shiftForm
    ring
  rw [heq]
  change _ ≤ Real.log N * vectorMass N c
  have hM : 0 ≤ vectorMass N c := sum_nonneg fun _ _ => sq_nonneg _
  have hshift (i : ℕ) := shiftForm_le N (spikePrime i) (spikePrime_prime i).two_le c hc
  have hcoarse (j : ℕ) :
      (∑ i ∈ range j, spikeAmplitude i * shiftForm N (spikePrime i) c) ≤
        2 * (∑ i ∈ range j, spikeAmplitude i) * vectorMass N c := by
    calc
      _ ≤ ∑ i ∈ range j, spikeAmplitude i * (2 * vectorMass N c) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hshift i).1 (spikeAmplitude_nonneg i)
      _ = _ := by rw [← sum_mul]; ring
  cases hkeq : k with
  | zero =>
    simp only [sum_range_zero]
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hN)) hM
  | succ j =>
    have hjN : spikePrime j ≤ N := (hk j).mpr (by omega)
    have hlog := Real.log_le_log
      (by exact_mod_cast (spikePrime_prime j).pos : (0 : ℝ) < spikePrime j)
      (by exact_mod_cast hjN : (spikePrime j : ℝ) ≤ N)
    have hb := spikeAmplitude_budget j
    by_cases hsmall : N < spikePrime j ^ 2
    · rw [sum_range_succ]
      have hlast := mul_le_mul_of_nonneg_left ((hshift j).2 hsmall) (spikeAmplitude_nonneg j)
      have hbudget := mul_le_mul_of_nonneg_right (hb.trans hlog) hM
      nlinarith [hcoarse j]
    · have hp : (0 : ℝ) < spikePrime j := by exact_mod_cast (spikePrime_prime j).pos
      have hNlarge : (spikePrime j : ℝ) ^ 2 ≤ N := by exact_mod_cast (not_lt.mp hsmall)
      have hloglarge := Real.log_le_log (pow_pos hp 2) hNlarge
      rw [Real.log_pow] at hloglarge
      norm_num only [Nat.cast_ofNat] at hloglarge
      have hnonneg : 0 ≤ ∑ i ∈ range j, spikeAmplitude i :=
        sum_nonneg fun i _ => spikeAmplitude_nonneg i
      have hsum : 2 * (∑ i ∈ range (j + 1), spikeAmplitude i) ≤ Real.log N := by
        rw [sum_range_succ]
        linarith
      exact (hcoarse (j + 1)).trans (mul_le_mul_of_nonneg_right hsum hM)

private theorem sparseToeplitzWeight_spike_square (j : ℕ) :
    sparseToeplitzWeight (spikePrime j) ^ 2 / spikePrime j =
      ((j + 1 : ℝ) / (j + 2)) ^ 2 * Real.log (spikePrime j) ^ 2 := by
  have hp : (0 : ℝ) < spikePrime j := by exact_mod_cast (spikePrime_prime j).pos
  rw [sparseToeplitzWeight_at, mul_pow, Real.sq_sqrt hp.le]
  unfold spikeAmplitude
  field_simp

/-- Matching upper constant, valid at every cutoff. -/
theorem sparseToeplitzWeight_square_mass_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 2 N, sparseToeplitzWeight n ^ 2 / n) ≤ Real.log N ^ 2 := by
  obtain ⟨k, hk⟩ := exists_spike_cutoff N
  have heq : (∑ n ∈ Icc 2 N, sparseToeplitzWeight n ^ 2 / n) =
      ∑ i ∈ range k, spikeAmplitude i ^ 2 := by
    calc
      _ = ∑ n ∈ Icc 2 N, sparseToeplitzWeight n / Real.sqrt n *
          (sparseToeplitzWeight n / Real.sqrt n) := by
        apply sum_congr rfl
        intro n hn
        rw [div_mul_div_comm, ← sq, ← sq, Real.sq_sqrt (Nat.cast_nonneg n)]
      _ = ∑ i ∈ range k, spikeAmplitude i *
          (sparseToeplitzWeight (spikePrime i) / Real.sqrt (spikePrime i)) :=
        sparse_sum_eq N k hk _
      _ = _ := by
        apply sum_congr rfl
        intro i _
        rw [sparseToeplitzWeight_at]
        have hp : (0 : ℝ) < spikePrime i := by exact_mod_cast (spikePrime_prime i).pos
        field_simp [ne_of_gt (Real.sqrt_pos.2 hp)]
  rw [heq]
  apply (sum_sq_le_sq_sum_of_nonneg (fun i _ => spikeAmplitude_nonneg i)).trans
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hnonneg : 0 ≤ ∑ i ∈ range k, spikeAmplitude i :=
    sum_nonneg fun i _ => spikeAmplitude_nonneg i
  have hsum : (∑ i ∈ range k, spikeAmplitude i) ≤ Real.log N := by
    cases hkeq : k with
    | zero => simpa using hlogN
    | succ j =>
      have hpN : spikePrime j ≤ N := (hk j).mpr (by omega)
      have hlog := Real.log_le_log
        (by exact_mod_cast (spikePrime_prime j).pos : (0 : ℝ) < spikePrime j)
        (by exact_mod_cast hpN : (spikePrime j : ℝ) ≤ N)
      have hb := spikeAmplitude_budget j
      have hs : 0 ≤ ∑ i ∈ range j, spikeAmplitude i :=
        sum_nonneg fun i _ => spikeAmplitude_nonneg i
      rw [sum_range_succ]
      linarith
  nlinarith

/-- At arbitrarily large prime cutoffs, the prime-square mass exceeds every
constant strictly below one. Thus all Toeplitz ceilings alone cannot improve
the leading constant in the primitive-set square-mass estimate. -/
theorem sparseToeplitzWeight_prime_mass_gt (θ : ℝ) (hθ : θ < 1) (N : ℕ) :
    ∃ P : ℕ, N ≤ P ∧
      θ * Real.log P ^ 2 <
        ∑ p ∈ (Icc 2 P).filter Nat.Prime, sparseToeplitzWeight p ^ 2 / p := by
  obtain ⟨j, hj⟩ := exists_nat_gt (max (N : ℝ) (2 / (1 - θ)))
  have hjN : N ≤ j := by exact_mod_cast (le_max_left _ _).trans hj.le
  have hjθ : 2 / (1 - θ) < (j : ℝ) := (le_max_right _ _).trans_lt hj
  have hden : 0 < (j : ℝ) + 2 := by positivity
  have hdiv : 2 / ((j : ℝ) + 2) < 1 - θ := by
    apply (div_lt_iff₀ hden).mpr
    have h := (div_lt_iff₀ (by linarith : 0 < 1 - θ)).mp hjθ
    nlinarith
  have hid : ((j + 1 : ℝ) / (j + 2)) ^ 2 =
      1 - 2 / (j + 2) + (1 / (j + 2)) ^ 2 := by
    field_simp
    ring
  have hratio : θ < ((j + 1 : ℝ) / (j + 2)) ^ 2 := by
    rw [hid]
    nlinarith [sq_nonneg (1 / ((j : ℝ) + 2))]
  refine ⟨spikePrime j, hjN.trans (spikePrime_strictMono.id_le j), ?_⟩
  have hlog : 0 < Real.log (spikePrime j) := Real.log_pos
    (by exact_mod_cast (spikePrime_prime j).one_lt)
  have hterm : θ * Real.log (spikePrime j) ^ 2 <
      sparseToeplitzWeight (spikePrime j) ^ 2 / spikePrime j := by
    rw [sparseToeplitzWeight_spike_square]
    exact mul_lt_mul_of_pos_right hratio (sq_pos_of_pos hlog)
  apply hterm.trans_le
  exact single_le_sum (f := fun p : ℕ => sparseToeplitzWeight p ^ 2 / (p : ℝ))
    (fun p _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg p))
    (mem_filter.mpr ⟨mem_Icc.mpr ⟨(spikePrime_prime j).two_le, le_rfl⟩, spikePrime_prime j⟩)

/-- Unconditional sharpness witness for the complete logarithmic Toeplitz
relaxation. No Weil-positive source is assumed or claimed. -/
theorem exists_sharp_prime_supported_toeplitz_weight :
    ∃ lam : ℕ → ℝ, (∀ n, 0 ≤ lam n) ∧
      (∀ n, ¬ n.Prime → lam n = 0) ∧ HasLogarithmicToeplitzCeiling lam ∧
      (∀ N : ℕ, 1 ≤ N → (∑ n ∈ Icc 2 N, lam n ^ 2 / n) ≤ Real.log N ^ 2) ∧
      ∀ θ : ℝ, θ < 1 → ∀ N : ℕ, ∃ P : ℕ, N ≤ P ∧
        θ * Real.log P ^ 2 < ∑ p ∈ (Icc 2 P).filter Nat.Prime, lam p ^ 2 / p :=
  ⟨sparseToeplitzWeight, sparseToeplitzWeight_nonneg,
    fun _ => sparseToeplitzWeight_eq_zero_of_not_prime, sparseToeplitzWeight_ceiling,
    sparseToeplitzWeight_square_mass_le, sparseToeplitzWeight_prime_mass_gt⟩

end RHTower.WeilSingularArithmetic
