import GaloisForLFunctions.RHTower.EulerDeletionBalancedPeriodFreedom
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Exact moment freedom under complete multiplicativity

Two large primes with equal cofactor cutoffs support opposite prime-value perturbations.
The resulting global positive completely multiplicative functions preserve every applicable
linear deletion endpoint. Their quadratic response is exactly twice the perturbation square
times a shorter literal coefficient prefix. At cutoff 930 this produces both curvature signs,
with all divisor-of-thirty deletion endpoints zero.

The proof uses factorization, divisor reindexing and symbolic ring identities. Exploratory
calculations supply no proof certificates. This refutes a finite inference; it says nothing
about a zero-forced relation for the literal infinite Mellin weights or RH.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.DeletionPairedPrimes
open DeletionBalancedPeriods

def primePairWeight (p q : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (1+t) ^ n.factorization p * (1-t) ^ n.factorization q

theorem weight_one (p q : ℕ) (t : ℝ) : primePairWeight p q t 1 = 1 := by
  simp [primePairWeight]

theorem weight_mul (p q : ℕ) (t : ℝ) (a b : ℕ) :
    primePairWeight p q t (a*b) = primePairWeight p q t a * primePairWeight p q t b := by
  by_cases ha : a = 0
  · subst a; simp [primePairWeight]
  by_cases hb : b = 0
  · subst b; simp [primePairWeight]
  simp only [primePairWeight, if_neg ha, if_neg hb, if_neg (mul_ne_zero ha hb),
    Nat.factorization_mul ha hb, Finsupp.add_apply, pow_add]
  ring

theorem weight_pos (p q : ℕ) {t : ℝ} (ht : |t| < 1) {n : ℕ} (hn : 0 < n) :
    0 < primePairWeight p q t n := by
  rw [primePairWeight, if_neg (by omega)]
  obtain ⟨hl, hu⟩ := abs_lt.mp ht
  exact mul_pos (pow_pos (by linarith) _) (pow_pos (by linarith) _)

theorem factorization_indicator {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hbound : n < p*p) : n.factorization p = if p ∣ n then 1 else 0 := by
  split_ifs with hd
  · obtain ⟨m, rfl⟩ := hd
    have hm : 0 < m := Nat.pos_of_mul_pos_left hn
    have hmp : m < p := (Nat.mul_lt_mul_left hp.pos).mp hbound
    rw [Nat.factorization_mul hp.ne_zero (by omega), Finsupp.add_apply,
      hp.factorization_self, Nat.factorization_eq_zero_of_lt hmp, add_zero]
  · exact Nat.factorization_eq_zero_of_not_dvd hd

theorem weight_restriction {p q N n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p.Coprime q) (hpp : N < p*p) (hqq : N < q*q) (hpqN : N < p*q)
    (hn : n ∈ Finset.Icc 1 N) (t : ℝ) :
    primePairWeight p q t n = 1 + (if p ∣ n then t else 0) - (if q ∣ n then t else 0) := by
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hn0 : 0 < n := by omega
  rw [primePairWeight, if_neg (by omega),
    factorization_indicator hp hn0 (lt_of_le_of_lt hnN hpp),
    factorization_indicator hq hn0 (lt_of_le_of_lt hnN hqq)]
  by_cases hpn : p ∣ n <;> by_cases hqn : q ∣ n
  · have h := Nat.le_of_dvd hn0 (hpq.mul_dvd_of_dvd_of_dvd hpn hqn)
    omega
  all_goals simp [hpn, hqn]

theorem sum_on_multiples {p N M : ℕ} (hp : 0 < p) (hM : N / p = M)
    (f : ℕ → ℝ) (hf : ∀ j ∈ Finset.Icc 1 M, f (p*j) = f j) :
    (∑ n ∈ Finset.Icc 1 N, if p ∣ n then f n else 0) =
      ∑ j ∈ Finset.Icc 1 M, f j := by
  rw [← Finset.sum_filter, sum_Icc_filter_dvd_reindex p N hp f, hM]
  exact Finset.sum_congr rfl hf

/-- Every scalar observation is classified by its three values at the paired weights. -/
theorem paired_observation {p q N M : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p.Coprime q) (hpp : N < p*p) (hqq : N < q*q) (hpqN : N < p*q)
    (hMp : N / p = M) (hMq : N / q = M) (f : ℕ → ℝ)
    (hfp : ∀ j ∈ Finset.Icc 1 M, f (p*j) = f j)
    (hfq : ∀ j ∈ Finset.Icc 1 M, f (q*j) = f j) (F : ℝ → ℝ) (t : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, f n * F (primePairWeight p q t n)) =
      F 1 * (∑ n ∈ Finset.Icc 1 N, f n) +
        (F (1+t) + F (1-t) - 2*F 1) * (∑ j ∈ Finset.Icc 1 M, f j) := by
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      f n * F (primePairWeight p q t n) = F 1 * f n +
        (F (1+t)-F 1) * (if p ∣ n then f n else 0) +
        (F (1-t)-F 1) * (if q ∣ n then f n else 0) := by
    rw [weight_restriction hp hq hpq hpp hqq hpqN hn]
    by_cases hpn : p ∣ n <;> by_cases hqn : q ∣ n
    · have h := Nat.le_of_dvd (by have := (Finset.mem_Icc.mp hn).1; omega)
        (hpq.mul_dvd_of_dvd_of_dvd hpn hqn)
      have := (Finset.mem_Icc.mp hn).2
      omega
    all_goals simp only [hpn, hqn, if_true, if_false, add_zero, sub_zero]; ring
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_on_multiples hp.pos hMp f hfp, sum_on_multiples hq.pos hMq f hfq]
  ring

/-- Exact two-channel moment response, for the actual global completely multiplicative weight. -/
theorem paired_moments {p q N M : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p.Coprime q) (hpp : N < p*p) (hqq : N < q*q) (hpqN : N < p*q)
    (hMp : N / p = M) (hMq : N / q = M) (f : ℕ → ℝ)
    (hfp : ∀ j ∈ Finset.Icc 1 M, f (p*j) = f j)
    (hfq : ∀ j ∈ Finset.Icc 1 M, f (q*j) = f j) (t : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, f n * primePairWeight p q t n) =
        ∑ n ∈ Finset.Icc 1 N, f n ∧
    (∑ n ∈ Finset.Icc 1 N, f n * primePairWeight p q t n ^ (2 : ℕ)) =
        (∑ n ∈ Finset.Icc 1 N, f n) + 2*t^(2 : ℕ)*(∑ j ∈ Finset.Icc 1 M, f j) := by
  have hl (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      f n * primePairWeight p q t n = f n + t * (if p ∣ n then f n else 0) -
        t * (if q ∣ n then f n else 0) := by
    rw [weight_restriction hp hq hpq hpp hqq hpqN hn]
    split_ifs <;> ring
  have hs (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      f n * primePairWeight p q t n ^ (2 : ℕ) = f n + (2*t+t^(2 : ℕ)) * (if p ∣ n then f n else 0) +
        (-2*t+t^(2 : ℕ)) * (if q ∣ n then f n else 0) := by
    rw [weight_restriction hp hq hpq hpp hqq hpqN hn]
    by_cases hpn : p ∣ n <;> by_cases hqn : q ∣ n
    · have h := Nat.le_of_dvd (by have := (Finset.mem_Icc.mp hn).1; omega)
        (hpq.mul_dvd_of_dvd_of_dvd hpn hqn)
      have := (Finset.mem_Icc.mp hn).2
      omega
    all_goals simp only [hpn, hqn, if_true, if_false]; ring
  constructor
  · rw [Finset.sum_congr rfl hl, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, sum_on_multiples hp.pos hMp f hfp,
      sum_on_multiples hq.pos hMq f hfq]
    ring
  · rw [Finset.sum_congr rfl hs, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, sum_on_multiples hp.pos hMp f hfp,
      sum_on_multiples hq.pos hMq f hfq]
    ring

theorem coefficient_dilation {d p : ℕ} (h : d.Coprime p) (j : ℕ) :
    coefficient d (p*j) = coefficient d j := by
  simp only [coefficient, blockDeletionCoefficient, h.dvd_mul_left]

theorem coefficient_sum (d N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, coefficient d n) = (N % d : ℕ) := by
  rw [sum_Icc_eq_sum_range_succ]
  dsimp only [coefficient]
  rw [← Int.cast_sum]
  change ((deletionCoeffPartialSum d N : ℤ) : ℝ) = _
  exact congrArg (fun z : ℤ => (z : ℝ)) (deletionCoeffPartialSum_eq_mod d N)



/-- The existing literal curvature, specialized by its symbolic four-channel identity. -/
theorem cell_linear (n : ℕ) : curvatureCoefficient 2 3 5 n =
    2 * (coefficient 6 n - coefficient 3 n +
      5 * (coefficient 15 n - coefficient 30 n)) := by
  have h := curvature_coefficient_linear (p := 2) (q := 3) (r := 5)
    (by norm_num) (by norm_num) (by norm_num) n
  norm_num at h ⊢
  exact h

theorem cell_dilation {p : ℕ} (hp : Nat.Coprime 30 p) (j : ℕ) :
    curvatureCoefficient 2 3 5 (p*j) = curvatureCoefficient 2 3 5 j := by
  rw [cell_linear, cell_linear]
  rw [coefficient_dilation (hp.of_dvd_left (by norm_num : 6 ∣ 30)),
    coefficient_dilation (hp.of_dvd_left (by norm_num : 3 ∣ 30)),
    coefficient_dilation (hp.of_dvd_left (by norm_num : 15 ∣ 30)),
    coefficient_dilation hp]

theorem cell_sum (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, curvatureCoefficient 2 3 5 n) =
      2 * ((N % 6 : ℕ) - (N % 3 : ℕ) +
        5 * ((N % 15 : ℕ) - (N % 30 : ℕ)) : ℝ) := by
  simp_rw [cell_linear]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [coefficient_sum, coefficient_sum, coefficient_sum, coefficient_sum]

/-- Prime pairing preserves every deletion channel for a divisor of thirty. -/
theorem paired_endpoints {p q N M : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p.Coprime q) (hpp : N < p*p) (hqq : N < q*q) (hpqN : N < p*q)
    (hMp : N / p = M) (hMq : N / q = M)
    (h30p : Nat.Coprime 30 p) (h30q : Nat.Coprime 30 q) (hN : 30 ∣ N) (t : ℝ) :
    ∀ d, d ∣ 30 → (∑ n ∈ Finset.Icc 1 N, coefficient d n * primePairWeight p q t n) = 0 := by
  intro d hd
  have h := (paired_moments hp hq hpq hpp hqq hpqN hMp hMq (coefficient d)
    (fun j _ => coefficient_dilation (h30p.of_dvd_left hd) j)
    (fun j _ => coefficient_dilation (h30q.of_dvd_left hd) j) t).1
  rw [h, coefficient_sum, Nat.mod_eq_zero_of_dvd (dvd_trans hd hN), Nat.cast_zero]

/-- Curvature is controlled exactly by the shorter literal coefficient prefix. -/
theorem paired_curvature {p q N M : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p.Coprime q) (hpp : N < p*p) (hqq : N < q*q) (hpqN : N < p*q)
    (hMp : N / p = M) (hMq : N / q = M)
    (h30p : Nat.Coprime 30 p) (h30q : Nat.Coprime 30 q) (hN : 30 ∣ N) (t : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, curvatureCoefficient 2 3 5 n * primePairWeight p q t n ^ (2 : ℕ)) =
      4*t^(2 : ℕ)*((M % 6 : ℕ) - (M % 3 : ℕ) +
        5*((M % 15 : ℕ) - (M % 30 : ℕ)) : ℝ) := by
  have h := (paired_moments hp hq hpq hpp hqq hpqN hMp hMq (curvatureCoefficient 2 3 5)
    (fun j _ => cell_dilation h30p j) (fun j _ => cell_dilation h30q j) t).2
  rw [h, cell_sum, cell_sum]
  have hd (d : ℕ) (hd : d ∣ 30) : N % d = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans hd hN)
  rw [hd 6 (by norm_num), hd 3 (by norm_num), hd 15 (by norm_num), hd 30 (by norm_num)]
  push_cast
  ring

/-- The literal floor form of the curvature prefix, exactly as displayed on the paper card. -/
theorem cell_sum_floor (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, curvatureCoefficient 2 3 5 n) =
      6 * ((N / 3 : ℕ) : ℝ) - 12 * ((N / 6 : ℕ) : ℝ) - 150 * ((N / 15 : ℕ) : ℝ) +
        300 * ((N / 30 : ℕ) : ℝ) := by
  rw [cell_sum]
  have h : ∀ d : ℕ, ((N % d : ℕ) : ℝ) = (N : ℝ) - (d : ℝ) * ((N / d : ℕ) : ℝ) := by
    intro d
    have hc : ((d * (N / d) + N % d : ℕ) : ℝ) = (N : ℝ) :=
      congrArg (fun m : ℕ => (m : ℝ)) (Nat.div_add_mod N d)
    push_cast at hc
    linarith
  rw [h 6, h 3, h 15, h 30]
  push_cast
  ring

def negativeWeight (t : ℝ) : ℕ → ℝ := primePairWeight 59 61 t

def positiveWeight (t : ℝ) : ℕ → ℝ := primePairWeight 251 257 t

theorem negative_endpoints (t : ℝ) :
    ∀ d, d ∣ 30 → (∑ n ∈ Finset.Icc 1 930, coefficient d n * negativeWeight t n) = 0 := by
  exact paired_endpoints (p := 59) (q := 61) (M := 15) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) t

theorem positive_endpoints (t : ℝ) :
    ∀ d, d ∣ 30 → (∑ n ∈ Finset.Icc 1 930, coefficient d n * positiveWeight t n) = 0 := by
  exact paired_endpoints (p := 251) (q := 257) (M := 3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) t

theorem negative_curvature (t : ℝ) :
    (∑ n ∈ Finset.Icc 1 930, curvatureCoefficient 2 3 5 n * negativeWeight t n ^ (2 : ℕ)) = -288*t^(2 : ℕ) := by
  have h := paired_curvature (p := 59) (q := 61) (N := 930) (M := 15)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) t
  norm_num at h
  dsimp only [negativeWeight]
  rw [h]
  ring

theorem positive_curvature (t : ℝ) :
    (∑ n ∈ Finset.Icc 1 930, curvatureCoefficient 2 3 5 n * positiveWeight t n ^ (2 : ℕ)) = 12*t^(2 : ℕ) := by
  have h := paired_curvature (p := 251) (q := 257) (N := 930) (M := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) t
  norm_num at h
  dsimp only [positiveWeight]
  rw [h]
  ring

/-- Unconditional, exact countermodels and the complete multiplicative laws on all naturals. -/
theorem completely_multiplicative_closed_endpoints_opposite_curvatures :
    ∃ wMinus wPlus : ℕ → ℝ,
      wMinus 1 = 1 ∧ wPlus 1 = 1 ∧
      (∀ a b, wMinus (a*b) = wMinus a * wMinus b) ∧
      (∀ a b, wPlus (a*b) = wPlus a * wPlus b) ∧
      (∀ n, 0 < n → 0 < wMinus n ∧ 0 < wPlus n) ∧
      (∀ d, d ∣ 30 →
        (∑ n ∈ Finset.Icc 1 930, coefficient d n * wMinus n) = 0 ∧
        (∑ n ∈ Finset.Icc 1 930, coefficient d n * wPlus n) = 0) ∧
      (∑ n ∈ Finset.Icc 1 930, curvatureCoefficient 2 3 5 n * wMinus n ^ (2 : ℕ)) = -72 ∧
      (∑ n ∈ Finset.Icc 1 930, curvatureCoefficient 2 3 5 n * wPlus n ^ (2 : ℕ)) = 3 := by
  refine ⟨negativeWeight (1/2), positiveWeight (1/2), weight_one _ _ _, weight_one _ _ _,
    weight_mul _ _ _, weight_mul _ _ _, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact ⟨weight_pos _ _ (by norm_num) hn, weight_pos _ _ (by norm_num) hn⟩
  · intro d hd
    exact ⟨negative_endpoints _ d hd, positive_endpoints _ d hd⟩
  · rw [negative_curvature]
    norm_num
  · rw [positive_curvature]
    norm_num

end RHTower.DeletionPairedPrimes
