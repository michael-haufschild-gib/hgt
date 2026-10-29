import GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.PrimeSquareTrial
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheDeficitOfThePrimeFormIsADirichletEnergy
import GaloisForLFunctions.RHTower.SummableDivisorHarmonicMean

/-!
# The remaining prime-power mass after the first flip

Removing the prime and its square from the complete Mangoldt ladder leaves
at most `log p / (p² (p - 1))`. The square is unflipped. Thus the first prime
correlation can be retained with its sign before bounding the entire tail.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

open RenormalizedArithmeticPotentialTheory ArithmeticFunction ArithmeticElectrostatics

/-- The geometric tail bound holds for every finite set of integer lags. -/
theorem primePower_tail_after_square {p : ℕ} (hp : p.Prime) (T : Finset ℕ) :
    (∑ t ∈ T, if p ∣ t ∧ t ≠ p ∧ t ≠ p ^ 2 then Λ t / (t : ℝ) else 0) ≤
      Real.log p / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
  let S := T.filter (fun t => p ∣ t ∧ t ≠ p ∧ t ≠ p ^ 2)
  have hpp : p ^ 2 ≠ p := by
    intro h
    have he := Nat.pow_right_injective hp.two_le (h.trans (pow_one p).symm)
    omega
  have hpS : p ∉ S := by simp [S]
  have hp2S : p ^ 2 ∉ S := by simp [S]
  have hpinsert : p ∉ insert (p ^ 2) S := by
    simp only [mem_insert, not_or]
    exact ⟨hpp.symm, hpS⟩
  have h := sum_dvd_vonMangoldt_div_le hp (insert p (insert (p ^ 2) S))
  rw [sum_insert hpinsert, sum_insert hp2S,
    if_pos (dvd_refl p), if_pos (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)),
    vonMangoldt_apply_prime hp, vonMangoldt_prime_pow hp (by norm_num : 0 < (2 : ℕ)),
    Nat.cast_pow] at h
  have hsum : (∑ t ∈ S, if p ∣ t then Λ t / (t : ℝ) else 0) =
      ∑ t ∈ T, if p ∣ t ∧ t ≠ p ∧ t ≠ p ^ 2 then Λ t / (t : ℝ) else 0 := by
    rw [show S = T.filter (fun t => p ∣ t ∧ t ≠ p ∧ t ≠ p ^ 2) from rfl,
      sum_filter]
    apply sum_congr rfl
    intro t _
    by_cases ht : p ∣ t ∧ t ≠ p ∧ t ≠ p ^ 2
    · rw [if_pos ht, if_pos ht.1, if_pos ht]
    · rw [if_neg ht, if_neg ht]
  rw [hsum] at h
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have he : Real.log p / ((p : ℝ) - 1) - Real.log p / p - Real.log p / (p : ℝ) ^ 2 =
      Real.log p / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
    field_simp [hpR, hp1]
    ring
  linarith only [h, he]

/-- The signed prime correction in one upward arithmetic row. -/
def primeSquareFlipRow (p n y : ℕ) : ℝ :=
  ∑ t ∈ Icc 1 y, (1 - finiteFlip {p} t) * Λ t / (t : ℝ) *
    (primeSquareTrial p n * primeSquareTrial p (t * n))

private theorem primeSquareFlip_term_le {p : ℕ} (hp : p.Prime) (n t : ℕ) :
    (1 - finiteFlip {p} t) * Λ t / (t : ℝ) *
        (primeSquareTrial p n * primeSquareTrial p (t * n)) ≤
      (if t = p then 2 * Real.log p / p *
        (primeSquareTrial p n * primeSquareTrial p (p * n)) else 0) +
      2 * (if p ∣ t ∧ t ≠ p ∧ t ≠ p ^ 2 then Λ t / (t : ℝ) else 0) := by
  by_cases htp : t = p
  · subst t
    have hflip : finiteFlip {p} p = -1 := by
      simp only [finiteFlip, prod_singleton, hp.factorization_self, pow_one]
    simp only [hflip, if_pos rfl, ne_eq, not_true_eq_false, false_and,
      and_false, if_false, mul_zero, add_zero, vonMangoldt_apply_prime hp]
    ring_nf
  · rw [if_neg htp, zero_add]
    by_cases ht2 : t = p ^ 2
    · subst t
      have hflip : finiteFlip {p} (p ^ 2) = 1 := by
        simp only [finiteFlip, prod_singleton, hp.factorization_pow, Finsupp.single_eq_same]
        norm_num
      simp only [hflip, sub_self, zero_mul, zero_div, ne_eq, not_true_eq_false,
        and_false, if_false, mul_zero, le_refl]
    · by_cases hpt : p ∣ t
      · rw [if_pos ⟨hpt, htp, ht2⟩]
        have hprod : primeSquareTrial p n * primeSquareTrial p (t * n) ≤ 1 := by
          rw [← abs_primeSquareTrial_product p n (t * n)]
          exact le_abs_self _
        have hbound : 0 ≤ 1 - finiteFlip {p} t ∧ 1 - finiteFlip {p} t ≤ 2 := by
          have h : |finiteFlip {p} t| = 1 := by
            simp only [finiteFlip, prod_singleton, abs_pow, abs_neg, abs_one, one_pow]
          have hl := (abs_le.mp (le_of_eq h)).1
          have hu := (abs_le.mp (le_of_eq h)).2
          constructor <;> linarith only [hl, hu]
        have hmass : 0 ≤ Λ t / (t : ℝ) := div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg t)
        calc
          _ = ((1 - finiteFlip {p} t) * (primeSquareTrial p n * primeSquareTrial p (t * n))) *
              (Λ t / (t : ℝ)) := by ring
          _ ≤ 2 * (Λ t / (t : ℝ)) := mul_le_mul_of_nonneg_right
            ((mul_le_mul_of_nonneg_left hprod hbound.1).trans (by simpa using hbound.2)) hmass
      · have hflip : finiteFlip {p} t = 1 :=
          finiteFlip_eq_one_of_coprime (by simpa only [mem_singleton, forall_eq] using hpt)
        simp only [hflip, sub_self, zero_mul, zero_div, hpt, false_and, if_false, le_refl]

/-- The first prime term keeps its sign; all later prime powers have one uniform tail cost. -/
theorem primeSquareFlipRow_le {p : ℕ} (hp : p.Prime) (n y : ℕ) :
    primeSquareFlipRow p n y ≤
      (if p ≤ y then 2 * Real.log p / p *
        (primeSquareTrial p n * primeSquareTrial p (p * n)) else 0) +
      2 * Real.log p / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
  have h := sum_le_sum (s := Icc 1 y) (fun t _ => primeSquareFlip_term_le hp n t)
  rw [sum_add_distrib, ← mul_sum] at h
  simp only [sum_ite_eq', mem_Icc, hp.one_le, true_and] at h
  have htail := mul_le_mul_of_nonneg_left (primePower_tail_after_square hp (Icc 1 y))
    (by norm_num : (0 : ℝ) ≤ 2)
  change primeSquareFlipRow p n y ≤ _ at h
  calc
    _ ≤ _ := h
    _ ≤ _ := by linarith only [htail]

/-- Pole coordinates remove both square-root edge weights exactly. -/
theorem atomicWeilForm_pole_profile_edges (F : ℕ → ℝ) (N : ℕ) :
    atomicWeilForm N (fun n => F n / Real.sqrt n) =
      2 * ∑ m ∈ Icc 1 N, (1 / (m : ℝ)) *
        ∑ t ∈ Icc 1 (N / m), (Λ t / (t : ℝ)) * (F m * F (t * m)) := by
  rw [atomicWeilForm_eq_edges]
  congr 1
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro t ht
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (mem_Icc.mp ht).1
  have hms : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hm0).ne'
  have hts : Real.sqrt (t : ℝ) ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
  rw [Nat.cast_mul, Real.sqrt_mul hm0.le, Nat.mul_comm m t]
  field_simp [hms, hts, hm0.ne', ht0.ne']
  simp only [Real.sq_sqrt hm0.le, Real.sq_sqrt ht0.le]
  ring

/-- The twist changes only the signed upward rows in pole coordinates. -/
theorem primeSquareTrial_prime_correction (p N : ℕ) :
    atomicWeilForm N (fun n => primeSquareTrial p n / Real.sqrt n) -
      atomicWeilForm N (fun n => finiteFlip {p} n * primeSquareTrial p n / Real.sqrt n) =
        2 * ∑ m ∈ Icc 1 N, (1 / (m : ℝ)) * primeSquareFlipRow p m (N / m) := by
  rw [atomicWeilForm_pole_profile_edges, atomicWeilForm_pole_profile_edges,
    ← mul_sub, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro m hm
  rw [← mul_sub, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro t ht
  have hm0 := (mem_Icc.mp hm).1
  have ht0 := (mem_Icc.mp ht).1
  have hmul := (finiteFlip_isSignGauge {p}).mul (Nat.ne_of_gt ht0) (Nat.ne_of_gt hm0)
  rw [hmul]
  linear_combination
    -(finiteFlip {p} t * (Λ t / (t : ℝ)) * primeSquareTrial p m * primeSquareTrial p (t * m)) *
      (finiteFlip_isSignGauge {p}).mul_self (Nat.ne_of_gt hm0)

private theorem filter_prime_upper_row {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (Icc 1 N).filter (fun m => p ≤ N / m) = Icc 1 (N / p) := by
  ext m
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hm, _⟩, h⟩
    refine ⟨hm, (Nat.le_div_iff_mul_le hp).mpr ?_⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).mp h
  · rintro ⟨hm, h⟩
    refine ⟨⟨hm, h.trans (Nat.div_le_self N p)⟩, (Nat.le_div_iff_mul_le hm).mpr ?_⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp h

open SelectiveMultiscaleArithmeticPositivity

/-- A finite-horizon bound retains the cancelling first correlation and every later prime power. -/
theorem primeSquareTrial_prime_correction_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    atomicWeilForm N (fun n => primeSquareTrial p n / Real.sqrt n) -
      atomicWeilForm N (fun n => finiteFlip {p} n * primeSquareTrial p n / Real.sqrt n) ≤
        (4 * Real.log p / p) *
          (-gaugeHarmonicSum (fun _ => 1) (N / p) +
            (2 / (p : ℝ) ^ 2) * gaugeHarmonicSum (fun _ => 1) ((N / p) / p ^ 2)) +
        (4 * Real.log p / ((p : ℝ) ^ 2 * ((p : ℝ) - 1))) *
          gaugeHarmonicSum (fun _ => 1) N := by
  rw [primeSquareTrial_prime_correction]
  have h := mul_le_mul_of_nonneg_left (sum_le_sum (s := Icc 1 N) (fun m _ =>
    mul_le_mul_of_nonneg_left (primeSquareFlipRow_le hp m (N / m))
      (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ)))) (by norm_num : (0 : ℝ) ≤ 2)
  refine h.trans_eq ?_
  simp only [mul_add, sum_add_distrib]
  have hhead : (∑ m ∈ Icc 1 N, (1 / (m : ℝ)) *
      (if p ≤ N / m then 2 * Real.log p / p *
        (primeSquareTrial p m * primeSquareTrial p (p * m)) else 0)) =
      (2 * Real.log p / p) *
        ∑ m ∈ Icc 1 (N / p), primeSquareTrial p m * primeSquareTrial p (p * m) / m := by
    rw [← filter_prime_upper_row hp.pos N, sum_filter, mul_sum]
    apply sum_congr rfl
    intro m _
    split_ifs <;> ring
  rw [hhead, primeSquareTrial_harmonic_correlation hp.pos]
  have htail : (∑ m ∈ Icc 1 N, (1 / (m : ℝ)) *
      (2 * Real.log p / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)))) =
      (2 * Real.log p / ((p : ℝ) ^ 2 * ((p : ℝ) - 1))) *
        gaugeHarmonicSum (fun _ => 1) N := by
    rw [gaugeHarmonicSum, mul_sum]
    exact sum_congr rfl fun m _ => by ring
  rw [htail]
  ring

/-- The exact upper bound furnished by the first prime and the complete tail. -/
def primeSquareFlipBound (p N : ℕ) : ℝ :=
  (4 * Real.log p / p) *
    (-gaugeHarmonicSum (fun _ => 1) (N / p) +
      (2 / (p : ℝ) ^ 2) * gaugeHarmonicSum (fun _ => 1) ((N / p) / p ^ 2)) +
  (4 * Real.log p / ((p : ℝ) ^ 2 * ((p : ℝ) - 1))) * gaugeHarmonicSum (fun _ => 1) N

/-- Fixed decimation preserves the logarithmic harmonic mass. -/
theorem tendsto_gaugeHarmonicSum_natDiv_div_log {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => gaugeHarmonicSum (fun _ => 1) (N / d) / Real.log N)
      atTop (𝓝 1) := by
  refine (_root_.RHTower.tendsto_harmonic_natDiv_div_log hd).congr fun N => ?_
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp only [gaugeHarmonicSum, one_div]

/-- The first prime cancels `4 log p / p`; the remaining cost begins at the prime cube. -/
theorem tendsto_primeSquareFlipBound {p : ℕ} (hp : p.Prime) :
    Tendsto (fun N : ℕ => primeSquareFlipBound p N / Real.log N) atTop
      (𝓝 (-4 * Real.log p / p +
        4 * Real.log p * (2 / (p : ℝ) ^ 3 + 1 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1))))) := by
  have h1 := tendsto_gaugeHarmonicSum_natDiv_div_log hp.pos
  have h2 := tendsto_gaugeHarmonicSum_natDiv_div_log (mul_pos hp.pos (pow_pos hp.pos 2))
  have h0 : Tendsto (fun N : ℕ => gaugeHarmonicSum (fun _ => 1) N / Real.log N)
      atTop (𝓝 1) := by
    simpa only [Nat.div_one] using tendsto_gaugeHarmonicSum_natDiv_div_log (by norm_num : 0 < (1 : ℕ))
  have h := (h1.neg.add (h2.const_mul (2 / (p : ℝ) ^ 2))).const_mul (4 * Real.log p / p)
  have hsum := h.add (h0.const_mul (4 * Real.log p / ((p : ℝ) ^ 2 * ((p : ℝ) - 1))))
  convert hsum using 1
  · funext N
    rw [primeSquareFlipBound, Nat.div_div_eq_div_mul]
    ring
  · congr 1
    ring

end GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.primeSquareFlipRow_le
