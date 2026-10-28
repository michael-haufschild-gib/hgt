import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PrimePowerMangoldtReindex
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanModesAreValuationSteps
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheDifferentOfATorsionOrbit

/-!
# Completed prime rows of valuation steps

Subtracting the constant profile from the local tower equation isolates the
upward geometric correction and the downward divisor correction. Their sum is
the negative torsion-adjunction energy of the conductor.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction ArithmeticIntersectionTheory BezoutValuationIncidence

theorem abs_valuationStep_le_one {p : ℕ} (hp : p.Prime) (k v : ℕ) :
    |valuationStep p k v| ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpd : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith only [hp2]
  unfold valuationStep
  split_ifs
  · norm_num
  · rw [abs_neg, abs_div, abs_one, abs_of_nonneg (zero_le_one.trans hpd)]
    exact (one_div_le_one_div_of_le zero_lt_one hpd).trans_eq (by norm_num)
  · norm_num

theorem summable_valuationStep_geometric_tail {p : ℕ} (hp : p.Prime) (k v : ℕ) :
    Summable (fun j : ℕ => valuationStep p k (v + 1 + j) / (p : ℝ) ^ (j + 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine Summable.of_norm_bounded (tsum_inv_pow_succ hp1).summable fun j => ?_
  rw [Real.norm_eq_abs, abs_div,
    abs_of_nonneg (show 0 ≤ (p : ℝ) ^ (j + 1) from pow_nonneg (Nat.cast_nonneg p) _)]
  exact div_le_div_of_nonneg_right (abs_valuationStep_le_one hp k _) (by positivity)

/-- The upward step difference is the geometric step tail minus its constant mass. -/
theorem hasSum_valuationStep_up_difference {p : ℕ} (hp : p.Prime) (k v : ℕ) :
    HasSum (fun j : ℕ => (valuationStep p k (v + 1 + j) - valuationStep p k v) /
        (p : ℝ) ^ (j + 1))
      ((∑' j : ℕ, valuationStep p k (v + 1 + j) / (p : ℝ) ^ (j + 1)) -
        valuationStep p k v / ((p : ℝ) - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h := (summable_valuationStep_geometric_tail hp k v).hasSum.sub
    ((tsum_inv_pow_succ hp1).mul_left (valuationStep p k v))
  have h' : HasSum (fun j : ℕ =>
      (valuationStep p k (v + 1 + j) - valuationStep p k v) / (p : ℝ) ^ (j + 1))
      ((∑' j : ℕ, valuationStep p k (v + 1 + j) / (p : ℝ) ^ (j + 1)) -
        valuationStep p k v * (1 / ((p : ℝ) - 1))) := h.congr_fun (fun j => by ring)
  simpa only [mul_one_div] using h'

theorem tsum_valuationStep_up_difference {p : ℕ} (hp : p.Prime) (k v : ℕ) :
    (∑' j : ℕ, (valuationStep p k (v + 1 + j) - valuationStep p k v) /
        (p : ℝ) ^ (j + 1)) =
      (∑' j : ℕ, valuationStep p k (v + 1 + j) / (p : ℝ) ^ (j + 1)) -
        valuationStep p k v / ((p : ℝ) - 1) :=
  (hasSum_valuationStep_up_difference hp k v).tsum_eq

/-- The two completed corrections have precisely the negative local adjunction energy. -/
theorem valuationStep_completed_row {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (v : ℕ) :
    Real.log p *
      ((∑' j : ℕ, (valuationStep p k (v + 1 + j) - valuationStep p k v) /
          (p : ℝ) ^ (j + 1)) +
        ∑ j ∈ range (v + 1), (valuationStep p k j - valuationStep p k v)) =
      -(Real.log (p ^ k : ℕ) + tameDifferent (p ^ k)) * valuationStep p k v := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h := towerOp_step hp1 hk v
  rw [tsum_valuationStep_up_difference hp, tameDifferent_prime_pow hp hk.ne',
    Nat.cast_pow, Real.log_pow]
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  unfold towerGaugeOp localEuler at h
  linear_combination -h

/-- The literal divisor correction of a prime-power Ramanujan mode is the finite
downward part of its valuation generator. -/
theorem ramanujan_primePower_down_correction {p k n : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hn : 0 < n) :
    (∑ d ∈ n.divisors,
      (ramanujanLagCoefficient (p ^ k) (n / d) - ramanujanLagCoefficient (p ^ k) n) * Λ d) =
      (((p ^ k).totient : ℝ) * Real.log p) *
        ∑ j ∈ range (n.factorization p + 1),
          (valuationStep p k j - valuationStep p k (n.factorization p)) := by
  have hfilter : ∀ d ∈ n.divisors,
      (ramanujanLagCoefficient (p ^ k) (n / d) - ramanujanLagCoefficient (p ^ k) n) * Λ d =
        if p ∣ d then
          (ramanujanLagCoefficient (p ^ k) (n / d) - ramanujanLagCoefficient (p ^ k) n) * Λ d
        else 0 := by
    intro d hd
    by_cases hpd : p ∣ d
    · rw [if_pos hpd]
    · have hcop : (p ^ k).Coprime d := (hp.coprime_iff_not_dvd.mpr hpd).pow_left k
      have he := ramanujanCoefficient_mul_lag_of_coprime (n := n / d) hcop
      rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)] at he
      rw [if_neg hpd, he, sub_self, zero_mul]
  rw [sum_congr rfl hfilter, sum_divisors_primePower_mangoldt hp hn.ne']
  have hterm : ∀ j ∈ range (n.factorization p),
      (ramanujanLagCoefficient (p ^ k) (n / p ^ (j + 1)) - ramanujanLagCoefficient (p ^ k) n) *
        Real.log p =
      (((p ^ k).totient : ℝ) * Real.log p) *
        (valuationStep p k (n.factorization p - (j + 1)) -
          valuationStep p k (n.factorization p)) := by
    intro j hj
    have hd : p ^ (j + 1) ∣ n :=
      (hp.pow_dvd_iff_le_factorization hn.ne').mpr (by have := mem_range.mp hj; omega)
    have hq : 0 < n / p ^ (j + 1) :=
      Nat.div_pos (Nat.le_of_dvd hn hd) (pow_pos hp.pos _)
    have hv : (n / p ^ (j + 1)).factorization p = n.factorization p - (j + 1) := by
      have he := congrArg (fun x : ℕ => x.factorization p) (Nat.div_mul_cancel hd)
      simp only [Nat.factorization_mul hq.ne' (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_same] at he
      omega
    rw [ramanujanCoefficient_prime_pow_eq_valuationStep hp hk hq.ne',
      ramanujanCoefficient_prime_pow_eq_valuationStep hp hk hn.ne', hv]
    ring
  rw [sum_congr rfl hterm, ← mul_sum]
  have hreverse : (∑ j ∈ range (n.factorization p),
      (valuationStep p k (n.factorization p - (j + 1)) - valuationStep p k (n.factorization p))) =
      ∑ j ∈ range (n.factorization p),
        (valuationStep p k j - valuationStep p k (n.factorization p)) := by
    calc
      _ = ∑ j ∈ range (n.factorization p),
          (valuationStep p k (n.factorization p - 1 - j) -
            valuationStep p k (n.factorization p)) := by
        exact sum_congr rfl fun j _ => by
          rw [show n.factorization p - (j + 1) = n.factorization p - 1 - j by omega]
      _ = _ := Finset.sum_range_reflect
        (fun j => valuationStep p k j - valuationStep p k (n.factorization p)) _
  rw [hreverse, Finset.sum_range_succ, sub_self, add_zero]

/-- The infinite upward Ramanujan correction is its absolutely convergent geometric row. -/
theorem hasSum_ramanujan_primePower_up_correction {p k n : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hn : 0 < n) :
    HasSum (fun t : ℕ =>
      (ramanujanLagCoefficient (p ^ k) (n * t) - ramanujanLagCoefficient (p ^ k) n) * Λ t /
        (t : ℝ))
      ((((p ^ k).totient : ℝ) * Real.log p) *
        ∑' j : ℕ, (valuationStep p k (n.factorization p + 1 + j) -
          valuationStep p k (n.factorization p)) / (p : ℝ) ^ (j + 1)) := by
  have hseries : HasSum (fun j : ℕ =>
      (ramanujanLagCoefficient (p ^ k) (n * p ^ (j + 1)) - ramanujanLagCoefficient (p ^ k) n) *
        Real.log p / (p : ℝ) ^ (j + 1))
      ((((p ^ k).totient : ℝ) * Real.log p) *
        ∑' j : ℕ, (valuationStep p k (n.factorization p + 1 + j) -
          valuationStep p k (n.factorization p)) / (p : ℝ) ^ (j + 1)) := by
    refine ((hasSum_valuationStep_up_difference hp k (n.factorization p)).summable.hasSum.mul_left
      (((p ^ k).totient : ℝ) * Real.log p)).congr_fun fun j => ?_
    rw [ramanujanCoefficient_prime_pow_eq_valuationStep hp hk
      (mul_ne_zero hn.ne' (pow_ne_zero _ hp.ne_zero)),
      ramanujanCoefficient_prime_pow_eq_valuationStep hp hk hn.ne']
    simp only [Nat.factorization_mul hn.ne' (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same]
    rw [show n.factorization p + (j + 1) = n.factorization p + 1 + j by omega]
    ring
  have h := hasSum_primePower_mangoldt hp
    (fun t => ramanujanLagCoefficient (p ^ k) (n * t) - ramanujanLagCoefficient (p ^ k) n) hseries
  refine h.congr_fun fun t => ?_
  by_cases hpt : p ∣ t
  · rw [if_pos hpt]
  · have hcop : (p ^ k).Coprime t := (hp.coprime_iff_not_dvd.mpr hpt).pow_left k
    rw [if_neg hpt, ramanujanCoefficient_mul_lag_of_coprime hcop, sub_self, zero_mul, zero_div]

/-- The literal completed prime row of a prime-power conductor has its exact
torsion-adjunction energy, including every integer in the row. -/
theorem hasSum_ramanujan_primePower_correction {p k n : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hn : 0 < n) :
    HasSum (fun t : ℕ =>
      (ramanujanLagCoefficient (p ^ k) (n * t) - ramanujanLagCoefficient (p ^ k) n) * Λ t /
        (t : ℝ))
      (-(Real.log (p ^ k : ℕ) + tameDifferent (p ^ k)) * ramanujanLagCoefficient (p ^ k) n -
        ∑ d ∈ n.divisors,
          (ramanujanLagCoefficient (p ^ k) (n / d) - ramanujanLagCoefficient (p ^ k) n) * Λ d) := by
  have h := hasSum_ramanujan_primePower_up_correction hp hk hn
  have he : (((p ^ k).totient : ℝ) * Real.log p) *
      (∑' j : ℕ, (valuationStep p k (n.factorization p + 1 + j) -
        valuationStep p k (n.factorization p)) / (p : ℝ) ^ (j + 1)) =
      -(Real.log (p ^ k : ℕ) + tameDifferent (p ^ k)) * ramanujanLagCoefficient (p ^ k) n -
        ∑ d ∈ n.divisors,
          (ramanujanLagCoefficient (p ^ k) (n / d) - ramanujanLagCoefficient (p ^ k) n) * Λ d := by
    rw [ramanujan_primePower_down_correction hp hk hn,
      ramanujanCoefficient_prime_pow_eq_valuationStep hp hk hn.ne']
    have hrow := valuationStep_completed_row hp hk (n.factorization p)
    linear_combination ((p ^ k).totient : ℝ) * hrow
  rwa [he] at h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
