import GaloisForLFunctions.BezoutValuationIncidence.TheEmptyVaughanLegDetectsAFixedStrip
import GaloisForLFunctions.RHTower.PolynomialFockLocalBregman

/-!
Finite Abel inversion transfers reciprocal-tail power gains at every positive
damping to a fixed zero-free strip. The same equivalence holds for the actual
empty-leg energy after translating cutoff and horizon exponents.
-/

open Finset Filter ArithmeticFunction RHTower RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A compact-interval power bound controls the inverse Abel increment at every nonnegative damping. -/
theorem rpow_one_add_increment_le_of_nonneg {ε : ℝ} (hε : 0 ≤ ε)
    {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) + 1) ^ (1 + ε) - (n : ℝ) ^ (1 + ε) ≤
      ((1 + ε) * 2 ^ ε) * (n : ℝ) ^ ε := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := abs_rpow_sub_rpow_le_of_le
    (u := (n : ℝ) + 1) (v := (n : ℝ)) (M := 2 * (n : ℝ))
    (β := 1 + ε) (by positivity) hn0 (by linarith only [hn1])
      (by linarith only [hn0]) (by linarith only [hε])
  rw [show (1 + ε) - 1 = ε by ring, show (n : ℝ) + 1 - n = 1 by ring,
    abs_one, mul_one, Real.mul_rpow (by norm_num) hn0.le, ← mul_assoc] at h
  exact (le_abs_self _).trans h

/-- A fixed power improvement in the signed reciprocal tail transfers back to Mertens sums. -/
theorem abs_sum_moebiusReal_le_of_reciprocalTail_bound_all_dampings {ε η K : ℝ}
    (hε : 0 ≤ ε) (hη : 0 < η) (hη1 : η < 1) (hK : 0 ≤ K)
    (hF : ∀ n : ℕ, 1 ≤ n → |pmPronicVaughanReciprocalTail ε n| ≤
      K * (n : ℝ) ^ (-ε - η)) {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, moebiusReal n| ≤
      (|pmPronicVaughanReciprocalTail ε 0| + 2 ^ (1 + ε) * K +
        ((1 + ε) * 2 ^ ε) * K * (1 / (1 - η) + 1)) * (N : ℝ) ^ (1 - η) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow1 : 1 ≤ (N : ℝ) ^ (1 - η) := Real.one_le_rpow hN1 (by linarith only [hη1])
  have hboundary : |((N : ℝ) + 1) ^ (1 + ε) * pmPronicVaughanReciprocalTail ε N| ≤
      2 ^ (1 + ε) * K * (N : ℝ) ^ (1 - η) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    calc
      _ ≤ (2 * (N : ℝ)) ^ (1 + ε) * (K * (N : ℝ) ^ (-ε - η)) := by
        apply mul_le_mul
        · exact Real.rpow_le_rpow (by positivity) (by linarith only [hN1]) (by positivity)
        · exact hF N hN
        · exact abs_nonneg _
        · exact Real.rpow_nonneg (by positivity) _
      _ = 2 ^ (1 + ε) * K * (N : ℝ) ^ (1 - η) := by
        rw [Real.mul_rpow (by norm_num) hN0.le]
        rw [show 2 ^ (1 + ε) * (N : ℝ) ^ (1 + ε) * (K * (N : ℝ) ^ (-ε - η)) =
          2 ^ (1 + ε) * K * ((N : ℝ) ^ (1 + ε) * (N : ℝ) ^ (-ε - η)) by ring,
          ← Real.rpow_add hN0, show (1 + ε) + (-ε - η) = 1 - η by ring]
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      |(((n : ℝ) + 1) ^ (1 + ε) - (n : ℝ) ^ (1 + ε)) *
        pmPronicVaughanReciprocalTail ε n| ≤ ((1 + ε) * 2 ^ ε) * K * (n : ℝ) ^ (-η) := by
    have hn1 := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hinc : 0 ≤ ((n : ℝ) + 1) ^ (1 + ε) - (n : ℝ) ^ (1 + ε) :=
      sub_nonneg.mpr (Real.rpow_le_rpow hn0.le (by linarith) (by positivity))
    rw [abs_mul, abs_of_nonneg hinc]
    calc
      _ ≤ (((1 + ε) * 2 ^ ε) * (n : ℝ) ^ ε) * (K * (n : ℝ) ^ (-ε - η)) :=
        mul_le_mul (rpow_one_add_increment_le_of_nonneg hε hn1) (hF n hn1)
          (abs_nonneg _) (by positivity)
      _ = ((1 + ε) * 2 ^ ε) * K * (n : ℝ) ^ (-η) := by
        rw [show (((1 + ε) * 2 ^ ε) * (n : ℝ) ^ ε) * (K * (n : ℝ) ^ (-ε - η)) =
          ((1 + ε) * 2 ^ ε) * K * ((n : ℝ) ^ ε * (n : ℝ) ^ (-ε - η)) by ring,
          ← Real.rpow_add hn0, show ε + (-ε - η) = -η by ring]
  have hsum : |∑ n ∈ Icc 1 N,
      (((n : ℝ) + 1) ^ (1 + ε) - (n : ℝ) ^ (1 + ε)) *
        pmPronicVaughanReciprocalTail ε n| ≤
      ((1 + ε) * 2 ^ ε) * K * (1 / (1 - η) + 1) * (N : ℝ) ^ (1 - η) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, ((1 + ε) * 2 ^ ε) * K * (n : ℝ) ^ (-η) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
      _ = ((1 + ε) * 2 ^ ε) * K * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-η) := by rw [mul_sum]
      _ ≤ ((1 + ε) * 2 ^ ε) * K * ((N : ℝ) ^ (1 - η) / (1 - η) + 1) :=
        mul_le_mul_of_nonneg_left (sum_rpow_neg_subcritical_le hη hη1 N) (by positivity)
      _ ≤ ((1 + ε) * 2 ^ ε) * K * ((N : ℝ) ^ (1 - η) / (1 - η) + (N : ℝ) ^ (1 - η)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hpow1) (by positivity)
      _ = _ := by ring
  rw [sum_moebiusReal_eq_reciprocalTail_abel]
  calc
    _ ≤ |pmPronicVaughanReciprocalTail ε 0| +
        |((N : ℝ) + 1) ^ (1 + ε) * pmPronicVaughanReciprocalTail ε N| +
          |∑ n ∈ Icc 1 N, (((n : ℝ) + 1) ^ (1 + ε) - (n : ℝ) ^ (1 + ε)) *
            pmPronicVaughanReciprocalTail ε n| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ |pmPronicVaughanReciprocalTail ε 0| * (N : ℝ) ^ (1 - η) +
        2 ^ (1 + ε) * K * (N : ℝ) ^ (1 - η) +
          ((1 + ε) * 2 ^ ε) * K * (1 / (1 - η) + 1) * (N : ℝ) ^ (1 - η) :=
      add_le_add (add_le_add (le_mul_of_one_le_right (abs_nonneg _) hpow1) hboundary) hsum
    _ = _ := by ring

/-- Any reciprocal-tail power improvement would give a fixed zero-free strip. -/
theorem zetaZeroAbscissa_lt_one_of_vaughan_reciprocalTail_power_all_dampings {ε η K : ℝ}
    (hε : 0 ≤ ε) (hη : 0 < η) (hη1 : η < 1) (hK : 0 ≤ K)
    (hF : ∀ n : ℕ, 1 ≤ n → |pmPronicVaughanReciprocalTail ε n| ≤
      K * (n : ℝ) ^ (-ε - η)) : zetaZeroAbscissa < 1 := by
  apply zetaZeroAbscissa_lt_one_iff_moebius_rate.mpr
  refine ⟨|pmPronicVaughanReciprocalTail ε 0| + 2 ^ (1 + ε) * K +
    ((1 + ε) * 2 ^ ε) * K * (1 / (1 - η) + 1), 1 - η, ?_,
    by linarith only [hη1], by linarith only [hη], ?_⟩
  · have : 0 < 1 - η := by linarith only [hη1]
    positivity
  · exact fun n hn => abs_sum_moebiusReal_le_of_reciprocalTail_bound_all_dampings hε hη hη1 hK hF hn

/-- A signed reciprocal-tail power gain is exactly a fixed zero-free strip. -/
theorem zetaZeroAbscissa_lt_one_iff_vaughan_reciprocalTail_power_all_dampings {ε : ℝ}
    (hε : 0 < ε) :
    zetaZeroAbscissa < 1 ↔ ∃ η K : ℝ, 0 < η ∧ η < 1 ∧ 0 ≤ K ∧
      ∀ n : ℕ, 1 ≤ n → |pmPronicVaughanReciprocalTail ε n| ≤
        K * (n : ℝ) ^ (-ε - η) := by
  constructor
  · intro hΘ
    obtain ⟨C, β, hC, hβ0, hβ1, hM⟩ := zetaZeroAbscissa_lt_one_iff_moebius_rate.mp hΘ
    refine ⟨(1 - β) / 2, (2 + 1 / ε) * C,
      by linarith only [hβ1], by linarith only [hβ0], by positivity, fun n hn => ?_⟩
    refine (abs_pmPronicVaughanReciprocalTail_le_of_mertens_rate hε hβ1 hC hM hn).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
        (by linarith only [hβ1])) (by positivity)
  · rintro ⟨η, K, hη, hη1, hK, hF⟩
    exact zetaZeroAbscissa_lt_one_of_vaughan_reciprocalTail_power_all_dampings
      hε.le hη hη1 hK hF

/-- The centered empty-leg power-saving problem is exactly the fixed-strip problem. -/
theorem zetaZeroAbscissa_lt_one_iff_vaughan_square_energy_power_all_dampings {ε : ℝ}
    (hε : 0 < ε) :
    zetaZeroAbscissa < 1 ↔ ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ N : ℕ, 1 ≤ N →
        pmPronicVaughanCentredGram ε N N (N ^ 2) 3 3 / ((N ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) ≤
          C * (N : ℝ) ^ (-δ) := by
  constructor
  · intro hΘ
    obtain ⟨η, K, hη, _, hK, hF⟩ := (zetaZeroAbscissa_lt_one_iff_vaughan_reciprocalTail_power_all_dampings hε).mp hΘ
    exact ⟨4 * η, pmPronicPowerDensity ε ^ 2 * K ^ 4, by positivity, by positivity,
      fun N hN => pmPronicVaughanCentredGram_square_power_bound_of_tail hε hK hF hN⟩
  · rintro ⟨δ, C, hδ, hC, hE⟩
    apply (zetaZeroAbscissa_lt_one_iff_vaughan_reciprocalTail_power_all_dampings hε).mpr
    refine ⟨min (δ / 4) (1 / 2), Real.sqrt (Real.sqrt (2 * C / pmPronicPowerDensity ε ^ 2)),
      lt_min (by positivity) (by norm_num), (min_le_right _ _).trans_lt (by norm_num),
      Real.sqrt_nonneg _, fun N hN => ?_⟩
    refine (abs_pmPronicVaughanReciprocalTail_le_of_square_energy_power hε hC hE hN).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN) (by linarith only [min_le_left (δ / 4) (1 / 2)])) (Real.sqrt_nonneg _)
#print axioms rpow_one_add_increment_le_of_nonneg
#print axioms abs_sum_moebiusReal_le_of_reciprocalTail_bound_all_dampings
#print axioms zetaZeroAbscissa_lt_one_of_vaughan_reciprocalTail_power_all_dampings
#print axioms zetaZeroAbscissa_lt_one_iff_vaughan_reciprocalTail_power_all_dampings
#print axioms zetaZeroAbscissa_lt_one_iff_vaughan_square_energy_power_all_dampings
end GaloisForLFunctions.BezoutValuationIncidence
