import GaloisForLFunctions.BezoutValuationIncidence.VaughanPacketsHaveAnExactResidualEnergyDensity
import GaloisForLFunctions.BezoutValuationIncidence.UniformTruncatedMobiusReceiversHaveZeroTrivialDensity

/-! Smooth-power pronic energy has a bounded integral error. Finite weighted
Cauchy–Schwarz then controls the three error pairings around a rank-one term. -/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem smooth_power_energy_eq_sum (ε : ℝ) (T : ℕ) :
    pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T ^ 2 =
      ∑ n ∈ Icc 1 T, (n : ℝ) ^ (1 - 2 * ε) / ((n : ℝ) + 1) := by
  rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
  apply sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hpow : ((n : ℝ) ^ (1 - ε)) ^ 2 = (n : ℝ) * (n : ℝ) ^ (1 - 2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le,
      show (1 - ε) * ((2 : ℕ) : ℝ) = 1 + (1 - 2 * ε) by push_cast; ring,
      Real.rpow_add hn0, Real.rpow_one]
  rw [hpow]
  field_simp

/-- The smooth-power pronic energy differs from its leading integral by a bounded amount. -/
theorem exists_smooth_power_pronicEnergy_bounded_error
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ T : ℕ, 1 ≤ T →
      |pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T ^ 2 -
        (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)| ≤ D := by
  let β : ℝ := 1 - 2 * ε
  have hβ0 : 0 < β := by dsimp only [β]; linarith only [hε2]
  have hβ1 : β < 1 := by dsimp only [β]; linarith only [hε]
  let D : ℝ := ‖riemannZeta (1 - (β : ℂ))‖ + partialSumRate (1 - (β : ℂ)) + (1 + 1 / (1 - β))
  have herr (T : ℕ) (hT : 1 ≤ T) :
      |pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T ^ 2 - (T : ℝ) ^ β / β| ≤ D := by
    rw [smooth_power_energy_eq_sum]
    have h := norm_sum_cpow_div_succ_sub_le (β := (β : ℂ)) hβ0 hβ1 hT
    have he (n : ℕ) : ((n : ℝ) : ℂ) ^ (β : ℂ) = (((n : ℝ) ^ β : ℝ) : ℂ) :=
      (Complex.ofReal_cpow (Nat.cast_nonneg n) β).symm
    simpa only [he, ← Complex.ofReal_div, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, D] using h
  exact ⟨D, (abs_nonneg _).trans (herr 1 le_rfl), herr⟩

/-- A common power majorant bounds the smooth pronic norm at every positive horizon. -/
theorem pronicNorm_smooth_power_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {T : ℕ} (hT : 1 ≤ T) :
    pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T ≤
      Real.sqrt (1 + 1 / (1 - 2 * ε)) * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) := by
  have hβ : 0 < 1 - 2 * ε := by linarith only [hε2]
  have hpow1 : 1 ≤ (T : ℝ) ^ (1 - 2 * ε) :=
    Real.one_le_rpow (by exact_mod_cast hT) hβ.le
  have hsum : (∑ n ∈ Icc 1 T,
      ((n : ℝ) ^ (1 - ε)) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
        (1 + 1 / (1 - 2 * ε)) * (T : ℝ) ^ (1 - 2 * ε) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * ε)) := by
        apply sum_le_sum
        intro n hn
        simpa only [one_pow, one_mul] using cell_le_of_abs_le_rpow (ε := ε)
          (K := 1) (A := (n : ℝ) ^ (1 - ε)) (mem_Icc.mp hn).1
            (by rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]; simp only [one_mul, le_refl])
      _ ≤ 1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) :=
        sum_Icc_rpow_neg_two_mul_le_of_pos hε hε2 T
      _ ≤ _ := (add_le_add hpow1 (le_refl ((T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)))).trans_eq (by ring)
  have h := Real.sqrt_le_sqrt hsum
  rw [Real.sqrt_mul (by positivity : 0 ≤ 1 + 1 / (1 - 2 * ε))] at h
  exact h

private theorem abs_pronic_sum_mul_le (T : ℕ) (a b : ℕ → ℝ) :
    |∑ n ∈ Icc 1 T, a n * b n / ((n : ℝ) * ((n : ℝ) + 1))| ≤
      pronicNorm a T * pronicNorm b T := by
  -- Absorb the positive cell weights into both factors before finite Cauchy–Schwarz.
  let w : ℕ → ℝ := fun n => Real.sqrt (1 / ((n : ℝ) * ((n : ℝ) + 1)))
  have hw (n : ℕ) : w n ^ 2 = 1 / ((n : ℝ) * ((n : ℝ) + 1)) :=
    Real.sq_sqrt (by positivity)
  have hpair : (∑ n ∈ Icc 1 T, (a n * w n) * (b n * w n)) =
      ∑ n ∈ Icc 1 T, a n * b n / ((n : ℝ) * ((n : ℝ) + 1)) := by
    apply sum_congr rfl
    intro n _
    rw [show (a n * w n) * (b n * w n) = a n * b n * w n ^ 2 by ring,
      hw, mul_one_div]
  have hnorm (f : ℕ → ℝ) :
      (∑ n ∈ Icc 1 T, (f n * w n) ^ 2) = pronicNorm f T ^ 2 := by
    rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
    exact sum_congr rfl fun n _ => by rw [mul_pow, hw, mul_one_div]
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 T) (fun n => a n * w n)
    (fun n => b n * w n)
  rw [hpair, hnorm, hnorm, ← mul_pow] at hcs
  exact abs_le.mpr (abs_le_of_sq_le_sq' hcs
    (mul_nonneg (pronicNorm_nonneg _ _) (pronicNorm_nonneg _ _)))

/-- A common rank-one component leaves only two mixed pairings and the residual pairing. -/
theorem abs_pronicGram_sub_rankOne_le (a b : ℝ) (h r s : ℕ → ℝ) (T : ℕ) :
    |(∑ n ∈ Icc 1 T, (a * h n + r n) * (b * h n + s n) /
        ((n : ℝ) * ((n : ℝ) + 1))) - a * b * pronicNorm h T ^ 2| ≤
      |a| * pronicNorm h T * pronicNorm s T +
        |b| * pronicNorm h T * pronicNorm r T + pronicNorm r T * pronicNorm s T := by
  have heq : (∑ n ∈ Icc 1 T, (a * h n + r n) * (b * h n + s n) /
      ((n : ℝ) * ((n : ℝ) + 1))) - a * b * pronicNorm h T ^ 2 =
        a * (∑ n ∈ Icc 1 T, h n * s n / ((n : ℝ) * ((n : ℝ) + 1))) +
          b * (∑ n ∈ Icc 1 T, h n * r n / ((n : ℝ) * ((n : ℝ) + 1))) +
            ∑ n ∈ Icc 1 T, r n * s n / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [heq]
  calc
    _ ≤ |a * (∑ n ∈ Icc 1 T, h n * s n / ((n : ℝ) * ((n : ℝ) + 1)))| +
        |b * (∑ n ∈ Icc 1 T, h n * r n / ((n : ℝ) * ((n : ℝ) + 1)))| +
          |∑ n ∈ Icc 1 T, r n * s n / ((n : ℝ) * ((n : ℝ) + 1))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [abs_mul, abs_mul, mul_assoc, mul_assoc]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (abs_pronic_sum_mul_le T h s) (abs_nonneg a))
        (mul_le_mul_of_nonneg_left (abs_pronic_sum_mul_le T h r) (abs_nonneg b)))
          (abs_pronic_sum_mul_le T r s)

#print axioms exists_smooth_power_pronicEnergy_bounded_error
#print axioms pronicNorm_smooth_power_le
#print axioms abs_pronicGram_sub_rankOne_le
end GaloisForLFunctions.BezoutValuationIncidence
