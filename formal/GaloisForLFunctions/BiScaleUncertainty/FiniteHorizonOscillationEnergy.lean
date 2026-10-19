import GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonPrimeRecurrence
import GaloisForLFunctions.BiScaleUncertainty.UniversalRamanujanCovarianceAndBiScaleRigidity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Logarithmic oscillations in the native joint energy

A telescoping potential controls additive cost uniformly in window size.
Prime recurrence controls every dilation edge in the same window.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
noncomputable section
set_option autoImplicit false

/-- Logarithmic oscillation on the actual positive integer window. -/
def logOscillation (t a : ℝ) (n : ℕ) : ℝ := Real.cos (t * Real.log n + a)

private theorem log_step_bound (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ Real.log (x + 1) - Real.log x ∧
      Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have hx0 : 0 < x := by linarith
  have hr : 1 ≤ (x + 1) / x := (le_div_iff₀ hx0).mpr (by linarith)
  rw [← Real.log_div (by positivity) (ne_of_gt hx0)]
  refine ⟨Real.log_nonneg hr, ?_⟩
  calc
    Real.log ((x + 1) / x) ≤ (x + 1) / x - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    _ = 1 / x := by field_simp; ring

private theorem oscillation_step_bounds (t a : ℝ) (ht : 0 ≤ t)
    (n : ℕ) (hn : 1 ≤ n) :
    |logOscillation t a (n + 1) - logOscillation t a n| ≤ 2 ∧
      |logOscillation t a (n + 1) - logOscillation t a n| ≤ t / n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd := log_step_bound n hn'
  constructor
  · calc
      |logOscillation t a (n + 1) - logOscillation t a n| ≤
          |logOscillation t a (n + 1)| + |logOscillation t a n| := abs_sub _ _
      _ ≤ 2 := by
        unfold logOscillation
        norm_num only [Nat.cast_add, Nat.cast_one]
        linarith [Real.abs_cos_le_one (t * Real.log (n + 1) + a),
          Real.abs_cos_le_one (t * Real.log n + a)]
  · calc
      |logOscillation t a (n + 1) - logOscillation t a n| ≤
          |(t * Real.log (n + 1) + a) - (t * Real.log n + a)| := by
            simpa only [logOscillation, Nat.cast_add, Nat.cast_one] using
              Real.abs_cos_sub_cos_le (t * Real.log (n + 1) + a) (t * Real.log n + a)
      _ = t * (Real.log (n + 1) - Real.log n) := by
        rw [show (t * Real.log (n + 1) + a) - (t * Real.log n + a) =
          t * (Real.log (n + 1) - Real.log n) by ring, abs_of_nonneg (mul_nonneg ht hd.1)]
      _ ≤ t / n := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hd.2 ht

private theorem square_le_potential_drop (x t u : ℝ) (hx : 1 ≤ x) (ht : 1 ≤ t)
    (hu : |u| ≤ 2) (hu' : |u| ≤ t / x) :
    u ^ 2 ≤ 24 * t ^ 2 / (x + t) - 24 * t ^ 2 / (x + 1 + t) := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < t := by linarith
  have hu2 : u ^ 2 ≤ 4 := by
    have h := (sq_le_sq₀ (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 2)).mpr hu
    norm_num only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] at h
    exact h
  have hu2x : u ^ 2 * x ^ 2 ≤ t ^ 2 := by
    have h := (le_div_iff₀ hx0).mp hu'
    have hsq := (sq_le_sq₀ (mul_nonneg (abs_nonneg u) hx0.le) ht0.le).mpr h
    simpa only [mul_pow, sq_abs] using hsq
  have hden : 0 < (x + t) * (x + 1 + t) := by positivity
  have hprod : u ^ 2 * ((x + t) * (x + 1 + t)) ≤ 24 * t ^ 2 := by
    rcases le_total x t with hxt | htx
    · have hd : (x + t) * (x + 1 + t) ≤ 6 * t ^ 2 := by
        have hb := mul_le_mul (show x + t ≤ 2 * t by linarith)
          (show x + 1 + t ≤ 3 * t by linarith) (by positivity : 0 ≤ x + 1 + t)
          (by positivity : 0 ≤ 2 * t)
        nlinarith
      calc
        u ^ 2 * ((x + t) * (x + 1 + t)) ≤ 4 * ((x + t) * (x + 1 + t)) :=
          mul_le_mul_of_nonneg_right hu2 hden.le
        _ ≤ 24 * t ^ 2 := by nlinarith
    · have hd : (x + t) * (x + 1 + t) ≤ 6 * x ^ 2 := by
        have hb := mul_le_mul (show x + t ≤ 2 * x by linarith)
          (show x + 1 + t ≤ 3 * x by linarith) (by positivity : 0 ≤ x + 1 + t)
          (by positivity : 0 ≤ 2 * x)
        nlinarith
      calc
        u ^ 2 * ((x + t) * (x + 1 + t)) ≤ u ^ 2 * (6 * x ^ 2) :=
          mul_le_mul_of_nonneg_left hd (sq_nonneg _)
        _ ≤ 24 * t ^ 2 := by nlinarith
  calc
    u ^ 2 ≤ 24 * t ^ 2 / ((x + t) * (x + 1 + t)) := (le_div_iff₀ hden).mpr hprod
    _ = 24 * t ^ 2 / (x + t) - 24 * t ^ 2 / (x + 1 + t) := by
      field_simp
      ring

/-- The additive cost is controlled by frequency, uniformly in window size. -/
theorem logOscillation_additiveStepEnergy (N : ℕ) (t a : ℝ) (ht : 1 ≤ t) :
    additiveStepEnergy N (logOscillation t a) ≤ 24 * t := by
  by_cases hN : 1 ≤ N
  · have hs : additiveStepEnergy N (logOscillation t a) ≤
        ∑ n ∈ Ico 1 N, (24 * t ^ 2 / (n + t) - 24 * t ^ 2 / ((n : ℝ) + 1 + t)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 := (mem_Ico.mp hn).1
      have hb := oscillation_step_bounds t a (by linarith) n hn1
      exact square_le_potential_drop n t _ (by exact_mod_cast hn1) ht hb.1 hb.2
    have he : (∑ n ∈ Ico 1 N, (24 * t ^ 2 / (n + t) - 24 * t ^ 2 / ((n : ℝ) + 1 + t))) =
        24 * t ^ 2 / (1 + t) - 24 * t ^ 2 / (N + t) := by
      have h := Finset.sum_Ico_sub (fun n : ℕ => -(24 * t ^ 2 / (n + t))) hN
      simpa only [Nat.cast_add, Nat.cast_one, neg_sub_neg] using h
    rw [he] at hs
    have hfirst : 24 * t ^ 2 / (1 + t) ≤ 24 * t := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1 + t)).mpr
      nlinarith
    have hlast : 0 ≤ 24 * t ^ 2 / (N + t) := by positivity
    linarith
  · have hNz : N = 0 := by omega
    subst N
    simp only [additiveStepEnergy, Ico_eq_empty_of_le (by omega : 0 ≤ 1), sum_empty]
    positivity

private theorem logOscillation_dilation_bound (t a ε : ℝ) (k n : ℕ)
    (hk : 0 < k) (hn : 0 < n) (m : ℤ)
    (hphase : |t * Real.log k - m * (2 * Real.pi)| ≤ ε) :
    |logOscillation t a (k * n) - logOscillation t a n| ≤ ε := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc := Real.abs_cos_sub_cos_le (t * Real.log (k * n : ℕ) + a)
    (t * Real.log n + a + m * (2 * Real.pi))
  rw [Real.cos_add_int_mul_two_pi] at hc
  calc
    |logOscillation t a (k * n) - logOscillation t a n| ≤
        |(t * Real.log (k * n : ℕ) + a) - (t * Real.log n + a + m * (2 * Real.pi))| := hc
    _ = |t * Real.log k - m * (2 * Real.pi)| := by
      rw [Nat.cast_mul, Real.log_mul hk0 hn0]
      congr 1
      ring
    _ ≤ ε := hphase

/-- A common phase tolerance controls every actual dilation edge in the window. -/
theorem logOscillation_multiplicativeScaleEnergy (K N : ℕ) (t a ε : ℝ) (hε : 0 ≤ ε)
    (hphase : ∀ k : ℕ, 2 ≤ k → k ≤ K → ∃ m : ℤ,
      |t * Real.log k - m * (2 * Real.pi)| ≤ ε) :
    multiplicativeScaleEnergy K N (logOscillation t a) ≤ (K : ℝ) * N * ε ^ 2 := by
  have hs : multiplicativeScaleEnergy K N (logOscillation t a) ≤
      ∑ k ∈ Icc 2 K, (N : ℝ) * ε ^ 2 := by
    apply Finset.sum_le_sum
    intro k hk
    obtain ⟨hk2, hkK⟩ := mem_Icc.mp hk
    obtain ⟨m, hm⟩ := hphase k hk2 hkK
    calc
      (∑ n ∈ Icc 1 (N / k), (logOscillation t a (k * n) - logOscillation t a n) ^ 2) ≤
          ∑ _n ∈ Icc 1 (N / k), ε ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hb := logOscillation_dilation_bound t a ε k n (by omega)
          (by have := (mem_Icc.mp hn).1; omega) m hm
        have hsq := (sq_le_sq₀ (abs_nonneg _) hε).mpr hb
        simpa only [sq_abs] using hsq
      _ = (N / k : ℕ) * ε ^ 2 := by simp
      _ ≤ (N : ℝ) * ε ^ 2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_le_self N k) (sq_nonneg _)
  have hcard : ((Icc 2 K).card : ℝ) ≤ K := by
    exact_mod_cast (show (Icc 2 K).card ≤ K by simp only [Nat.card_Icc]; omega)
  calc
    multiplicativeScaleEnergy K N (logOscillation t a) ≤
        ∑ k ∈ Icc 2 K, (N : ℝ) * ε ^ 2 := hs
    _ = ((Icc 2 K).card : ℝ) * ((N : ℝ) * ε ^ 2) := by simp
    _ ≤ (K : ℝ) * N * ε ^ 2 := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ (N : ℝ) * ε ^ 2)

end
end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon

namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
open SieveMoments
noncomputable section
set_option autoImplicit false

/-- One prime-count-controlled clock makes every finite-window dilation inexpensive.
The additive estimate is uniform in both the window and the phase offset. -/
theorem exists_finite_horizon_low_energy (K Q : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ (Q + 1) ^ (oddPrimeModes (2 * K)).card ∧
      ∀ (N : ℕ) (a : ℝ),
        biScaleJointEnergy K N (logOscillation (2 * Real.pi * q / Real.log 2) a) ≤
          (24 * (2 * Real.pi / Real.log 2)) * ((Q + 1 : ℕ) : ℝ) ^ (oddPrimeModes (2 * K)).card +
            (K : ℝ) * N * (2 * Real.pi * K / (Q + 1)) ^ 2 := by
  obtain ⟨q, hq, hqQ, happ⟩ := exists_prime_horizon_recurrence K Q
  refine ⟨q, hq, hqQ, ?_⟩
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have ht : 1 ≤ 2 * Real.pi * q / Real.log 2 := by
    apply (le_div_iff₀ hlog).mpr
    nlinarith [Real.pi_gt_three]
  have he : 0 ≤ 2 * Real.pi * K / (Q + 1 : ℝ) := by positivity
  have hphase : ∀ k : ℕ, 2 ≤ k → k ≤ K → ∃ m : ℤ,
      |(2 * Real.pi * q / Real.log 2) * Real.log k - m * (2 * Real.pi)| ≤
        2 * Real.pi * K / (Q + 1 : ℝ) := by
    intro k hk hkK
    obtain ⟨m, hm⟩ := happ k hk hkK
    refine ⟨m, ?_⟩
    calc
      |(2 * Real.pi * q / Real.log 2) * Real.log k - m * (2 * Real.pi)| =
          (2 * Real.pi) * |(q : ℝ) * Real.log k / Real.log 2 - m| := by
        rw [show (2 * Real.pi * q / Real.log 2) * Real.log k - m * (2 * Real.pi) =
          (2 * Real.pi) * ((q : ℝ) * Real.log k / Real.log 2 - m) by ring,
          abs_mul, abs_of_nonneg (show 0 ≤ 2 * Real.pi by positivity)]
      _ ≤ (2 * Real.pi) * ((K : ℝ) / (Q + 1)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = 2 * Real.pi * K / (Q + 1 : ℝ) := by ring
  intro N a
  have hadd := logOscillation_additiveStepEnergy N (2 * Real.pi * q / Real.log 2) a ht
  have hdil := logOscillation_multiplicativeScaleEnergy K N
    (2 * Real.pi * q / Real.log 2) a (2 * Real.pi * K / (Q + 1)) he hphase
  have hqQ' : (q : ℝ) ≤ ((Q + 1 : ℕ) : ℝ) ^ (oddPrimeModes (2 * K)).card := by
    exact_mod_cast hqQ
  have hfreq : 24 * (2 * Real.pi * q / Real.log 2) ≤
      (24 * (2 * Real.pi / Real.log 2)) * ((Q + 1 : ℕ) : ℝ) ^ (oddPrimeModes (2 * K)).card := by
    calc
      24 * (2 * Real.pi * q / Real.log 2) = (24 * (2 * Real.pi / Real.log 2)) * q := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hqQ'
        (show 0 ≤ 24 * (2 * Real.pi / Real.log 2) by positivity)
  exact (add_le_add hadd hdil).trans (add_le_add hfreq le_rfl)

end
end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
