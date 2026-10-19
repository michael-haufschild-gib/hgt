import GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonOscillationEnergy
import GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonIntegerVariance

/-!
# Explicit finite-horizon coercivity witnesses

At a window fixed by the odd-prime mode count, actual logarithmic oscillations have
macroscopic variance about every center and quantitatively small native joint energy.
All approximation and quadrature premises are discharged in the witness construction.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
open SieveMoments
noncomputable section
set_option autoImplicit false

/-- Unconditional witnesses for polynomial deterioration of finite-horizon coercivity.
The window depends on the existing odd-prime mode count, and every center is tested. -/
theorem exists_prime_count_window_witness (K Q : ℕ) :
    let d := (oddPrimeModes (2 * K)).card
    let N := 1024 * (Q + 1) ^ (d + 2)
    ∃ f : ℕ → ℝ,
      (∀ c : ℝ, (N : ℝ) / 16 ≤ ∑ n ∈ Finset.Icc 1 N, (f n - c) ^ 2) ∧
      biScaleJointEnergy K N f ≤
        (384 + 65536 * (K : ℝ) ^ 3) * ((Q + 1 : ℕ) : ℝ) ^ d := by
  let d := (oddPrimeModes (2 * K)).card
  let N := 1024 * (Q + 1) ^ (d + 2)
  let M := 512 * (Q + 1) ^ (d + 2)
  let R : ℝ := (Q + 1 : ℕ)
  obtain ⟨q, hq, hqQ, henergy⟩ := exists_finite_horizon_low_energy K Q
  let t := 2 * Real.pi * q / Real.log 2
  let a := -(t * Real.log N)
  let f := logOscillation t a
  change ∃ f : ℕ → ℝ, (∀ c : ℝ, (N : ℝ) / 16 ≤ ∑ n ∈ Finset.Icc 1 N, (f n - c) ^ 2) ∧
    biScaleJointEnergy K N f ≤ (384 + 65536 * (K : ℝ) ^ 3) * R ^ d
  refine ⟨f, ?_, ?_⟩
  all_goals
    have hR0 : 0 < R := by dsimp [R]; positivity
    have hR1 : 1 ≤ R := by dsimp [R]; norm_cast; omega
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hloglo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have ht0 : 2 * Real.pi / Real.log 2 ≤ 16 := by
      apply (div_le_iff₀ hlog).mpr
      linarith [Real.pi_lt_four]
    have hNcast : (N : ℝ) = 1024 * R ^ (d + 2) := by
      simp only [N, R, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    have hpow : R ^ d ≤ R ^ (d + 2) := by
      have h := mul_le_mul_of_nonneg_left (show 1 ≤ R ^ 2 by nlinarith)
        (pow_nonneg hR0.le d)
      simpa only [mul_one, pow_add] using h
  · intro c
    have hM : 0 < M := by dsimp [M]; positivity
    have hNM : 2 * M = N := by dsimp [M, N]; ring
    have hMcast : (M : ℝ) = 512 * R ^ (d + 2) := by
      simp only [M, R, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    have ht : 0 < t := by
      dsimp [t]
      exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
        (by exact_mod_cast (show 0 < q by omega))) hlog
    have hres : t * Real.log 2 = (q : ℝ) * (2 * Real.pi) := by
      dsimp [t]
      field_simp
    have hqQ' : (q : ℝ) ≤ R ^ d := by
      dsimp [R, d]
      exact_mod_cast hqQ
    have hfreq : t ≤ 16 * R ^ d := by
      calc
        t = (2 * Real.pi / Real.log 2) * q := by dsimp [t]; ring
        _ ≤ 16 * (q : ℝ) := mul_le_mul_of_nonneg_right ht0 (Nat.cast_nonneg q)
        _ ≤ 16 * R ^ d := mul_le_mul_of_nonneg_left hqQ' (by norm_num)
    have hv := integer_window_variance_lower_bound M hM q t c ht hres
    rw [hNM] at hv
    have hmass : 128 * R ^ (d + 2) ≤ (M : ℝ) * Real.log 2 / 2 := by
      rw [hMcast]
      have h := mul_le_mul_of_nonneg_left hloglo (pow_nonneg hR0.le (d + 2))
      nlinarith
    have hsmall : 2 * t ≤ 32 * R ^ (d + 2) := by linarith
    change (N : ℝ) / 16 ≤ ∑ n ∈ Finset.Icc 1 N, (Real.cos (t * Real.log n + a) - c) ^ 2
    calc
      (N : ℝ) / 16 = 64 * R ^ (d + 2) := by rw [hNcast]; ring
      _ ≤ (M : ℝ) * Real.log 2 / 2 - 2 * t := by
        nlinarith [pow_nonneg hR0.le (d + 2)]
      _ ≤ _ := hv
  · have he : biScaleJointEnergy K N f ≤
      (24 * (2 * Real.pi / Real.log 2)) * R ^ d +
        (K : ℝ) * N * (2 * Real.pi * K / R) ^ 2 := by
      simpa only [f, t, R, d, Nat.cast_add, Nat.cast_one] using henergy N a
    have hdil : (K : ℝ) * N * (2 * Real.pi * K / R) ^ 2 =
        (4096 * Real.pi ^ 2 * (K : ℝ) ^ 3) * R ^ d := by
      rw [hNcast, pow_add]
      field_simp [hR0.ne']
      ring
    have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
    have hcoeff : 4096 * Real.pi ^ 2 * (K : ℝ) ^ 3 ≤ 65536 * (K : ℝ) ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hpi2 (pow_nonneg (Nat.cast_nonneg K) 3)
      nlinarith
    calc
      biScaleJointEnergy K N f ≤
          (24 * (2 * Real.pi / Real.log 2)) * R ^ d +
            (K : ℝ) * N * (2 * Real.pi * K / R) ^ 2 := he
      _ = (24 * (2 * Real.pi / Real.log 2) + 4096 * Real.pi ^ 2 * (K : ℝ) ^ 3) * R ^ d := by
        rw [hdil]
        ring
      _ ≤ (384 + 65536 * (K : ℝ) ^ 3) * R ^ d :=
        mul_le_mul_of_nonneg_right (add_le_add (by linarith) hcoeff) (pow_nonneg hR0.le d)

end
end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
