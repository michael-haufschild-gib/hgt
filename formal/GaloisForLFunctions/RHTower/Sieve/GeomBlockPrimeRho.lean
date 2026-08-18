import GaloisForLFunctions.RHTower.Sieve.PrimeBlockScaledBound
import GaloisForLFunctions.RHTower.Sieve.ScaledEnvelopeEstimate

/-!
# The relative bound on a ladder step's prime polynomial

Assembling the block identification, the scaled Route-T envelope and its relative form gives what
the annulus contribution consumes: the prime polynomial of the `j`-th ladder step is a small
multiple of the step's left endpoint, the multiple being explicit in the relative envelope.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **A ladder step's prime polynomial is a small multiple of the step's left endpoint.** -/
theorem exists_norm_primeBlockPoly_geomBlock_le :
    ∃ A delta Ctot τ₀ : ℝ, 0 < delta ∧ 0 < Ctot ∧ 2 ≤ τ₀ ∧
      ∀ (z₀ z L j : ℕ) (Q η D w R : ℝ), 1 ≤ z₀ → Q = (z₀ : ℝ) → 0 ≤ η → j + 1 ≤ L →
        z = ⌊Q * (1 + η) ^ L⌋₊ → 1 ≤ D → τ₀ ≤ |(-(2 * Real.pi * w))| → 0 ≤ R →
        relScaledEnvelope A delta Ctot D (-(2 * Real.pi * w))
            (max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) ≤ R →
        ‖primeBlockPoly (geomBlock (primesRange z₀ z) Q (1 + η) j) w‖
          ≤ (4 / Real.log 2) * ((1 + η) * R + 7 * Real.exp 9 / Q) * (Q * (1 + η) ^ j) := by
  obtain ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, hbound⟩ := exists_norm_primeBlockPoly_scaled_le
  refine ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, ?_⟩
  intro z₀ z L j Q η D w R hz₀ hQ hη hj hz hD hτ hR0 hRle
  have hQ1 : (1 : ℝ) ≤ Q := by
    rw [hQ]
    exact_mod_cast hz₀
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hpow : (1 : ℝ) ≤ (1 + η) ^ j := one_le_pow₀ hr1
  have hQj : (1 : ℝ) ≤ Q * (1 + η) ^ j := by nlinarith [hQ1, hpow]
  have hQj0 : (0 : ℝ) < Q * (1 + η) ^ j := by linarith
  have hQj1 : (1 : ℝ) ≤ Q * (1 + η) ^ (j + 1) := by
    have : Q * (1 + η) ^ j ≤ Q * (1 + η) ^ (j + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 (by omega)) hQ0.le
    linarith
  set a : ℕ := ⌊Q * (1 + η) ^ j⌋₊ with ha
  set b : ℕ := ⌊Q * (1 + η) ^ (j + 1)⌋₊ with hb
  have ha1 : 1 ≤ a := by
    rw [ha]
    exact Nat.le_floor (by exact_mod_cast hQj)
  have hb1 : 1 ≤ b := by
    rw [hb]
    exact Nat.le_floor (by exact_mod_cast hQj1)
  have hab : a ≤ b := by
    rw [ha, hb]
    refine Nat.floor_le_floor ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 (by omega)) hQ0.le
  have hBiff := mem_geomBlock_primesRange (z₀ := z₀) (z := z) (Q := Q) (η := η) hη hQ hj hz
  have hstep := hbound (geomBlock (primesRange z₀ z) Q (1 + η) j) a b D w ha1 hab hBiff hD hτ
  -- the envelope is the cutoff times its relative size
  have hbR : (0 : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hb1
  have hmaxb : max ((b : ℕ) : ℝ) 1 = ((b : ℕ) : ℝ) := max_eq_left (by exact_mod_cast hb1)
  have hEnv : scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w)) (max ((b : ℕ) : ℝ) 1)
      = max ((b : ℕ) : ℝ) 1
        * relScaledEnvelope A delta Ctot D (-(2 * Real.pi * w)) (max ((b : ℕ) : ℝ) 1) :=
    scaledTwistEnvelope_eq_mul (by rw [hmaxb]; exact hbR)
  have hbQ : ((b : ℕ) : ℝ) ≤ Q * (1 + η) ^ (j + 1) := by
    rw [hb]
    exact Nat.floor_le (by linarith)
  have hmax0 : (0 : ℝ) < max ((b : ℕ) : ℝ) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hEnv0 : (0 : ℝ)
      ≤ scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w)) (max ((b : ℕ) : ℝ) 1) :=
    scaledTwistEnvelope_nonneg (A := A) (delta := delta) (Ctot := Ctot) (D := D)
      (τ := -(2 * Real.pi * w)) hCtot.le (by linarith) (by linarith) (le_max_right _ _)
  have hrel0 : (0 : ℝ)
      ≤ relScaledEnvelope A delta Ctot D (-(2 * Real.pi * w)) (max ((b : ℕ) : ℝ) 1) := by
    rw [hEnv] at hEnv0
    exact nonneg_of_mul_nonneg_right hEnv0 hmax0
  rw [hmaxb] at hrel0 hRle
  have hEnvLe : scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w)) (max ((b : ℕ) : ℝ) 1)
      ≤ Q * (1 + η) ^ (j + 1) * R := by
    rw [hEnv, hmaxb]
    exact mul_le_mul hbQ hRle hrel0 (by linarith)
  have hconst : (7 : ℝ) * Real.exp 9 ≤ 7 * Real.exp 9 / Q * (Q * (1 + η) ^ j) := by
    have hid : 7 * Real.exp 9 / Q * (Q * (1 + η) ^ j) = 7 * Real.exp 9 * (1 + η) ^ j := by
      field_simp
    rw [hid]
    nlinarith [hpow, Real.exp_pos (9 : ℝ)]
  have hexpand : Q * (1 + η) ^ (j + 1) * R = (1 + η) * R * (Q * (1 + η) ^ j) := by
    rw [pow_succ]
    ring
  have hfac : (0 : ℝ) < 4 / Real.log 2 := by
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine hstep.trans ?_
  have hsum : scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w)) (max ((b : ℕ) : ℝ) 1)
      + 7 * Real.exp 9
      ≤ ((1 + η) * R + 7 * Real.exp 9 / Q) * (Q * (1 + η) ^ j) := by
    rw [add_mul]
    rw [hexpand] at hEnvLe
    linarith [hEnvLe, hconst]
  have hlast := mul_le_mul_of_nonneg_left hsum hfac.le
  linarith [hlast]

end

end RHTower.Sieve
