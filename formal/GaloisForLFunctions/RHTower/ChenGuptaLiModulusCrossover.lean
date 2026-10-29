import GaloisForLFunctions.RHTower.ChenGuptaLiZeroDensityExponents

/-!
# The modulus crossover in the Chen–Gupta–Li density envelope

The two source powers exchange dominance exactly at `q = T^12`.
At conductor one their sum is between one and two copies of the `30/13`
height power. These are statements about the displayed density envelope;
they do not turn a positive density exponent into zero exclusion.
-/

noncomputable section

namespace RHTower

/-- The exact modulus boundary between the two powers in the density estimate. -/
theorem cgl_source_power_crossover {q T δ : ℝ}
    (hq : 0 < q) (hT : 0 < T) (hδ : 0 < δ) :
    q ^ ((7 / 3 : ℝ) * δ) * T ^ (2 * δ) ≤ (q * T) ^ ((30 / 13 : ℝ) * δ) ↔
      q ≤ T ^ (12 : ℕ) := by
  have hqp := Real.rpow_pos_of_pos hq ((7 / 3 : ℝ) * δ)
  have htp := Real.rpow_pos_of_pos hT (2 * δ)
  have hqtp := Real.rpow_pos_of_pos (mul_pos hq hT) ((30 / 13 : ℝ) * δ)
  rw [← Real.log_le_log_iff (mul_pos hqp htp) hqtp,
    Real.log_mul hqp.ne' htp.ne', Real.log_rpow hq, Real.log_rpow hT,
    Real.log_rpow (mul_pos hq hT), Real.log_mul hq.ne' hT.ne', ← sub_nonneg]
  rw [show (30 / 13 : ℝ) * δ * (Real.log q + Real.log T) -
      ((7 / 3 : ℝ) * δ * Real.log q + 2 * δ * Real.log T) =
      (δ / 39) * (12 * Real.log T - Real.log q) by ring,
    mul_nonneg_iff_of_pos_left (by positivity : 0 < δ / 39), sub_nonneg]
  simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log_iff hq (pow_pos hT 12)

/-- Equality of the two powers occurs only on the crossover boundary. -/
theorem cgl_source_power_eq_iff {q T δ : ℝ}
    (hq : 0 < q) (hT : 0 < T) (hδ : 0 < δ) :
    q ^ ((7 / 3 : ℝ) * δ) * T ^ (2 * δ) = (q * T) ^ ((30 / 13 : ℝ) * δ) ↔
      q = T ^ (12 : ℕ) := by
  have hqp := Real.rpow_pos_of_pos hq ((7 / 3 : ℝ) * δ)
  have htp := Real.rpow_pos_of_pos hT (2 * δ)
  have hqtp := Real.rpow_pos_of_pos (mul_pos hq hT) ((30 / 13 : ℝ) * δ)
  rw [← Real.log_injOn_pos.eq_iff (mul_pos hqp htp) hqtp,
    Real.log_mul hqp.ne' htp.ne', Real.log_rpow hq, Real.log_rpow hT,
    Real.log_rpow (mul_pos hq hT), Real.log_mul hq.ne' hT.ne', ← sub_eq_zero]
  rw [show (7 / 3 : ℝ) * δ * Real.log q + 2 * δ * Real.log T -
      (30 / 13 : ℝ) * δ * (Real.log q + Real.log T) =
      (δ / 39) * (Real.log q - 12 * Real.log T) by ring,
    mul_eq_zero, or_iff_right (ne_of_gt (by positivity : 0 < δ / 39)), sub_eq_zero]
  simpa only [Real.log_pow, Nat.cast_ofNat] using
    Real.log_injOn_pos.eq_iff hq (pow_pos hT 12)

/-- Strict dominance is also decided by the same boundary. -/
theorem cgl_source_power_lt_iff {q T δ : ℝ}
    (hq : 0 < q) (hT : 0 < T) (hδ : 0 < δ) :
    q ^ ((7 / 3 : ℝ) * δ) * T ^ (2 * δ) < (q * T) ^ ((30 / 13 : ℝ) * δ) ↔
      q < T ^ (12 : ℕ) := by
  rw [lt_iff_le_and_ne, cgl_source_power_crossover hq hT hδ,
    ne_eq, cgl_source_power_eq_iff hq hT hδ, ← lt_iff_le_and_ne]

/-- The source's literal conductor and height coordinates inherit the exact crossover. -/
theorem cglZeroDensityFirstTerm_le_second_iff
    (σ : CGLZeroDensityExponentPoint) (n T : ℕ) :
    cglZeroDensityFirstTerm σ n T ≤ cglZeroDensitySecondTerm σ n T ↔
      cglZeroDensityModulusScale n ≤ cglZeroDensityHeightScale T ^ (12 : ℕ) := by
  apply cgl_source_power_crossover
  · exact zero_lt_one.trans_le (one_le_cglZeroDensityModulusScale n)
  · exact zero_lt_one.trans_le (one_le_cglZeroDensityHeightScale T)
  · exact sub_pos.mpr σ.lt_one

/-- At conductor one, the larger source power has coefficient `30/13`, not `7/3`. -/
theorem cgl_conductor_one_bounds (σ : CGLZeroDensityExponentPoint) (T : ℕ) :
    let B := cglZeroDensityHeightScale T ^ ((30 / 13 : ℝ) * cglZeroDensityDefect σ)
    1 ≤ B ∧ B ≤ cglZeroDensityFirstTerm σ 0 T + cglZeroDensitySecondTerm σ 0 T ∧
      cglZeroDensityFirstTerm σ 0 T + cglZeroDensitySecondTerm σ 0 T ≤ 2 * B := by
  dsimp only
  have hT := one_le_cglZeroDensityHeightScale T
  have hδ := cglZeroDensityDefect_nonneg σ
  have hp : 0 ≤ cglZeroDensityHeightScale T ^ (2 * cglZeroDensityDefect σ) :=
    Real.rpow_nonneg (zero_le_one.trans hT) _
  have hle : cglZeroDensityHeightScale T ^ (2 * cglZeroDensityDefect σ) ≤
      cglZeroDensityHeightScale T ^ ((30 / 13 : ℝ) * cglZeroDensityDefect σ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith only [hδ])
  have h1 : 1 ≤ cglZeroDensityHeightScale T ^ ((30 / 13 : ℝ) * cglZeroDensityDefect σ) := by
    calc
      1 = cglZeroDensityHeightScale T ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by positivity)
  simp only [cglZeroDensityFirstTerm, cglZeroDensitySecondTerm,
    cglZeroDensityModulusScale, Nat.cast_zero, zero_add, Real.one_rpow, one_mul]
  exact ⟨h1, by linarith only [hp], by linarith only [hle]⟩

/-- A singleton count fits the conductor-one envelope at every literal height. -/
theorem cgl_conductor_one_envelope_permits_singleton
    (σ : CGLZeroDensityExponentPoint) (T : ℕ) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : ℝ) ≤
      cglZeroDensityFirstTerm σ 0 T + cglZeroDensitySecondTerm σ 0 T := by
  refine ⟨1, Nat.one_ne_zero, ?_⟩
  simpa only [Nat.cast_one] using
    (cgl_conductor_one_bounds σ T).1.trans (cgl_conductor_one_bounds σ T).2.1

/-- Exact exponent comparison at the claimed seven-eighths boundary: every
density power remains positive there. -/
theorem density_exponents_at_seven_eighths :
    (30 / 13 : ℝ) * (1 - 7 / 8) = 15 / 52 ∧
    (7 / 3 : ℝ) * (1 - 7 / 8) = 7 / 24 ∧
    (2 : ℝ) * (1 - 7 / 8) = 1 / 4 ∧
    0 < (15 / 52 : ℝ) ∧ 0 < (7 / 24 : ℝ) ∧ 0 < (1 / 4 : ℝ) := by
  norm_num

end RHTower

#print axioms RHTower.cglZeroDensityFirstTerm_le_second_iff
#print axioms RHTower.cgl_source_power_eq_iff
#print axioms RHTower.cgl_conductor_one_bounds
#print axioms RHTower.cgl_conductor_one_envelope_permits_singleton
