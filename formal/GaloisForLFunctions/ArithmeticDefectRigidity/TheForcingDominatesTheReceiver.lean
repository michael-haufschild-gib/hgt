import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SingleDampingSublinearPairingAndBlockEnergy
import GaloisForLFunctions.BezoutValuationIncidence.AllDampingVinogradovKorobovBandAndInteriorGrowth

/-!
# The forcing scale of the arithmetic receiver

The inversion law writes the centered Möbius receiver as the difference between its positive
forcing and its proper cofactor dilation. The forcing has pronic energy at least a positive
multiple of `T^(1-2ε)`. The actual receiver carries the Vinogradov–Korobov saving relative to
that energy. Thus the forcing and receiver require different normalizations below half damping.

The estimates concern the actual source. No admission or cancellation premise is supplied.
-/

open Finset Filter Topology RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- A positive damping below the absolute-convergence threshold. -/
abbrev SubcriticalDamping := {ε : ℝ // 0 < ε ∧ ε < 1 / 2}

/-- The complete pronic energy of the positive inversion forcing. -/
def forcingEnergy (ε : ℝ) (T : ℕ) : ℝ :=
  pronicNorm T (inversionDefect ε) ^ 2

/-- The coefficient supplied by one dyadic block of the positive zeta tail. -/
def forcingFloor (ε : ℝ) : ℝ :=
  (pmPowerDampedDivisorDensity ε).re ^ 2 * ((2 : ℝ) ^ (-(1 + ε))) ^ 2 / 2

theorem forcingEnergy_nonneg (ε : ℝ) (T : ℕ) : 0 ≤ forcingEnergy ε T :=
  sq_nonneg _

theorem forcingFloor_pos (ε : SubcriticalDamping) : 0 < forcingFloor ε := by
  have hm := RHTower.pmPowerDampedDivisorDensity_re_pos ε.property.1
  unfold forcingFloor
  positivity

/-- The forcing retains the full trivial energy scale, at every horizon. -/
theorem forcingFloor_mul_rpow_le (ε : SubcriticalDamping) (T : ℕ) :
    forcingFloor ε * (T : ℝ) ^ (1 - 2 * (ε : ℝ)) ≤ forcingEnergy ε T := by
  by_cases hT : T = 0
  · subst T
    have ha : 1 - 2 * (ε : ℝ) ≠ 0 := by linarith [ε.property.2]
    simp only [Nat.cast_zero, Real.zero_rpow ha, mul_zero]
    exact forcingEnergy_nonneg ε 0
  have hT0 : (0 : ℝ) < T := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hT)
  have hpower : (T : ℝ) ^ (1 - 2 * (ε : ℝ)) =
      (T : ℝ) * (T : ℝ) ^ (-(2 * (ε : ℝ))) := by
    rw [show 1 - 2 * (ε : ℝ) = -(2 * (ε : ℝ)) + 1 by ring,
      Real.rpow_add_one hT0.ne']
    ring
  have hsum : (T : ℝ) ^ (1 - 2 * (ε : ℝ)) ≤
      ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * (ε : ℝ))) := by
    rw [hpower]
    calc (T : ℝ) * (T : ℝ) ^ (-(2 * (ε : ℝ)))
        = ∑ _n ∈ Icc 1 T, (T : ℝ) ^ (-(2 * (ε : ℝ))) := by simp
      _ ≤ ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * (ε : ℝ))) := by
        refine sum_le_sum fun n hn => ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        exact Real.rpow_le_rpow_of_nonpos hn0
          (by exact_mod_cast (mem_Icc.mp hn).2) (by linarith [ε.property.1])
  have hmajorant : ((2 : ℝ) ^ (-(1 + (ε : ℝ)))) ^ 2 / 2 *
      (T : ℝ) ^ (1 - 2 * (ε : ℝ)) ≤ majorantEnergy ε T := by
    calc _ ≤ ((2 : ℝ) ^ (-(1 + (ε : ℝ)))) ^ 2 / 2 *
          ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * (ε : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ majorantEnergy ε T := by
        rw [majorantEnergy, mul_sum]
        exact sum_le_sum fun n hn => majorantEnergy_cell_le ε.property.1 (mem_Icc.mp hn).1
  rw [forcingEnergy, pronicNorm_inversionDefect_sq_eq ε.property.1]
  have h := mul_le_mul_of_nonneg_left hmajorant
    (sq_nonneg (pmPowerDampedDivisorDensity (ε : ℝ)).re)
  calc forcingFloor ε * (T : ℝ) ^ (1 - 2 * (ε : ℝ))
      = (pmPowerDampedDivisorDensity (ε : ℝ)).re ^ 2 *
        (((2 : ℝ) ^ (-(1 + (ε : ℝ)))) ^ 2 / 2 *
          (T : ℝ) ^ (1 - 2 * (ε : ℝ))) := by unfold forcingFloor; ring
    _ ≤ _ := h

/-- The forcing is nonzero at every positive horizon. -/
theorem forcingEnergy_succ_pos (ε : SubcriticalDamping) (T : ℕ) :
    0 < forcingEnergy ε (T + 1) :=
  lt_of_lt_of_le (mul_pos (forcingFloor_pos ε)
    (Real.rpow_pos_of_pos (by positivity) _)) (forcingFloor_mul_rpow_le ε (T + 1))

/-- The receiver has a signed arithmetic saving relative to the full forcing energy. -/
theorem exists_receiver_le_vk_mul_forcingEnergy (ε : SubcriticalDamping) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop,
      dampedMobiusEnergy ε T ≤
        C * Real.exp (-(vkKappa * vkScale T / 270)) * forcingEnergy ε T := by
  obtain ⟨C, hC, hbound⟩ := eventually_receiver_le_growth_of_pos ε.property.1 ε.property.2
  have hc := forcingFloor_pos ε
  refine ⟨C / forcingFloor ε, div_nonneg hC hc.le, ?_⟩
  filter_upwards [hbound] with T hT
  have hfloor : (T : ℝ) ^ (1 - 2 * (ε : ℝ)) ≤ forcingEnergy ε T / forcingFloor ε := by
    rw [le_div_iff₀ hc]
    simpa only [mul_comm] using forcingFloor_mul_rpow_le ε T
  calc dampedMobiusEnergy ε T
      ≤ C * (T : ℝ) ^ (1 - 2 * (ε : ℝ)) *
          Real.exp (-(vkKappa * vkScale T / 270)) := hT
    _ ≤ C * (forcingEnergy ε T / forcingFloor ε) *
          Real.exp (-(vkKappa * vkScale T / 270)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfloor hC) (Real.exp_pos _).le
    _ = _ := by ring

end GaloisForLFunctions.ArithmeticDefectRigidity
