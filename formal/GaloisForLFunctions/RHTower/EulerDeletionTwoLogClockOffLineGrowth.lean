import GaloisForLFunctions.RHTower.EulerDeletionTwoLogClockRHEndpoint
import GaloisForLFunctions.RHTower.EulerDeletionDilationPowerGrowth

/-!
# Off-line zeros force growth in the signed two-log-clock quotient

The corpus's source-current power floor is transferred through the exact
physical EDQ carrier and the new whole-source clock localization. Thus an
off-line zero cannot put its growth only into late-clock leakage or the
bounded innovation martingale; it forces power growth in the retained signed
paired-Möbius quotient itself.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology

namespace RHTower.DeletionResidueMartingale

theorem exists_current_bound_by_twoLogClockProjection
    (rho : RiemannGaussian.NontrivialZetaZero) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      |(DeletionMobiusCurrent.sourceCurrent N rho.1).re| ≤
        C * (8 * ‖(historySpace (twoLogClockThreshold N)).starProjection
          (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) +
          24 * (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) + 24) := by
  obtain ⟨C, hC, hcurrent⟩ :=
    DeletionMobiusPrimitive.exists_current_bound_by_primitiveEnergy rho
  refine ⟨C, hC, fun N => ?_⟩
  have hprimitive := DeletionMobiusPrimitive.primitiveEnergy_le_two_modular_norm_sq N
  have hmodular := DeletionSignedResidueCovariance.modular_norm_sq_le_two_energy_add_four N
  rw [DeletionSignedResidueCovariance.energy_eq_predictableDrift_norm_sq] at hmodular
  have hdrift := predictableDrift_energy_le_two_twoLogClockProjection_add_log N
  have hbudget : DeletionMobiusPrimitive.primitiveEnergy N ≤
      8 * ‖(historySpace (twoLogClockThreshold N)).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) +
      24 * (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) + 24 := by
    nlinarith
  exact (hcurrent N).trans (mul_le_mul_of_nonneg_left hbudget hC.le)

/-- An off-line zero forces a positive power-law floor in the exact signed
two-log-clock quotient energy at every sufficiently large cutoff. The
exponent is the zero's horizontal excess from the critical line. -/
theorem exists_twoLogClockProjection_rpow_lower
    (rho : RiemannGaussian.NontrivialZetaZero) (hoff : rho.1.re ≠ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ (2 * |rho.1.re - 1 / 2|) ≤
        ‖(historySpace (twoLogClockThreshold N)).starProjection
          (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) := by
  let a : ℝ := 2 * |rho.1.re - 1 / 2|
  have ha : 0 < a := by
    dsimp [a]
    have hdelta : 0 < |rho.1.re - 1 / 2| :=
      abs_pos.mpr (sub_ne_zero.mpr hoff)
    linarith
  let t : ℝ := a / 2
  have ht : 0 < t := by dsimp [t]; linarith
  let C₀ : ℝ := 2 / Real.log 2 + 1
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  let A : ℝ := 24 * C₀ / t + 24
  obtain ⟨D, hD, hfloor⟩ :=
    DeletionDilationGrowth.exists_abs_sourceCurrent_rpow_lower rho hoff
  obtain ⟨C, hC, hupper⟩ := exists_current_bound_by_twoLogClockProjection rho
  let c : ℝ := D / (16 * C)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  have hpowT : Tendsto (fun N : ℕ => (N : ℝ) ^ t) atTop atTop :=
    (tendsto_rpow_atTop ht).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop,
      2 * C * A ≤ D * (N : ℝ) ^ t :=
    by simpa only [mul_comm] using
      (hpowT.atTop_mul_const hD).eventually_ge_atTop (2 * C * A)
  filter_upwards [hfloor, hlarge, eventually_ge_atTop (3 : ℕ)] with
    N hfloorN hlargeN hN3
  have hNpos : (0 : ℝ) < N := by positivity
  have hNgeOne : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlogPow : Real.log (N : ℝ) ≤ (N : ℝ) ^ t / t :=
    Real.log_le_rpow_div hNpos.le ht
  have hHlog := twoLogClockThreshold_le_log_budget hN3
  have hHpow : (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) ≤
      (C₀ / t) * (N : ℝ) ^ t := by
    calc
      _ ≤ C₀ * Real.log (N : ℝ) := hHlog
      _ ≤ C₀ * ((N : ℝ) ^ t / t) :=
        mul_le_mul_of_nonneg_left hlogPow hC₀.le
      _ = (C₀ / t) * (N : ℝ) ^ t := by ring
  have hpowOne : (1 : ℝ) ≤ (N : ℝ) ^ t := Real.one_le_rpow hNgeOne ht.le
  have hrem : 24 * (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) + 24 ≤
      A * (N : ℝ) ^ t := by
    have hA : A = 24 * (C₀ / t) + 24 := by dsimp [A]; ring
    rw [hA]
    nlinarith [mul_le_mul_of_nonneg_left hHpow (by norm_num : (0 : ℝ) ≤ 24),
      mul_le_mul_of_nonneg_left hpowOne (by norm_num : (0 : ℝ) ≤ 24)]
  have hpower : (N : ℝ) ^ a = (N : ℝ) ^ t * (N : ℝ) ^ t := by
    rw [show a = t + t by dsimp [t]; ring, Real.rpow_add hNpos]
  have hpowNonneg : 0 ≤ (N : ℝ) ^ t := Real.rpow_nonneg hNpos.le _
  have hsmall : C * A * (N : ℝ) ^ t ≤ (D / 2) * (N : ℝ) ^ a := by
    rw [hpower]
    nlinarith [mul_nonneg (show 0 ≤ D * (N : ℝ) ^ t - 2 * C * A by
      linarith) hpowNonneg]
  have hmain : D * (N : ℝ) ^ a ≤
      C * (8 * ‖(historySpace (twoLogClockThreshold N)).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) +
        24 * (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) + 24) :=
    hfloorN.trans (hupper N)
  have hremmul : C * (24 * (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) + 24) ≤
      C * A * (N : ℝ) ^ t :=
    by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrem hC.le
  have hleft : (D / 2) * (N : ℝ) ^ a ≤
      8 * C * ‖(historySpace (twoLogClockThreshold N)).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) := by
    nlinarith
  have hfactor : c * (8 * C) = D / 2 := by
    dsimp [c]
    have hCne : C ≠ 0 := hC.ne'
    field_simp
    ring
  have h8C : 0 < 8 * C := by positivity
  apply (mul_le_mul_iff_left₀ h8C).mp
  calc
    (c * (N : ℝ) ^ a) * (8 * C) = (D / 2) * (N : ℝ) ^ a := by
      rw [mul_assoc, mul_comm ((N : ℝ) ^ a), ← mul_assoc, hfactor]
    _ ≤ 8 * C * ‖(historySpace (twoLogClockThreshold N)).starProjection
      (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) := hleft
    _ = ‖(historySpace (twoLogClockThreshold N)).starProjection
      (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) *
        (8 * C) := by ring

end RHTower.DeletionResidueMartingale
