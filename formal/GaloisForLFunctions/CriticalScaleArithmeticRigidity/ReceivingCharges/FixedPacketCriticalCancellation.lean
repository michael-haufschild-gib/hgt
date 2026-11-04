import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FixedConductorCriticalCancellation
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeMoments
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeComplementReceiver

/-!
# Complete cancellation of fixed finite receiving packets

A finite family of fixed conductors has vanishing complete critical output
for every bounded coefficient family. Harmonic centering has bounded
coefficients, so it preserves this cancellation for each fixed prime cutoff.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  ArithmeticHodgeTheoryOfDegenerations SpacingScaleHarmonicAnalysis
  SelectiveMultiscaleArithmeticPositivity

/-- Bounded coefficients in a fixed finite conductor family have vanishing complete output. -/
theorem tendsto_fixedPacket_critical_complete_norm {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (a : ℕ → ℕ → ℝ) (B : ℕ → ℝ)
    (hB : ∀ᶠ N in atTop, ∀ m ∈ S, |a N m| ≤ B m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (∑ m ∈ S, a N m • normalizedRamanujanHorizonVector m N)‖) atTop (𝓝 0) := by
  have hlim := tendsto_finsetSum S (fun m hm =>
    (tendsto_fixedConductor_critical_complete_norm hc hR hcrit (hS m hm)).const_mul (B m))
  simp only [mul_zero, sum_const_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hB] with N hBN
  simp only [map_sum, map_smul]
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro m hm
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hBN m hm) (norm_nonneg _)

/-- Physical conductor synthesis is the finite sum of normalized horizon modes. -/
theorem physicalPacket_eq_sum_normalizedModes (Q N : ℕ) (a : ℕ → ℝ) :
    (Real.sqrt (Real.log N))⁻¹ • packetVector (normalizedConductorPacket Q a) N =
      ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N := by
  rw [packetVector_normalizedConductorPacket, smul_sum]
  apply sum_congr rfl
  intro m _
  simp only [normalizedRamanujanHorizonVector, smul_smul]
  rw [mul_comm]

/-- The harmonic mean of a fixed conductor packet is bounded by its finite period bounds. -/
theorem harmonicMean_fixedPacket_abs_le (Q : ℕ) {N : ℕ} (hN : 1 ≤ N) (a : ℕ → ℝ) :
    |harmonicSum N (conductorHorizonProfile Q a) / harmonicMass N| ≤
      ∑ m ∈ Icc 1 Q, |a m| * modeBound m := by
  let B := ∑ m ∈ Icc 1 Q, |a m| * modeBound m
  have hpoint (n : ℕ) : |normalizedConductorPacket Q a n| ≤ B := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
    intro m hm
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_le_periodSum (mem_Icc.mp hm).1
        (normalizedRamanujanMode_periodic (mem_Icc.mp hm).1) n) (abs_nonneg _)
  have hmass := harmonicMass_pos hN
  simp only [SelectiveMultiscaleArithmeticPositivity.harmonicSum, conductorHorizonProfile,
    div_div, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rw [abs_div, abs_of_pos hmass]
  apply (div_le_iff₀ hmass).mpr
  calc
    _ ≤ ∑ n ∈ Icc 1 N, |normalizedConductorPacket Q a n / (n : ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 N, B / (n : ℝ) := by
      apply sum_le_sum
      intro n _
      rw [abs_div, Nat.abs_cast]
      exact div_le_div_of_nonneg_right (hpoint n) (Nat.cast_nonneg n)
    _ = B * harmonicMass N := by
      simp only [harmonicMass, mul_sum, div_eq_mul_inv, one_mul]

/-- Exact harmonic centering leaves every fixed coefficient uniformly bounded in the horizon. -/
theorem harmonicCentered_fixedCoefficient_abs_le (Q : ℕ) {N : ℕ}
    (hN : 1 ≤ N) (a : ℕ → ℝ) (m : ℕ) :
    |harmonicCenteredCoefficients Q N a m| ≤
      |a m| + ∑ j ∈ Icc 1 Q, |a j| * modeBound j := by
  have hmean := harmonicMean_fixedPacket_abs_le Q hN a
  have hB : 0 ≤ ∑ j ∈ Icc 1 Q, |a j| * modeBound j := by
    unfold modeBound
    positivity
  unfold harmonicCenteredCoefficients addConstantConductor
  split_ifs
  · exact (abs_add_le _ _).trans (add_le_add le_rfl (by simpa only [abs_neg] using hmean))
  · simpa only [add_zero] using le_add_of_nonneg_right hB

/-- Every fixed packet, after literal harmonic pole removal, has vanishing complete critical output. -/
theorem tendsto_harmonicCentered_fixedPacket_complete_norm {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (Q : ℕ) (a : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        ((Real.sqrt (Real.log N))⁻¹ • packetVector
          (normalizedConductorPacket Q (harmonicCenteredCoefficients Q N a)) N)‖)
      atTop (𝓝 0) := by
  simp only [physicalPacket_eq_sum_normalizedModes]
  apply tendsto_fixedPacket_critical_complete_norm hc hR hcrit (Icc 1 Q)
    (fun m hm => (mem_Icc.mp hm).1) (fun N => harmonicCenteredCoefficients Q N a)
    (fun m => |a m| + ∑ j ∈ Icc 1 Q, |a j| * modeBound j)
  filter_upwards [eventually_ge_atTop 1] with N hN m _
  exact harmonicCentered_fixedCoefficient_abs_le Q hN a m

#print axioms tendsto_fixedPacket_critical_complete_norm
#print axioms harmonicMean_fixedPacket_abs_le
#print axioms tendsto_harmonicCentered_fixedPacket_complete_norm

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
