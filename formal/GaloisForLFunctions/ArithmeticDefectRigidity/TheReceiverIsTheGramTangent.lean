import GaloisForLFunctions.ArithmeticDefectRigidity.ForcingScaleSeparation

/-!
# The actual receiver is the tangent difference of the forcing Gram matrix

Write `A` for the centered receiver, `ρ` for its forcing, and `D` for the proper cofactor sum.
The identity `ρ = A + D` gives a two-vector Gram system with energies `F = ‖ρ‖²`, `G = ‖D‖²`
and pairing `Q = ⟪ρ,D⟫`. Its squared-distance coordinate is exactly `F + G - 2Q = E`.

The Gram determinant is `EF - ⟪A,ρ⟫²`. It is nonnegative, but its normalization by `F²` tends
to zero for the actual source. Thus passing to the forcing-scale Gram determinant erases the
critical receiver. The exact signed distance retains it.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

def receiverForcingPairing (ε : ℝ) (T : ℕ) : ℝ :=
  pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (inversionDefect ε)

def cofactorEnergy (ε : ℝ) (T : ℕ) : ℝ :=
  pronicNorm T (offDiagonalUnitDilation ε) ^ 2

def forcingCofactorPairing (ε : ℝ) (T : ℕ) : ℝ :=
  pronicPairing T (inversionDefect ε) (offDiagonalUnitDilation ε)

/-- The full cofactor energy includes the signed receiver-forcing covariance. -/
theorem cofactorEnergy_eq (ε : ℝ) (T : ℕ) :
    cofactorEnergy ε T = forcingEnergy ε T + dampedMobiusEnergy ε T -
      2 * receiverForcingPairing ε T := by
  have hE : dampedMobiusEnergy ε T =
      pronicNorm T (pmPowerDampedCenteredDivisorPrefix ε) ^ 2 := by
    rw [pronicNorm_centeredPrefix, Real.sq_sqrt (dampedMobiusEnergy_nonneg ε T)]
  rw [hE]
  simp only [cofactorEnergy, forcingEnergy, receiverForcingPairing, pronicNorm_sq,
    pronicPairing, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun n hn => by
    rw [inversionDefect_eq_centeredPrefix_add_offDiagonal ε (mem_Icc.mp hn).1]
    ring

/-- The forcing-cofactor pairing differs from forcing energy by the signed covariance. -/
theorem forcingCofactorPairing_eq (ε : ℝ) (T : ℕ) :
    forcingCofactorPairing ε T = forcingEnergy ε T - receiverForcingPairing ε T := by
  simp only [forcingCofactorPairing, forcingEnergy, receiverForcingPairing,
    pronicNorm_sq, pronicPairing, ← sum_sub_distrib]
  exact sum_congr rfl fun n hn => by
    rw [inversionDefect_eq_centeredPrefix_add_offDiagonal ε (mem_Icc.mp hn).1]
    ring

/-- The receiver is exactly the signed distance coordinate of the two-vector Gram matrix. -/
theorem gram_distance_eq_receiverEnergy (ε : ℝ) (T : ℕ) :
    forcingEnergy ε T + cofactorEnergy ε T - 2 * forcingCofactorPairing ε T =
      dampedMobiusEnergy ε T := by
  rw [cofactorEnergy_eq, forcingCofactorPairing_eq]
  ring

/-- The covariance cannot exceed the geometric mean of the two energies. -/
theorem receiverForcingPairing_sq_le (ε : ℝ) (T : ℕ) :
    receiverForcingPairing ε T ^ 2 ≤ dampedMobiusEnergy ε T * forcingEnergy ε T := by
  have hpos := sum_mul_div_le_pronicNorm T
    (pmPowerDampedCenteredDivisorPrefix ε) (inversionDefect ε)
  have hneg := sum_mul_div_le_pronicNorm T
    (pmPowerDampedCenteredDivisorPrefix ε) (fun n => -inversionDefect ε n)
  rw [pronicNorm_neg] at hneg
  have hsum : (∑ n ∈ Icc 1 T,
      pmPowerDampedCenteredDivisorPrefix ε n * -inversionDefect ε n /
        ((n : ℝ) * ((n : ℝ) + 1))) = -receiverForcingPairing ε T := by
    simp only [receiverForcingPairing, pronicPairing, mul_neg, neg_div, sum_neg_distrib]
  rw [hsum] at hneg
  change receiverForcingPairing ε T ≤ _ at hpos
  have habs : |receiverForcingPairing ε T| ≤
      pronicNorm T (pmPowerDampedCenteredDivisorPrefix ε) *
        pronicNorm T (inversionDefect ε) := abs_le.mpr ⟨by linarith, hpos⟩
  have h := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs, mul_pow, pronicNorm_centeredPrefix,
    Real.sq_sqrt (dampedMobiusEnergy_nonneg ε T)] at h
  exact h

/-- The determinant of the forcing and cofactor Gram matrix. -/
def forcingGramDefect (ε : ℝ) (T : ℕ) : ℝ :=
  forcingEnergy ε T * cofactorEnergy ε T - forcingCofactorPairing ε T ^ 2

theorem forcingGramDefect_eq (ε : ℝ) (T : ℕ) :
    forcingGramDefect ε T = dampedMobiusEnergy ε T * forcingEnergy ε T -
      receiverForcingPairing ε T ^ 2 := by
  rw [forcingGramDefect, cofactorEnergy_eq, forcingCofactorPairing_eq]
  ring

/-- The complete determinant has a nonnegative budget paid by the product of both scales. -/
theorem forcingGramDefect_bounds (ε : ℝ) (T : ℕ) :
    0 ≤ forcingGramDefect ε T ∧
      forcingGramDefect ε T ≤ dampedMobiusEnergy ε T * forcingEnergy ε T := by
  rw [forcingGramDefect_eq]
  exact ⟨sub_nonneg.mpr (receiverForcingPairing_sq_le ε T),
    sub_le_self _ (sq_nonneg _)⟩

/-- The forcing-normalized determinant vanishes for the actual arithmetic source. -/
theorem tendsto_forcingGramDefect_div_forcingEnergy_sq_zero (ε : SubcriticalDamping) :
    Tendsto (fun T => forcingGramDefect ε T / forcingEnergy ε T ^ 2) atTop (𝓝 0) := by
  refine squeeze_zero' (Filter.Eventually.of_forall fun T =>
    div_nonneg (forcingGramDefect_bounds ε T).1 (sq_nonneg _)) ?_
    (tendsto_receiver_div_forcingEnergy_zero ε)
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hF : forcingEnergy ε T ≠ 0 := by
    cases T with
    | zero => omega
    | succ N => exact (forcingEnergy_succ_pos ε N).ne'
  calc
    _ ≤ dampedMobiusEnergy ε T * forcingEnergy ε T / forcingEnergy ε T ^ 2 :=
      div_le_div_of_nonneg_right (forcingGramDefect_bounds ε T).2 (sq_nonneg _)
    _ = _ := by field_simp

/-- Receiver normalization retains exactly one unit in the collapsing Gram distance. -/
theorem gram_distance_div_receiverEnergy_eq_one (ε : SubcriticalDamping) (T : ℕ) :
    (forcingEnergy ε (T + 1) + cofactorEnergy ε (T + 1) -
      2 * forcingCofactorPairing ε (T + 1)) / dampedMobiusEnergy ε (T + 1) = 1 := by
  rw [gram_distance_eq_receiverEnergy, div_self (receiverEnergy_succ_pos ε T).ne']

end GaloisForLFunctions.ArithmeticDefectRigidity
