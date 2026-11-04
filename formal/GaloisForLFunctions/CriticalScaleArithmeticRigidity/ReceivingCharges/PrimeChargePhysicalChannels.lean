import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeQuadraticChannels
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeUniformCoefficients
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FixedPacketCriticalCancellation

/-!
# Literal prime and scalar channels in physical coordinates

Physical normalization divides the exact dilation identity by the horizon
logarithm. The scalar diagonal retains its floor and Mertens remainders;
its cost is logarithmic in the overlap and proportional to physical input.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory CompletedArithmeticForms

/-- The neutral coherent physical vector is exactly its conductor synthesis. -/
theorem harmonicPrimeChargeVector_eq_sum (Q N : ℕ) (t : ℝ) :
    harmonicPrimeChargeVector Q N t =
      ∑ m ∈ Icc 1 Q, harmonicPrimeChargeCoefficients Q N t m •
        normalizedRamanujanHorizonVector m N :=
  physicalPacket_eq_sum_normalizedModes Q N _

/-- Physical normalization retains the complete finite Mertens diagonal of the prime form. -/
theorem renormalizedPrime_physicalPacket (N : ℕ) (F : ℕ → ℝ) (s : ℝ) :
    let u := (Real.sqrt (Real.log N))⁻¹ • packetVector F N
    (Real.log N * ‖u‖ ^ 2 - ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫) +
      (s - Real.eulerMascheroniConstant) * ‖u‖ ^ 2 =
      (jumpEnergy N F + ∑ n ∈ Icc 1 N,
        F n ^ 2 / n * (s + floorDefect N n - mertensRemainder (N / n))) / Real.log N := by
  dsimp only
  have hs : (Real.sqrt (Real.log N))⁻¹ ^ 2 = (Real.log N)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, map_smul,
    real_inner_smul_left, real_inner_smul_right]
  calc
    _ = (Real.sqrt (Real.log N))⁻¹ ^ 2 *
        ((Real.log N * ‖packetVector F N‖ ^ 2 -
          ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (packetVector F N), packetVector F N⟫) +
          (s - Real.eulerMascheroniConstant) * ‖packetVector F N‖ ^ 2) := by ring
    _ = _ := by rw [hs, renormalizedPrime_packetVector]; ring

/-- The literal physical scalar correction costs only the overlap logarithm and input square. -/
theorem abs_physicalPacket_scalar_diagonal_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 1 ≤ c)
    {N : ℕ} (hN : 1 ≤ N) (hcN : c ≤ N) (F : ℕ → ℝ) :
    let u := (Real.sqrt (Real.log N))⁻¹ • packetVector F N
    |((Real.log N * ‖u‖ ^ 2 - ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫) +
        (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
          completeWeilSelfError φ c N) * ‖u‖ ^ 2) - jumpEnergy N F / Real.log N| ≤
      (|completeWeilSelfFinitePart φ 1| + Real.log c + Real.exp (1 / 2) / 2 +
        Real.log 2 + (Real.log 4 + 4 + Real.eulerMascheroniConstant)) * ‖u‖ ^ 2 := by
  dsimp only
  have h := renormalizedPrime_physicalPacket N F
    (completeWeilSelfFinitePart φ c + completeWeilSelfError φ c N)
  dsimp only at h
  rw [show completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
      completeWeilSelfError φ c N =
      (completeWeilSelfFinitePart φ c + completeWeilSelfError φ c N) -
        Real.eulerMascheroniConstant by ring, h, add_div, add_sub_cancel_left,
    abs_div, abs_of_nonneg (Real.log_natCast_nonneg N)]
  have hb := div_le_div_of_nonneg_right
    (abs_complete_packet_diagonal_le hφ hsupp hM hc hN hcN F)
    (Real.log_natCast_nonneg N)
  refine hb.trans_eq ?_
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
    Real.sq_sqrt (Real.log_natCast_nonneg N), packetVector_norm_sq]
  ring

#print axioms renormalizedPrime_physicalPacket
#print axioms abs_physicalPacket_scalar_diagonal_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
