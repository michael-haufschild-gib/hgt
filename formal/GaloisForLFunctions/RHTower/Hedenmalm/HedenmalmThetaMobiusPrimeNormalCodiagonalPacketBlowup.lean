import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalHalfDensityDomainNoGo
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalWardContract

/-!
# Finite physical packets through the adaptive prime-normal codiagonal

Although the physical Möbius half-density does not enter the adaptive `ℓ¹` domain off center, each
finite prime packet does.  This file sends those literal packets through the existing adaptive
source codiagonal.

The codiagonal lower bound converts uniform boundedness of its arithmetic output into the Route P
finite Ward bound.  Conversely, on a neutral copy every packet is zero.  Hence bounded output is
exactly same-fibre neutrality, and every off-center copy has codiagonal outputs exceeding every
real threshold.  The surviving producer must therefore prove a genuine source cancellation law
before the `ℓ¹` output norm is closed; completion cannot manufacture it.
-/

open Complex MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Literal finite packet of physical Möbius prime-normal half-densities. -/
def thetaMobiusPrimeNormalHalfDensityPacket
    (q : XiZeroCopy) (s : Finset Nat.Primes) : AdaptivePrimeL1 :=
  ⟨fun p => if p ∈ s then
      (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ) else 0,
    memℓp_gen (summable_of_hasFiniteSupport (by
      refine s.finite_toSet.subset ?_
      intro p hp
      by_contra hps
      apply hp
      simp [show p ∉ s by exact hps]))⟩

theorem thetaMobiusPrimeNormalHalfDensityPacket_apply
    (q : XiZeroCopy) (s : Finset Nat.Primes) (p : Nat.Primes) :
    thetaMobiusPrimeNormalHalfDensityPacket q s p = if p ∈ s then
      (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ) else 0 :=
  rfl

/-- Packet `ℓ¹` norm is its finite absolute half-density mass. -/
theorem norm_thetaMobiusPrimeNormalHalfDensityPacket
    (q : XiZeroCopy) (s : Finset Nat.Primes) :
    ‖thetaMobiusPrimeNormalHalfDensityPacket q s‖ = ∑ p ∈ s,
      |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one]
  calc
    (∑' p : Nat.Primes, ‖thetaMobiusPrimeNormalHalfDensityPacket q s p‖) =
        ∑ p ∈ s, ‖thetaMobiusPrimeNormalHalfDensityPacket q s p‖ := by
      apply tsum_eq_sum
      intro p hp
      rw [thetaMobiusPrimeNormalHalfDensityPacket_apply]
      simp [hp]
    _ = ∑ p ∈ s,
        |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [thetaMobiusPrimeNormalHalfDensityPacket_apply]
      simp [hp, Real.norm_eq_abs]

/-- Actual adaptive arithmetic-source output of one physical finite packet. -/
def thetaMobiusPrimeNormalCodiagonalPacketOutput
    (q : XiZeroCopy) (s : Finset Nat.Primes) : AdaptiveArithmeticL1 :=
  adaptivePrimeNormalCodiagonal
    (xiAdaptivePrimeNormalScale q)
    (xiSpectralPointSupport q.1)
    (xiAdaptivePrimeNormalScale_spec q)
    (thetaMobiusPrimeNormalHalfDensityPacket q s)

/-- Route P quadratic packet energy is bounded by physical packet `ℓ¹` mass. -/
theorem thetaMobiusPrimeNormalProfilePacketEnergy_le_halfDensityPacket_norm
    (q : XiZeroCopy) (s : Finset Nat.Primes) :
    thetaMobiusPrimeNormalProfilePacketEnergy q s ≤
      ‖thetaMobiusPrimeNormalHalfDensityPacket q s‖ := by
  rw [thetaMobiusPrimeNormalProfilePacketEnergy,
    norm_thetaMobiusPrimeNormalHalfDensityPacket]
  apply Finset.sum_le_sum
  intro p _hp
  rw [← thetaMobiusPrimeNormalProfileHalfDensityAmplitude_sq]
  have h0 := abs_nonneg (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q)
  have h1 := abs_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_le_one p q
  rw [← sq_abs]
  nlinarith

/-- Codiagonal conservativity controls every finite physical packet by its arithmetic output. -/
theorem norm_halfDensityPacket_le_codiagonalPacketOutput
    (q : XiZeroCopy) (s : Finset Nat.Primes) :
    ‖thetaMobiusPrimeNormalHalfDensityPacket q s‖ ≤
      (4 / 3 : ℝ) * ‖thetaMobiusPrimeNormalCodiagonalPacketOutput q s‖ := by
  have h := adaptivePrimeNormalCodiagonal_lower_bound
    (xiAdaptivePrimeNormalScale q)
    (xiSpectralPointSupport q.1)
    (xiAdaptivePrimeNormalScale_spec q)
    (thetaMobiusPrimeNormalHalfDensityPacket q s)
  change (3 / 4 : ℝ) * ‖thetaMobiusPrimeNormalHalfDensityPacket q s‖ ≤
    ‖thetaMobiusPrimeNormalCodiagonalPacketOutput q s‖ at h
  nlinarith [norm_nonneg (thetaMobiusPrimeNormalHalfDensityPacket q s),
    norm_nonneg (thetaMobiusPrimeNormalCodiagonalPacketOutput q s)]

/-- Uniform arithmetic output bound for all finite physical packets at one divisor copy. -/
def ThetaMobiusPrimeNormalCodiagonalPacketOutputBoundAt (q : XiZeroCopy) : Prop :=
  ∃ C : ℝ, ∀ s : Finset Nat.Primes,
    ‖thetaMobiusPrimeNormalCodiagonalPacketOutput q s‖ ≤ C

/-- Uniform codiagonal output boundedness is exactly same-fibre theta neutrality. -/
theorem thetaMobiusPrimeNormalCodiagonalPacketOutputBoundAt_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    ThetaMobiusPrimeNormalCodiagonalPacketOutputBoundAt q ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    have hward : ThetaMobiusPrimeNormalWardBoundAt q := by
      refine ⟨(4 / 3 : ℝ) * C, fun s => ?_⟩
      calc
        thetaMobiusPrimeNormalProfilePacketEnergy q s ≤
            ‖thetaMobiusPrimeNormalHalfDensityPacket q s‖ :=
          thetaMobiusPrimeNormalProfilePacketEnergy_le_halfDensityPacket_norm q s
        _ ≤ (4 / 3 : ℝ) * ‖thetaMobiusPrimeNormalCodiagonalPacketOutput q s‖ :=
          norm_halfDensityPacket_le_codiagonalPacketOutput q s
        _ ≤ (4 / 3 : ℝ) * C :=
          mul_le_mul_of_nonneg_left (hC s) (by norm_num)
    rw [thetaMobiusPrimeNormalWardBoundAt_iff_reciprocalEigenvalue_sq_positiveReal,
      thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero] at hward
    exact hward
  · intro hflux
    refine ⟨0, fun s => ?_⟩
    have hpacket : thetaMobiusPrimeNormalHalfDensityPacket q s = 0 := by
      ext p
      rw [thetaMobiusPrimeNormalHalfDensityPacket_apply]
      by_cases hp : p ∈ s
      · rw [if_pos hp, thetaMobiusPrimeNormalProfileHalfDensityAmplitude,
          (thetaMobiusPrimeNormalReflectionProfile_eq_zero_iff_boundaryFlux_zero p q).2 hflux]
        norm_num
      · rw [if_neg hp]
        rfl
    rw [thetaMobiusPrimeNormalCodiagonalPacketOutput, hpacket, map_zero, norm_zero]

/-- Pointwise codiagonal output contract is exactly positivity of the Route P squared node. -/
theorem thetaMobiusPrimeNormalCodiagonalPacketOutputBoundAt_iff_reciprocalEigenvalue_sq_positiveReal
    (q : XiZeroCopy) :
    ThetaMobiusPrimeNormalCodiagonalPacketOutputBoundAt q ↔
      ∃ r : ℝ, 0 < r ∧ thetaXiReciprocalEigenvalue q ^ 2 = (r : ℂ) := by
  rw [thetaMobiusPrimeNormalCodiagonalPacketOutputBoundAt_iff_boundaryFlux_zero,
    thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero]

/-- Every off-center copy has actual adaptive codiagonal packet outputs exceeding every threshold. -/
theorem exists_codiagonalPacketOutput_norm_gt_of_boundaryFlux_ne_zero
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0) (M : ℝ) :
    ∃ s : Finset Nat.Primes,
      M < ‖thetaMobiusPrimeNormalCodiagonalPacketOutput q s‖ := by
  by_contra h
  apply hflux
  apply (thetaMobiusPrimeNormalCodiagonalPacketOutputBoundAt_iff_boundaryFlux_zero q).1
  exact ⟨M, fun s => le_of_not_gt (fun hs => h ⟨s, hs⟩)⟩

/-- Global finite-packet boundedness for actual adaptive arithmetic outputs. -/
def ThetaMobiusPrimeNormalCodiagonalPacketOutputBound : Prop :=
  ∀ q : XiZeroCopy, ThetaMobiusPrimeNormalCodiagonalPacketOutputBoundAt q

/-- Global boundedness of actual adaptive codiagonal packet outputs is equivalent to RH. -/
theorem thetaMobiusPrimeNormalCodiagonalPacketOutputBound_iff_riemannHypothesis :
    ThetaMobiusPrimeNormalCodiagonalPacketOutputBound ↔ RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  exact forall_congr'
    thetaMobiusPrimeNormalCodiagonalPacketOutputBoundAt_iff_boundaryFlux_zero

end

end RHTower.HedenmalmThetaSource
