import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalCodiagonalPacketBlowup
import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalReflectedGreenSource

/-!
# Scalar Möbius reader packet blow-up

Positive `ℓ¹` completion is not the reason finite physical packets blow up.  At one oriented Xi
copy every physical half-density coefficient has the same real sign, while each exact adaptive
Möbius divisor-reader column lies within `1/4` of `-1`.  Hence even the signed complex scalar
augmentation retains at least `3/4` of total half-density mass.

Uniform boundedness of these literal scalar source outputs is exactly same-fibre theta neutrality;
off center they exceed every threshold.  A surviving source producer must add a genuinely new
opposite principal channel before this reader, rather than rely on cancellation already present
in its Möbius tail or on reflection averaging.
-/

open Complex MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

theorem routeNGammaSewnTwistedCriticalChannelAmplitude_le_universal
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnTwistedCriticalChannelAmplitude t p ≤
      routeNGammaSewnUniversalCriticalChannelAmplitude p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
  rw [routeNGammaSewnTwistedCriticalChannelAmplitude_eq_universal_mul_sqrtCocycle]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hp0.le _)
    (Real.rpow_le_one_of_one_le_of_nonpos hp1
      (neg_nonpos.mpr (abs_nonneg t)))

theorem thetaMobiusPrimeNormalProfileHalfDensityAmplitude_nonneg_of_rate_nonneg
    (q : XiZeroCopy) (ha : 0 ≤ primeDepthBVWoldXiCenteredRate q.1)
    (p : Nat.Primes) :
    0 ≤ thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q := by
  rw [thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_channelGap, if_pos ha]
  exact sub_nonneg.mpr (routeNGammaSewnTwistedCriticalChannelAmplitude_le_universal _ _)

theorem thetaMobiusPrimeNormalProfileHalfDensityAmplitude_nonpos_of_rate_neg
    (q : XiZeroCopy) (ha : ¬ 0 ≤ primeDepthBVWoldXiCenteredRate q.1)
    (p : Nat.Primes) :
    thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q ≤ 0 := by
  rw [thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_channelGap, if_neg ha]
  exact neg_nonpos.mpr
    (sub_nonneg.mpr (routeNGammaSewnTwistedCriticalChannelAmplitude_le_universal _ _))

/-- Signed scalar output of the literal adaptive Möbius divisor reader on one finite physical
half-density packet. -/
def thetaMobiusPrimeNormalScalarReaderPacketOutput
    (q : XiZeroCopy) (s : Finset Nat.Primes) : ℂ :=
  ∑ p ∈ s, (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ) *
    adaptivePrimeNormalDivisorReader q
      (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)

/-- Same orientation at every prime prevents cancellation in the unweighted scalar sum. -/
theorem norm_sum_thetaMobiusPrimeNormalProfileHalfDensityAmplitude
    (q : XiZeroCopy) (s : Finset Nat.Primes) :
    ‖∑ p ∈ s, (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ)‖ =
      ∑ p ∈ s, |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| := by
  by_cases ha : 0 ≤ primeDepthBVWoldXiCenteredRate q.1
  · have hnonneg : ∀ p : Nat.Primes,
        0 ≤ thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q :=
      thetaMobiusPrimeNormalProfileHalfDensityAmplitude_nonneg_of_rate_nonneg q ha
    have hcast : (∑ p ∈ s,
        (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ)) =
        ((∑ p ∈ s, thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℝ) : ℂ) := by
      push_cast
      rfl
    calc
      ‖∑ p ∈ s, (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ)‖ =
          |∑ p ∈ s, thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| := by
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      _ = ∑ p ∈ s, thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q :=
        abs_of_nonneg (Finset.sum_nonneg fun p _ => hnonneg p)
      _ = ∑ p ∈ s, |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| := by
        apply Finset.sum_congr rfl
        intro p _hp
        rw [abs_of_nonneg (hnonneg p)]
  · have hnonpos : ∀ p : Nat.Primes,
        thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q ≤ 0 :=
      thetaMobiusPrimeNormalProfileHalfDensityAmplitude_nonpos_of_rate_neg q ha
    have hcast : (∑ p ∈ s,
        (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ)) =
        ((∑ p ∈ s, thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℝ) : ℂ) := by
      push_cast
      rfl
    calc
      ‖∑ p ∈ s, (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ)‖ =
          |∑ p ∈ s, thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| := by
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      _ = -(∑ p ∈ s, thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q) :=
        abs_of_nonpos (Finset.sum_nonpos fun p _ => hnonpos p)
      _ = ∑ p ∈ s, |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro p _hp
        rw [abs_of_nonpos (hnonpos p)]

/-- Exact reader tails perturb the common `-1` principal output by at most one quarter of packet
mass. -/
theorem norm_scalarReaderPacketOutput_add_principal_le_quarter
    (q : XiZeroCopy) (s : Finset Nat.Primes) :
    ‖thetaMobiusPrimeNormalScalarReaderPacketOutput q s +
        ∑ p ∈ s, (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ)‖ ≤
      (1 / 4 : ℝ) *
        ∑ p ∈ s, |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| := by
  rw [thetaMobiusPrimeNormalScalarReaderPacketOutput, ← Finset.sum_add_distrib]
  calc
    ‖∑ p ∈ s,
        ((thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ) *
          adaptivePrimeNormalDivisorReader q
            (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) +
          (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ))‖ =
        ‖∑ p ∈ s, (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ) *
          (adaptivePrimeNormalDivisorReader q
            (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) + 1)‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ ∑ p ∈ s, ‖(thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ) *
          (adaptivePrimeNormalDivisorReader q
            (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ s, |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| *
          (1 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _hp
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left
        (norm_adaptivePrimeNormalDivisorReader_single_add_one_le_quarter q p)
        (abs_nonneg _)
    _ = (1 / 4 : ℝ) *
        ∑ p ∈ s, |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring

/-- Signed scalar reader retains at least three quarters of physical packet mass. -/
theorem three_quarters_halfDensityMass_le_scalarReaderPacketOutput_norm
    (q : XiZeroCopy) (s : Finset Nat.Primes) :
    (3 / 4 : ℝ) *
        (∑ p ∈ s, |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q|) ≤
      ‖thetaMobiusPrimeNormalScalarReaderPacketOutput q s‖ := by
  have hdev := norm_scalarReaderPacketOutput_add_principal_le_quarter q s
  have htri :
      ‖∑ p ∈ s, (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ)‖ ≤
        ‖thetaMobiusPrimeNormalScalarReaderPacketOutput q s +
          ∑ p ∈ s, (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ)‖ +
        ‖thetaMobiusPrimeNormalScalarReaderPacketOutput q s‖ := by
    have := norm_sub_le
      (thetaMobiusPrimeNormalScalarReaderPacketOutput q s +
        ∑ p ∈ s, (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q : ℂ))
      (thetaMobiusPrimeNormalScalarReaderPacketOutput q s)
    simpa only [add_sub_cancel_left] using this
  rw [norm_sum_thetaMobiusPrimeNormalProfileHalfDensityAmplitude] at htri
  linarith

/-- Route P packet energy is controlled directly by signed scalar Möbius output. -/
theorem thetaMobiusPrimeNormalProfilePacketEnergy_le_scalarReaderPacketOutput_norm
    (q : XiZeroCopy) (s : Finset Nat.Primes) :
    thetaMobiusPrimeNormalProfilePacketEnergy q s ≤
      (4 / 3 : ℝ) * ‖thetaMobiusPrimeNormalScalarReaderPacketOutput q s‖ := by
  have hmass := three_quarters_halfDensityMass_le_scalarReaderPacketOutput_norm q s
  calc
    thetaMobiusPrimeNormalProfilePacketEnergy q s ≤
        ‖thetaMobiusPrimeNormalHalfDensityPacket q s‖ :=
      thetaMobiusPrimeNormalProfilePacketEnergy_le_halfDensityPacket_norm q s
    _ = ∑ p ∈ s, |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| :=
      norm_thetaMobiusPrimeNormalHalfDensityPacket q s
    _ ≤ (4 / 3 : ℝ) * ‖thetaMobiusPrimeNormalScalarReaderPacketOutput q s‖ := by
      have hsum0 : 0 ≤ ∑ p ∈ s,
          |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q| :=
        Finset.sum_nonneg (fun p _ => abs_nonneg
          (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q))
      nlinarith [norm_nonneg (thetaMobiusPrimeNormalScalarReaderPacketOutput q s)]

/-- Uniform signed scalar-reader output bound at one divisor copy. -/
def ThetaMobiusPrimeNormalScalarReaderPacketOutputBoundAt (q : XiZeroCopy) : Prop :=
  ∃ C : ℝ, ∀ s : Finset Nat.Primes,
    ‖thetaMobiusPrimeNormalScalarReaderPacketOutput q s‖ ≤ C

/-- Signed scalar-reader boundedness is exactly same-fibre theta neutrality. -/
theorem thetaMobiusPrimeNormalScalarReaderPacketOutputBoundAt_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    ThetaMobiusPrimeNormalScalarReaderPacketOutputBoundAt q ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    have hward : ThetaMobiusPrimeNormalWardBoundAt q := by
      refine ⟨(4 / 3 : ℝ) * C, fun s => ?_⟩
      exact (thetaMobiusPrimeNormalProfilePacketEnergy_le_scalarReaderPacketOutput_norm q s).trans
        (mul_le_mul_of_nonneg_left (hC s) (by norm_num))
    rw [thetaMobiusPrimeNormalWardBoundAt_iff_reciprocalEigenvalue_sq_positiveReal,
      thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero] at hward
    exact hward
  · intro hflux
    refine ⟨0, fun s => ?_⟩
    rw [thetaMobiusPrimeNormalScalarReaderPacketOutput]
    have hp : ∀ p : Nat.Primes,
        thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q = 0 := by
      intro p
      rw [thetaMobiusPrimeNormalProfileHalfDensityAmplitude,
        (thetaMobiusPrimeNormalReflectionProfile_eq_zero_iff_boundaryFlux_zero p q).2 hflux]
      ring
    simp [hp]

/-- Off center, even signed scalar Möbius packet outputs exceed every threshold. -/
theorem exists_scalarReaderPacketOutput_norm_gt_of_boundaryFlux_ne_zero
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0) (M : ℝ) :
    ∃ s : Finset Nat.Primes,
      M < ‖thetaMobiusPrimeNormalScalarReaderPacketOutput q s‖ := by
  by_contra h
  apply hflux
  apply (thetaMobiusPrimeNormalScalarReaderPacketOutputBoundAt_iff_boundaryFlux_zero q).1
  exact ⟨M, fun s => le_of_not_gt (fun hs => h ⟨s, hs⟩)⟩

/-- Global signed scalar-reader packet bound. -/
def ThetaMobiusPrimeNormalScalarReaderPacketOutputBound : Prop :=
  ∀ q : XiZeroCopy, ThetaMobiusPrimeNormalScalarReaderPacketOutputBoundAt q

/-- Global boundedness of signed scalar Möbius outputs is equivalent to RH. -/
theorem thetaMobiusPrimeNormalScalarReaderPacketOutputBound_iff_riemannHypothesis :
    ThetaMobiusPrimeNormalScalarReaderPacketOutputBound ↔ RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  exact forall_congr'
    thetaMobiusPrimeNormalScalarReaderPacketOutputBoundAt_iff_boundaryFlux_zero

end

end RHTower.HedenmalmThetaSource
