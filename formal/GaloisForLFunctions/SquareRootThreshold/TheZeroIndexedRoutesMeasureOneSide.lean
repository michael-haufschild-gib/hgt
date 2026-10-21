import GaloisForLFunctions.RHTower.PrimeTailSeedHurwitzReflection
import GaloisForLFunctions.RHTower.XiHurwitzAnchorPrimeTwoOrientationEnergy
import GaloisForLFunctions.RHTower.TimeOneGammaJetFockRHCriterion
import GaloisForLFunctions.RHTower.ConstitutiveDaggerConfluence
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology
import GaloisForLFunctions.RHTower.PrimeRotationXiCompletedResolution
import GaloisForLFunctions.RHTower.XiZeroLocalCriticalPhaseUniversalityLaw
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# The zero-indexed routes measure one side

The route candidates that index their objects by the zeros of `Ξ` each carry a per-zero
indicator: the Hurwitz two-seed residual `2^{ρ−2} − 2^{−ρ̄−1}` of route HJ, the first-prime seam
charge and the Hurwitz orientation defect, the time-one Gamma factorial-Fock jet boundedness of
route SEC, the radially calibrated dagger confluence of route CDC, the Deninger half-density mate
gain of route BSH, the invertibility of the completed rotation-algebra relation of route IRK, and
the reality of the weight-one Clifford energy of route W1C. This module records that at every
point of the Xi divisor all of them are the single Boolean "the zero is on the line"
(`theZeroIndexedRoutesMeasureOneSide`), and that each global form is the Riemann hypothesis
(`riemannHypothesis_iff_forall_xiDivisorSupport_of_indicator`, with the instances below).

The content of these candidate routes is therefore one route: the orientation of each zero
relative to the critical line, read on the zero itself. What separates them from a proof is not
the indicator but its production from the prime source before the zero is known.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open _root_.RHTower

/-- RH is the statement that every point of the Xi divisor lies on the line. -/
theorem riemannHypothesis_iff_forall_xiDivisorSupport_re_eq_half :
    RiemannHypothesis ↔ ∀ ρ : XiDivisorSupport, (ρ : ℂ).re = 1 / 2 :=
  ⟨fun h ρ => xi_divisor_support_re_eq_half_of_rh h ρ,
    riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half⟩

/-- **Transfer.** Any per-zero indicator that vanishes exactly on the line decides RH globally. -/
theorem riemannHypothesis_iff_forall_xiDivisorSupport_of_indicator {P : XiDivisorSupport → Prop}
    (hP : ∀ ρ : XiDivisorSupport, (ρ : ℂ).re = 1 / 2 ↔ P ρ) :
    RiemannHypothesis ↔ ∀ ρ : XiDivisorSupport, P ρ :=
  riemannHypothesis_iff_forall_xiDivisorSupport_re_eq_half.trans (forall_congr' hP)

/-! ### 1. The per-zero readings -/

/-- **HJ.** The two-seed residual vanishes at a divisor point iff the point is on the line. -/
theorem re_eq_half_iff_primeTailSeedTwoReflectionResidual_eq_zero (ρ : XiDivisorSupport) :
    (ρ : ℂ).re = 1 / 2 ↔ primeTailSeedTwoReflectionResidual (ρ : ℂ) = 0 :=
  ((primeTailSeedTwoReflectionResidual_eq_zero_iff_firstPrimeSeamCharge_eq_zero (ρ : ℂ)
    (xi_divisor_support_re_mem_open_unit ρ)).trans
    (orbitwiseFirstPrimeSeamCharge_eq_zero_iff (ρ : ℂ))).symm

/-- **HJ / SEC.** The first-prime seam charge vanishes iff the point is on the line. -/
theorem re_eq_half_iff_orbitwiseFirstPrimeSeamCharge_eq_zero (ρ : XiDivisorSupport) :
    (ρ : ℂ).re = 1 / 2 ↔ orbitwiseFirstPrimeSeamCharge (ρ : ℂ) = 0 :=
  (orbitwiseFirstPrimeSeamCharge_eq_zero_iff (ρ : ℂ)).symm

/-- **HJ.** The Hurwitz orientation defect vanishes iff the point is on the line. -/
theorem re_eq_half_iff_xiHurwitzOrientationDefect_eq_zero (ρ : XiDivisorSupport) :
    (ρ : ℂ).re = 1 / 2 ↔ xiHurwitzOrientationDefect ρ = 0 :=
  (re_eq_half_iff_orbitwiseFirstPrimeSeamCharge_eq_zero ρ).trans
    (orbitwiseFirstPrimeSeamCharge_eq_zero_iff_orientationDefect_zero ρ)

/-- **SEC.** Time-one Gamma factorial-Fock jet boundedness at any safe base point iff on the
line. -/
theorem re_eq_half_iff_timeOneGammaJetFockBounded (ρ : XiDivisorSupport) {x0 : ℝ}
    (hx0 : 1 < x0) : (ρ : ℂ).re = 1 / 2 ↔ TimeOneGammaJetFockBounded (ρ : ℂ) x0 :=
  (timeOneGammaJetFockBounded_iff_re_eq_half (xi_divisor_support_re_mem_open_unit ρ) hx0).symm

/-- **CDC.** Radially calibrated dagger confluence iff on the line. -/
theorem re_eq_half_iff_admitsRadiallyCalibratedDaggerConfluence (ρ : XiDivisorSupport)
    {N n : ℕ} (hN : 1 ≤ N) (hn : 2 ≤ n) :
    (ρ : ℂ).re = 1 / 2 ↔ AdmitsRadiallyCalibratedDaggerConfluence N n (ρ : ℂ) :=
  (admitsRadiallyCalibratedDaggerConfluence_iff_re_eq_half hN hn (ρ : ℂ)).symm

/-- **BSH.** The Deninger half-density mate gain is one iff on the line. -/
theorem re_eq_half_iff_deningerHalfDensityMateGain_eq_one (ρ : XiDivisorSupport) {n : ℕ}
    (hn : 2 ≤ n) : (ρ : ℂ).re = 1 / 2 ↔ deningerHalfDensityMateGain n (ρ : ℂ) = 1 :=
  (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn (ρ : ℂ)).symm

/-- **IRK.** The completed rotation-algebra relation is not a unit iff on the line. -/
theorem re_eq_half_iff_not_isUnit_deningerMeyerXiCompletedRelationMatrix (ρ : XiDivisorSupport)
    (p : Nat.Primes) (q : ℕ) :
    (ρ : ℂ).re = 1 / 2 ↔ ¬ IsUnit (deningerMeyerXiCompletedRelationMatrix p q ρ) := by
  rw [deningerMeyerXiCompletedRelation_isUnit_iff, not_not]

/-- **W1C.** The weight-one Clifford energy is real iff on the line. -/
theorem re_eq_half_iff_weightOneCliffordEnergy_im_eq_zero (ρ : XiDivisorSupport) (a : ℝ) :
    (ρ : ℂ).re = 1 / 2 ↔ (weightOneCliffordEnergy a (ρ : ℂ)).im = 0 :=
  (weightOneCliffordEnergy_im_eq_zero_iff_re_eq_half_of_xiZero a
    (xi_eq_zero_of_mem_divisor_support ρ)).symm

/-! ### 2. One side -/

/-- **The zero-indexed routes measure one side.** At every point of the Xi divisor the HJ
residual, the seam charge, the orientation defect, the SEC jet boundedness, the CDC confluence,
the BSH mate gain, the IRK non-invertibility and the W1C reality are the one statement
`Re ρ = ½`. -/
theorem theZeroIndexedRoutesMeasureOneSide (ρ : XiDivisorSupport) {x0 : ℝ} (hx0 : 1 < x0)
    {N n : ℕ} (hN : 1 ≤ N) (hn : 2 ≤ n) (p : Nat.Primes) (q : ℕ) (a : ℝ) :
    ((ρ : ℂ).re = 1 / 2 ↔ primeTailSeedTwoReflectionResidual (ρ : ℂ) = 0) ∧
    ((ρ : ℂ).re = 1 / 2 ↔ orbitwiseFirstPrimeSeamCharge (ρ : ℂ) = 0) ∧
    ((ρ : ℂ).re = 1 / 2 ↔ xiHurwitzOrientationDefect ρ = 0) ∧
    ((ρ : ℂ).re = 1 / 2 ↔ TimeOneGammaJetFockBounded (ρ : ℂ) x0) ∧
    ((ρ : ℂ).re = 1 / 2 ↔ AdmitsRadiallyCalibratedDaggerConfluence N n (ρ : ℂ)) ∧
    ((ρ : ℂ).re = 1 / 2 ↔ deningerHalfDensityMateGain n (ρ : ℂ) = 1) ∧
    ((ρ : ℂ).re = 1 / 2 ↔ ¬ IsUnit (deningerMeyerXiCompletedRelationMatrix p q ρ)) ∧
    ((ρ : ℂ).re = 1 / 2 ↔ (weightOneCliffordEnergy a (ρ : ℂ)).im = 0) :=
  ⟨re_eq_half_iff_primeTailSeedTwoReflectionResidual_eq_zero ρ,
    re_eq_half_iff_orbitwiseFirstPrimeSeamCharge_eq_zero ρ,
    re_eq_half_iff_xiHurwitzOrientationDefect_eq_zero ρ,
    re_eq_half_iff_timeOneGammaJetFockBounded ρ hx0,
    re_eq_half_iff_admitsRadiallyCalibratedDaggerConfluence ρ hN hn,
    re_eq_half_iff_deningerHalfDensityMateGain_eq_one ρ hn,
    re_eq_half_iff_not_isUnit_deningerMeyerXiCompletedRelationMatrix ρ p q,
    re_eq_half_iff_weightOneCliffordEnergy_im_eq_zero ρ a⟩

/-! ### 3. The global forms are RH -/

theorem riemannHypothesis_iff_forall_xiHurwitzOrientationDefect_eq_zero :
    RiemannHypothesis ↔ ∀ ρ : XiDivisorSupport, xiHurwitzOrientationDefect ρ = 0 :=
  riemannHypothesis_iff_forall_xiDivisorSupport_of_indicator
    re_eq_half_iff_xiHurwitzOrientationDefect_eq_zero

theorem riemannHypothesis_iff_forall_admitsRadiallyCalibratedDaggerConfluence {N n : ℕ}
    (hN : 1 ≤ N) (hn : 2 ≤ n) :
    RiemannHypothesis ↔ ∀ ρ : XiDivisorSupport, AdmitsRadiallyCalibratedDaggerConfluence N n ρ :=
  riemannHypothesis_iff_forall_xiDivisorSupport_of_indicator fun ρ =>
    re_eq_half_iff_admitsRadiallyCalibratedDaggerConfluence ρ hN hn

theorem riemannHypothesis_iff_forall_deningerHalfDensityMateGain_eq_one {n : ℕ} (hn : 2 ≤ n) :
    RiemannHypothesis ↔ ∀ ρ : XiDivisorSupport, deningerHalfDensityMateGain n ρ = 1 :=
  riemannHypothesis_iff_forall_xiDivisorSupport_of_indicator fun ρ =>
    re_eq_half_iff_deningerHalfDensityMateGain_eq_one ρ hn

theorem riemannHypothesis_iff_forall_not_isUnit_deningerMeyerXiCompletedRelationMatrix
    (p : Nat.Primes) (q : ℕ) :
    RiemannHypothesis ↔
      ∀ ρ : XiDivisorSupport, ¬ IsUnit (deningerMeyerXiCompletedRelationMatrix p q ρ) :=
  riemannHypothesis_iff_forall_xiDivisorSupport_of_indicator fun ρ =>
    re_eq_half_iff_not_isUnit_deningerMeyerXiCompletedRelationMatrix ρ p q

theorem riemannHypothesis_iff_forall_weightOneCliffordEnergy_im_eq_zero (a : ℝ) :
    RiemannHypothesis ↔ ∀ ρ : XiDivisorSupport, (weightOneCliffordEnergy a ρ).im = 0 :=
  riemannHypothesis_iff_forall_xiDivisorSupport_of_indicator fun ρ =>
    re_eq_half_iff_weightOneCliffordEnergy_im_eq_zero ρ a

end GaloisForLFunctions.SquareRootThreshold

end
