import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFECenteredQNMClockRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhaseSensitiveChiralWardAmplitude

/-!
# Source-FE clock/chiral-amplitude transduction

The exact source-FE/centered-QNM clock defect of HC57 is a literal nonlinear source observable.
Evaluating its unit-packet defect at reflected support gives the Xi tilt times the nonzero source
cocycle.  The physical phase-sensitive mixed-horizon chiral source is this coefficient multiplied
by an explicit transducer.

For every nonzero Einstein seed the transducer is nowhere zero.  Thus source darkness and clock
anticommutation have the same pointwise zero locus, and universal darkness/anticommutation is RH.
The existing FZZ-P information force, every PW-B recoil-grade imbalance, and the RBH
multiplicity-leading imbalance are exact scalar images of this same clock coefficient.

`[NEW] [NONLINEAR SOURCE] [CLOCK TRANSDUCTION] [FOUR-ROUTE WARD] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Reflected output coefficient of the source-FE/centered-QNM defect on one unit packet. -/
def hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  hbXiPeierlsSourceFECenteredQNMClockDefect n (Finsupp.single q 1)
    (xiZeroCopyReflectEquiv q)

/-- The reflected clock coefficient is exactly Xi tilt times the literal source cocycle. -/
theorem hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q =
      Complex.I * (((q.1 : ℂ).re - 1 / 2 : ℝ) : ℂ) *
        hbXiPeierlsUnitSourceFECocycle q := by
  rw [hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient,
    hbXiPeierlsSourceFECenteredQNMClockDefect_single]
  simp

/-- Redshift centering makes the extracted clock charge independent of overtone. -/
theorem hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_overtone_independent
    (n m : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q =
      hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient m q := by
  rw [hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq,
    hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq]

/-- Exact physical conversion from reflected clock charge to nonlinear chiral source amplitude. -/
def hbXiPeierlsClockToChiralSourceTransducer
    (amplitude : ℂ) (q : XiZeroCopy) : ℂ :=
  2 * Complex.I * hbXiPhaseSensitiveChiralWardMultiplier amplitude q /
    hbXiPeierlsUnitSourceFECocycle q

/-- The actual nonlinear mixed-horizon source is exactly the transduced HC57 clock coefficient. -/
theorem d4BMMixedHorizonOpticalSourceProjection_eq_clockTransducer_mul_defectCoefficient
    (n : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q =
      hbXiPeierlsClockToChiralSourceTransducer amplitude q *
        hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q := by
  rw [d4BMMixedHorizonOpticalSourceProjection_eq_chiralMultiplier_mul_deningerCharge,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq,
    hbXiPeierlsClockToChiralSourceTransducer,
    hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq]
  have hk := hbXiPeierlsUnitSourceFECocycle_ne_zero q
  field_simp [hk]
  simp only [deningerDivisorThetaEigen]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Every nonzero Einstein seed gives a nowhere-zero physical clock/source transducer. -/
theorem hbXiPeierlsClockToChiralSourceTransducer_ne_zero
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    hbXiPeierlsClockToChiralSourceTransducer amplitude q ≠ 0 := by
  rw [hbXiPeierlsClockToChiralSourceTransducer]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (hbXiPhaseSensitiveChiralWardMultiplier_ne_zero ha q))
    (hbXiPeierlsUnitSourceFECocycle_ne_zero q)

/-- Exact FZZ-P information-force image of the reflected source-FE clock coefficient. -/
theorem hbXiPeierlsClockDefectCoefficient_transduces_fzzInformationForce
    (n : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    hbXiPeierlsClockToChiralSourceTransducer amplitude q *
        hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q =
      -(hbXiPhaseSensitiveChiralWardMultiplier amplitude q /
          (fzzCigarParityDeningerInformationWardMultiplier
            (deningerDivisorThetaEigen q).re : ℂ)) *
        ((fzzCigarParityReflectedFermiInformationForce
          (deningerDivisorThetaEigen q).re : ℝ) : ℂ) := by
  rw [← d4BMMixedHorizonOpticalSourceProjection_eq_clockTransducer_mul_defectCoefficient
      (n := n) (orthogonalMixing := orthogonalMixing),
    d4BMMixedHorizonOpticalSourceProjection_eq_fzzInformationRatio_mul_force]

/-- Exact PW-B recoil-grade image of the reflected source-FE clock coefficient. -/
theorem hbXiPeierlsClockDefectCoefficient_transduces_pwImbalance
    (n : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) (k : ℕ) :
    hbXiPeierlsClockToChiralSourceTransducer amplitude q *
        hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q =
      -(hbXiPhaseSensitiveChiralWardMultiplier amplitude q /
          (schwarzschildParikhWilczekDeningerWardMultiplier k : ℂ)) *
        ((schwarzschildParikhWilczekBorelPartnerRealImbalance
          (deningerDivisorThetaEigen q) k : ℝ) : ℂ) := by
  rw [← d4BMMixedHorizonOpticalSourceProjection_eq_clockTransducer_mul_defectCoefficient
      (n := n) (orthogonalMixing := orthogonalMixing),
    d4BMMixedHorizonOpticalSourceProjection_eq_pwRatio_mul_imbalance]

/-- Exact RBH multiplicity-leading image of the reflected source-FE clock coefficient. -/
theorem hbXiPeierlsClockDefectCoefficient_transduces_rbhImbalance
    (n : ℕ) (amplitude orthogonalMixing : ℂ) (rho : XiDivisorSupport) :
    hbXiPeierlsClockToChiralSourceTransducer amplitude
          (reflectedBiHeatFirstDivisorCopy rho) *
        hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n
          (reflectedBiHeatFirstDivisorCopy rho) =
      -(2 * hbXiPhaseSensitiveChiralWardMultiplier amplitude
          (reflectedBiHeatFirstDivisorCopy rho) /
          (reflectedBiHeatMultiplicityInformationWardMultiplier rho : ℂ)) *
        ((reflectedBiHeatMultiplicityLeadingJetNormImbalance rho : ℝ) : ℂ) := by
  rw [← d4BMMixedHorizonOpticalSourceProjection_eq_clockTransducer_mul_defectCoefficient
      (n := n) (orthogonalMixing := orthogonalMixing),
    d4BMMixedHorizonOpticalSourceProjection_eq_rbhRatio_mul_imbalance]

/-- For nonzero seed, clock-coefficient extinction is exactly physical chiral-source darkness. -/
theorem hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff_chiralSource
    (n : ℕ) {amplitude : ℂ} (ha : amplitude ≠ 0)
    (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q = 0 ↔
      d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q = 0 := by
  rw [d4BMMixedHorizonOpticalSourceProjection_eq_clockTransducer_mul_defectCoefficient
      (n := n),
    mul_eq_zero]
  simp [hbXiPeierlsClockToChiralSourceTransducer_ne_zero ha q]

/-- The common clock/source charge vanishes exactly on the critical line. -/
theorem hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hItilt | hk
    · have htilt : ((((q.1 : ℂ).re - 1 / 2 : ℝ) : ℂ)) = 0 :=
        (mul_eq_zero.mp hItilt).resolve_left Complex.I_ne_zero
      have hreal := congrArg Complex.re htilt
      norm_num at hreal
      linarith
    · exact False.elim (hbXiPeierlsUnitSourceFECocycle_ne_zero q hk)
  · intro h
    rw [h]
    norm_num

/-- Universal extinction of reflected clock coefficients is equivalent to RH. -/
theorem forall_hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    exact (hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff n q).mp (h q)
  · intro hRH q
    apply (hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff n q).mpr
    exact (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp
      ((forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr hRH q)

/-- Universal clock extinction is exactly universal physical chiral-source cancellation. -/
theorem forall_hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff_chiralCancellation
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q = 0) ↔
      HBXiPhaseSensitiveChiralWardAmplitudeCancellation := by
  constructor
  · intro h q
    rw [d4BMMixedHorizonOpticalSourceProjection_eq_clockTransducer_mul_defectCoefficient
      (n := n), h q, mul_zero]
  · intro h q
    exact
      (hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff_chiralSource
        n (by norm_num) 0 q).mpr (h q)

end

end RHTower
