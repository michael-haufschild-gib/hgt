import GaloisForLFunctions.RHTower.ThetaCuspHawkingTargetIndependentFullCokernelPeierlsRealization
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFinitePhysicalClockStepCovarianceRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEClockChiralAmplitudeTransduction

/-!
# Total third-order BM cokernel/source-clock transduction

Let `K_n(q)` be the complete target-independent retarded-minus-advanced `++-` cokernel orbit and
let `D_n(q)` be the literal source-FE centered-QNM clock-defect coefficient.  The two quantities
were previously independent RH receivers.  Here they are identified coefficient-exactly:

`K_n(q) = -Sigma_n(q) * normSq(D_n(q))`,

where `Sigma_n(q)` is explicit and strictly positive on every actual Xi fibre.  No tilt is divided
out: the only denominator is the squared norm of the nowhere-zero literal source cocycle.  Thus the
identity is regular on the critical wall.

This closes the invariant source-to-clock bridge for HB.  The remaining dynamical burden is a
single sign: any physical Einstein--Teukolsky argument orienting the complete causal orbit
nonnegatively forces its already-proved nonpositive clock-defect energy to vanish.  Fibrewise this
is exactly covariance of one unit physical-clock step; globally it is RH.

Because `K_n` is the total causal cut, the result is independent of the common direct third
Einstein jet and of field-redefinition-dependent AIME/cascade channel coordinates.

`[NEW] [TOTAL COKERNEL] [SOURCE-CLOCK TRANSDUCTION] [POSITIVE FACTORIZATION] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Strictly positive conversion from squared source-FE clock defect to the complete third-order
BM cokernel orbit.  Its denominator never vanishes, including on the critical wall. -/
def hbXiPeierlsClockDefectToFullCokernelSusceptibility
    (n : ℕ) (q : XiZeroCopy) : ℝ :=
  4 * d4BMXiHBOpticalPowerToPeierlsOrbitSusceptibility n q *
      hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier n q /
    Complex.normSq (hbXiPeierlsUnitSourceFECocycle q)

theorem hbXiPeierlsClockDefectToFullCokernelSusceptibility_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < hbXiPeierlsClockDefectToFullCokernelSusceptibility n q := by
  unfold hbXiPeierlsClockDefectToFullCokernelSusceptibility
  exact div_pos
    (mul_pos
      (mul_pos (by norm_num)
        (d4BMXiHBOpticalPowerToPeierlsOrbitSusceptibility_pos n q))
      (hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier_pos n q))
    (Complex.normSq_pos.mpr (hbXiPeierlsUnitSourceFECocycle_ne_zero q))

/-- The infinitesimal reflected source-clock energy is exactly tilt squared times literal source
cocycle energy. -/
theorem normSq_hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq
    (n : ℕ) (q : XiZeroCopy) :
    Complex.normSq
        (hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q) =
      ((q.1 : ℂ).re - 1 / 2) ^ 2 *
        Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) := by
  rw [hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq]
  norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- Exact total-source transduction: the complete target-independent third-order cokernel orbit is
the negative of a strictly positive coefficient times source-FE clock-defect energy. -/
theorem hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_neg_clockDefectEnergy
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q =
      -((hbXiPeierlsClockDefectToFullCokernelSusceptibility n q *
        Complex.normSq
          (hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q) : ℝ) : ℂ) := by
  rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_neg_hbOpticalPower,
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_wardEnergyMultiplier_mul_charge_sq,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq,
    normSq_hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq]
  unfold hbXiPeierlsClockDefectToFullCokernelSusceptibility
  have hk : Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr (hbXiPeierlsUnitSourceFECocycle_ne_zero q))
  simp only [deningerDivisorThetaEigen, ofReal_re]
  push_cast
  field_simp [hk]
  ring

/-- Complete causal-orbit extinction is exactly extinction of the literal source-clock defect. -/
theorem hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_zero_iff_clockDefect
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q = 0 ↔
      hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q = 0 := by
  rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_neg_clockDefectEnergy]
  have hSigma : hbXiPeierlsClockDefectToFullCokernelSusceptibility n q ≠ 0 :=
    ne_of_gt (hbXiPeierlsClockDefectToFullCokernelSusceptibility_pos n q)
  simp [hSigma]

/-- Fibrewise source-to-finite-time bridge: total third-order causal-orbit extinction is exactly
covariance of one source-predeclared unit physical-clock step. -/
theorem hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_zero_iff_unitClockStep
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q = 0 ↔
      hbXiPeierlsUnitSourceFEPacketTransport
          (hbXiPeierlsCenteredQNMPhysicalClockStep 0 1 (Finsupp.single q 1)) =
        hbXiPeierlsCenteredQNMPhysicalClockStep 0 1
          (hbXiPeierlsUnitSourceFEPacketTransport (Finsupp.single q 1)) := by
  rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_zero_iff_clockDefect,
    hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff,
    hbXiPeierlsUnitSourceFEPhysicalClockStep_single_commute_iff]
  norm_num

/-- Global source-to-finite-time bridge: universal complete-cokernel extinction is exactly one
unit physical-clock covariance law, and therefore exactly RH. -/
theorem forall_hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_zero_iff_unitClockStepCovariant
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q = 0) ↔
      HBXiPeierlsUnitSourceFEPhysicalClockStepCovariant 0 1 :=
  (forall_hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_zero_iff_rh n).trans
    hbXiPeierlsUnitSourceFEUnitPhysicalClockStepCovariant_iff_rh.symm

end

end RHTower
