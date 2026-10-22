import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingReducedSecondOrderChiralTeukolskyGradeIncidence
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskyBackreactionReturnDeterminant

/-!
# Source-derived reduced chiral Teukolsky Jost return determinant

The exact HC62 doubled-grade Einstein--BM--helicity source is installed as the additive cross
source of the branch-resolved gravitational returned Jost channel.  At an Xi QNM the arbitrary
multiplicative horizon phase disappears, leaving a phase-sensitive Evans determinant equal to the
source-FE clock defect times two nowhere-zero transfer factors.

`[NEW] [SECOND-ORDER TEUKOLSKY SOURCE] [EVANS DETERMINANT] [CAYLEY RETURN] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Spectral extension of the HC62 reduced doubled-grade source on a fixed Xi fibre. -/
def d4ThetaReducedSecondOrderChiralTeukolskyCrossSource
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) (z : ℂ) : ℂ :=
  d4ThetaReducedSecondOrderChiralTeukolskyGradeSource amplitude mixed anti q
    (d4ThetaTeukolskyQuadraticChiralCuspWeight z)

/-- Returned Jost channel whose additive term is the actual reduced doubled-grade source. -/
def d4ThetaReducedSecondOrderChiralReturnedJost
    (amplitude mixed anti : ℂ) (q : XiZeroCopy)
    (horizonPhase : ℂ → ℂ) (omega : ℂ) : ℂ → ℂ :=
  teukolskyReturnedJostWithHorizonPhase omega horizonPhase
    (d4ThetaReducedSecondOrderChiralTeukolskyCrossSource amplitude mixed anti q)

/-- At an Xi QNM the returned Jost channel is exactly the HC62 physical source coefficient. -/
theorem d4ThetaReducedSecondOrderChiralReturnedJost_qnmPlus
    (n : ℕ) (amplitude mixed anti : ℂ) (q : XiZeroCopy)
    (horizonPhase : ℂ → ℂ) :
    d4ThetaReducedSecondOrderChiralReturnedJost amplitude mixed anti q horizonPhase
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        (xiSpectralPoint q) =
      d4ThetaReducedSecondOrderChiralTeukolskyGradeSource amplitude mixed anti q
        (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)) := by
  exact teukolskyReturnedJostWithHorizonPhase_qnmPlus n q _ _

/-- Exact source-derived Evans identity at every Xi descendant. -/
theorem d4ThetaReducedSecondOrderChiralReturnDeterminant_qnmPlus_eq
    (n : ℕ) (amplitude mixed anti : ℂ) (q : XiZeroCopy)
    (horizonPhase : ℂ → ℂ) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        (d4ThetaReducedSecondOrderChiralReturnedJost amplitude mixed anti q horizonPhase
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)))
        (xiSpectralPoint q) =
      d4ThetaReducedSecondOrderChiralTeukolskyGradeSource amplitude mixed anti q
          (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)) *
        thetaCuspHawkingHypergeometricJostMinus
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
          (xiSpectralPoint q) := by
  rw [teukolskyReturnDeterminant_qnmPlus,
    d4ThetaReducedSecondOrderChiralReturnedJost_qnmPlus]

/-- Unsquared source-FE clock factorization of the physical chiral Evans determinant. -/
theorem d4ThetaReducedSecondOrderChiralReturnDeterminant_qnmPlus_eq_clockDefect
    (j n : ℕ) (amplitude mixed anti orthogonalMixing : ℂ) (q : XiZeroCopy)
    (horizonPhase : ℂ → ℂ) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus j (xiSpectralPoint q))
        (d4ThetaReducedSecondOrderChiralReturnedJost amplitude mixed anti q horizonPhase
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus j (xiSpectralPoint q)))
        (xiSpectralPoint q) =
      hbXiPeierlsClockToChiralSourceTransducer amplitude q *
          hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q *
        thetaCuspHawkingHypergeometricJostMinus
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus j (xiSpectralPoint q))
          (xiSpectralPoint q) := by
  rw [d4ThetaReducedSecondOrderChiralReturnDeterminant_qnmPlus_eq,
    d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_eq_clockDefect
      n amplitude mixed anti orthogonalMixing q]

/-- For nonzero seed, the source-derived chiral Evans determinant is nonzero exactly off line. -/
theorem d4ThetaReducedSecondOrderChiralReturnDeterminant_qnmPlus_ne_zero_iff
    (n : ℕ) {amplitude : ℂ} (ha : amplitude ≠ 0)
    (mixed anti orthogonalMixing : ℂ) (q : XiZeroCopy)
    (horizonPhase : ℂ → ℂ) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        (d4ThetaReducedSecondOrderChiralReturnedJost amplitude mixed anti q horizonPhase
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)))
        (xiSpectralPoint q) ≠ 0 ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [teukolskyReturnDeterminant_qnmPlus_ne_zero_iff,
    d4ThetaReducedSecondOrderChiralReturnedJost_qnmPlus]
  exact d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_ne_zero_iff
    ha mixed anti orthogonalMixing q

/-- Excitation of the physical Evans return is exactly failure of doubled-weight unitarity. -/
theorem d4ThetaReducedSecondOrderChiralReturnDeterminant_ne_zero_iff_weight_nonunitary
    (n : ℕ) {amplitude : ℂ} (ha : amplitude ≠ 0)
    (mixed anti orthogonalMixing : ℂ) (q : XiZeroCopy)
    (horizonPhase : ℂ → ℂ) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        (d4ThetaReducedSecondOrderChiralReturnedJost amplitude mixed anti q horizonPhase
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)))
        (xiSpectralPoint q) ≠ 0 ↔
      (d4ThetaTeukolskyQuadraticChiralCuspWeight
        (xiSpectralPoint q)).re ≠ 1 / 2 := by
  rw [d4ThetaReducedSecondOrderChiralReturnDeterminant_qnmPlus_ne_zero_iff
      n ha mixed anti orthogonalMixing q horizonPhase,
    d4ThetaTeukolskyQuadraticChiralCuspWeight_xi_re_ne_half_iff]

/-- Universal extinction of the source-derived chiral Evans determinant is RH. -/
theorem forall_d4ThetaReducedSecondOrderChiralReturnDeterminant_qnmPlus_eq_zero_iff_rh
    (j n : ℕ) {amplitude : ℂ} (ha : amplitude ≠ 0)
    (mixed anti : ℂ) (horizonPhase : ℂ → ℂ) :
    (∀ q : XiZeroCopy,
      teukolskyReturnDeterminant
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus j (xiSpectralPoint q))
          (d4ThetaReducedSecondOrderChiralReturnedJost amplitude mixed anti q horizonPhase
            (thetaCuspHawkingTopologicalBlackHoleQNMPlus j (xiSpectralPoint q)))
          (xiSpectralPoint q) = 0) ↔
      RiemannHypothesis := by
  rw [← forall_d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_eq_zero_iff_rh
      ha n mixed anti]
  constructor
  · intro hall q
    have hdet := hall q
    rw [d4ThetaReducedSecondOrderChiralReturnDeterminant_qnmPlus_eq, mul_eq_zero] at hdet
    exact hdet.resolve_right
      (thetaCuspHawkingHypergeometricJostMinus_qnmPlus_ne_zero j q)
  · intro hall q
    rw [d4ThetaReducedSecondOrderChiralReturnDeterminant_qnmPlus_eq, hall q, zero_mul]

/-- Cayley completion of the source-derived reduced chiral return. -/
def d4ThetaReducedSecondOrderChiralReturnCayleySMatrix
    (amplitude mixed anti : ℂ) (q : XiZeroCopy)
    (horizonPhase : ℂ → ℂ) (omega z : ℂ) : ℂ :=
  teukolskyReturnCayleySMatrix omega
    (d4ThetaReducedSecondOrderChiralReturnedJost
      amplitude mixed anti q horizonPhase omega) z

/-- Exact theta-shadow inverse law for the source-derived Cayley return. -/
theorem d4ThetaReducedSecondOrderChiralReturnCayleySMatrix_shadow
    (amplitude mixed anti : ℂ) (q : XiZeroCopy)
    (horizonPhase : ℂ → ℂ) (omega z : ℂ) :
    d4ThetaReducedSecondOrderChiralReturnCayleySMatrix amplitude mixed anti q
        horizonPhase omega (thetaCuspHawkingOpticalCuspShadow z) =
      (d4ThetaReducedSecondOrderChiralReturnCayleySMatrix amplitude mixed anti q
        horizonPhase omega z)⁻¹ := by
  exact teukolskyReturnCayleySMatrix_shadow omega _ z

/-- For nonzero seed, the completed physical return is nontrivial exactly off line. -/
theorem d4ThetaReducedSecondOrderChiralReturnCayleySMatrix_qnmPlus_ne_one_iff
    (n : ℕ) {amplitude : ℂ} (ha : amplitude ≠ 0)
    (mixed anti orthogonalMixing : ℂ) (q : XiZeroCopy)
    (horizonPhase : ℂ → ℂ) :
    d4ThetaReducedSecondOrderChiralReturnCayleySMatrix amplitude mixed anti q horizonPhase
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        (xiSpectralPoint q) ≠ 1 ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  simpa [d4ThetaReducedSecondOrderChiralReturnCayleySMatrix,
    d4ThetaReducedSecondOrderChiralReturnedJost,
    d4ThetaReducedSecondOrderChiralTeukolskyCrossSource] using
      (teukolskyReturnCayleySMatrix_qnmPlus_ne_one_iff_crossSource n q horizonPhase
        (d4ThetaReducedSecondOrderChiralTeukolskyCrossSource amplitude mixed anti q)).trans
      (d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_ne_zero_iff
        ha mixed anti orthogonalMixing q)

/-- Universal triviality of the source-derived Cayley return is RH. -/
theorem forall_d4ThetaReducedSecondOrderChiralReturnCayleySMatrix_qnmPlus_eq_one_iff_rh
    (j n : ℕ) {amplitude : ℂ} (ha : amplitude ≠ 0)
    (mixed anti : ℂ) (horizonPhase : ℂ → ℂ) :
    (∀ q : XiZeroCopy,
      d4ThetaReducedSecondOrderChiralReturnCayleySMatrix amplitude mixed anti q horizonPhase
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus j (xiSpectralPoint q))
          (xiSpectralPoint q) = 1) ↔
      RiemannHypothesis := by
  rw [← forall_d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_eq_zero_iff_rh
      ha n mixed anti]
  have hpoint : ∀ q : XiZeroCopy,
      d4ThetaReducedSecondOrderChiralReturnCayleySMatrix amplitude mixed anti q horizonPhase
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus j (xiSpectralPoint q))
          (xiSpectralPoint q) = 1 ↔
        d4ThetaReducedSecondOrderChiralTeukolskyGradeSource amplitude mixed anti q
          (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)) = 0 := by
    intro q
    simpa [d4ThetaReducedSecondOrderChiralReturnCayleySMatrix,
      d4ThetaReducedSecondOrderChiralReturnedJost,
      d4ThetaReducedSecondOrderChiralTeukolskyCrossSource] using
        not_congr (teukolskyReturnCayleySMatrix_qnmPlus_ne_one_iff_crossSource j q
          horizonPhase
          (d4ThetaReducedSecondOrderChiralTeukolskyCrossSource amplitude mixed anti q))
  constructor
  · intro hall q
    exact (hpoint q).mp (hall q)
  · intro hall q
    exact (hpoint q).mpr (hall q)

end

end RHTower
