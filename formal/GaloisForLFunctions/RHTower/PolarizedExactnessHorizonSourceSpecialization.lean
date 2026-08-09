import GaloisForLFunctions.RHTower.ArithmeticXiStokesCentralRankPort

/-!
# Exact source specialization of the polarized horizon law

The literal rational-adelic ordinary-prime cycle has trace one.  This file packages the already
constructed Xi paracyclic residue in the completed-local form `(q - 1)c`, retaining the oriented
unsquared factor and its nonzero first Xi-jet coefficient.
-/

namespace RHTower

noncomputable section

/-- Actual positive central source parameter on the ordinary-prime Xi landing. -/
def polarizedXiSourceParameter (n : ℕ) (rho : XiDivisorSupport) : ℝ :=
  deningerHalfDensityMateGain n (rho : ℂ)

/-- Actual nonzero first Xi-jet coefficient multiplying the oriented defect. -/
def polarizedXiSourceCoefficient (rho : XiDivisorSupport) : ℂ :=
  thetaInternalJetLeadingSourceCoefficient rho

/-- Literal source residue of the landed paracyclic equivariance defect on the trace-one
ordinary-prime atom. -/
def polarizedXiPrimeSourceResidue
    (n : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) : ℂ :=
  ccmRationalAdelicTwoLegCyclicResidue
    (GaloisForLFunctions.HTGeometry.cyclicParacyclicEquivarianceDefect
      ccmRationalAdelicDegreeOneCyclicRotation
      (sourceDaggerNormalizedDegreeOneRotationLinear n (rho : ℂ))
      (ccmMobiusThetaXiJetTwoLegLanding
        (xiSupportMultiplicity rho) (xiSpectralPointSupport rho))
      (ccmRationalAdelicOrdinaryPrimeCycleAtom p))

/-- The source parameter is strictly positive, hence nonzero. -/
theorem polarizedXiSourceParameter_pos (n : ℕ) (rho : XiDivisorSupport) :
    0 < polarizedXiSourceParameter n rho :=
  deningerHalfDensityMateGain_pos n (rho : ℂ)

/-- The first Xi-jet coefficient carried by the source is nonzero. -/
theorem polarizedXiSourceCoefficient_ne_zero (rho : XiDivisorSupport) :
    polarizedXiSourceCoefficient rho ≠ 0 :=
  thetaInternalJetLeadingSourceCoefficient_ne_zero rho

/-- Exact source residue formula `(5.4)`: on every literal ordinary-prime trace-one atom the
landed defect is `(q-1)c`, with no norm or square applied. -/
theorem polarizedXiPrimeSourceResidue_eq_sub_one_mul
    (n : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    polarizedXiPrimeSourceResidue n rho p =
      ((polarizedXiSourceParameter n rho : ℂ) - 1) *
        polarizedXiSourceCoefficient rho := by
  rw [polarizedXiPrimeSourceResidue,
    GaloisForLFunctions.IrregularStokes.ccmXiPrimeResidue_eq_centralHolonomyDefect]
  rfl

/-- Because the retained coefficient is nonzero, the oriented source residue vanishes exactly
when the unsquared source parameter is the identity. -/
theorem polarizedXiPrimeSourceResidue_eq_zero_iff
    (n : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    polarizedXiPrimeSourceResidue n rho p = 0 ↔
      polarizedXiSourceParameter n rho = 1 := by
  rw [polarizedXiPrimeSourceResidue_eq_sub_one_mul,
    mul_eq_zero, or_iff_left (polarizedXiSourceCoefficient_ne_zero rho)]
  exact_mod_cast sub_eq_zero

/-- Reflected positive Stokes energy of the actual source parameter. -/
def polarizedXiPositiveStokesEnergy (n : ℕ) (rho : XiDivisorSupport) : ℝ :=
  polarizedXiSourceParameter n rho +
    (polarizedXiSourceParameter n rho)⁻¹ - 2

/-- Exact doubled-amplitude identity for the actual source parameter. -/
theorem polarizedXiPositiveStokesEnergy_eq_square_div
    (n : ℕ) (rho : XiDivisorSupport) :
    polarizedXiPositiveStokesEnergy n rho =
      (polarizedXiSourceParameter n rho - 1) ^ 2 /
        polarizedXiSourceParameter n rho := by
  have hq : polarizedXiSourceParameter n rho ≠ 0 :=
    (polarizedXiSourceParameter_pos n rho).ne'
  unfold polarizedXiPositiveStokesEnergy
  field_simp [hq]
  ring

end

end RHTower
