import GaloisForLFunctions.RHTower.PrimeDepthWoldWall
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldRelationKernelAtlasTransition
import GaloisForLFunctions.RHTower.XiUnitDoubleEulerPhysicalTraceClassUniversalityLaw
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# BV--Wold depth-one Schatten atlas landing

This module identifies the abstract prime-depth Schatten wall with the actual logarithm of the
BV--Wold consecutive-triangle anomaly and the physical/unit-double trace-class correction.  It
then proves the operator-native conversion needed by any future source construction: a genuine
Schatten-1 operator carrying that depth-one family on injectively labelled prime diagonal slots
forces the divisor parameter onto the critical line.

No source landing or RH premise is assumed.  The source-side construction of such an operator is
kept as a separate producer obligation.
-/

namespace RHTower

noncomputable section

/-- Actual source-atlas relative logarithmic coefficient at prime `p` and Wold depth `e`. -/
def primeDepthBVWoldXiRelativeLogCoefficient
    (rho : XiDivisorSupport) (e : ℕ) (p : Nat.Primes) : ℝ :=
  Real.log (primeDepthBVWoldPrimeConsecutiveTriangleAnomaly
      (primeDepthBVWoldXiCenteredRate rho) p e) +
    xiUnitDoubleEulerPhysicalTraceRemainder p

/-- The abstract wall coefficient is exactly the positive scale in the actual BV--Wold atlas. -/
theorem primeDepthBVWoldPrimeConsecutiveTriangleLogScale_eq_woldCoeff
    (p : Nat.Primes) (e : ℕ) :
    primeDepthBVWoldPrimeConsecutiveTriangleLogScale p e = woldCoeff e p := by
  rw [primeDepthBVWoldPrimeConsecutiveTriangleLogScale, woldCoeff]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- The abstract trace-class remainder is the physical/unit-double seam coefficient. -/
theorem woldRemainder_eq_xiUnitDoubleEulerPhysicalTraceRemainder
    (p : Nat.Primes) :
    woldRemainder p = xiUnitDoubleEulerPhysicalTraceRemainder p := by
  rfl

/-- Exact coefficient conversion: actual anomaly logarithm plus physical seam equals wall family. -/
theorem primeDepthBVWoldXiRelativeLogCoefficient_eq
    (rho : XiDivisorSupport) (e : ℕ) (p : Nat.Primes) :
    primeDepthBVWoldXiRelativeLogCoefficient rho e p =
      primeDepthBVWoldXiCenteredRate rho * woldCoeff e p + woldRemainder p := by
  rw [primeDepthBVWoldXiRelativeLogCoefficient,
    primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq, Real.log_exp,
    woldCoeff, woldRemainder, xiUnitDoubleEulerPhysicalTraceRemainder]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- Exact global wall for the actual Xi-labelled relative logarithmic coefficient. -/
theorem summable_primeDepthBVWoldXiRelativeLogCoefficient_iff
    (rho : XiDivisorSupport) (e : ℕ) :
    Summable (primeDepthBVWoldXiRelativeLogCoefficient rho e) ↔
      primeDepthBVWoldXiCenteredRate rho = 0 ∨ 2 ≤ e := by
  have hfun : primeDepthBVWoldXiRelativeLogCoefficient rho e =
      fun p => primeDepthBVWoldXiCenteredRate rho * woldCoeff e p + woldRemainder p := by
    funext p
    exact primeDepthBVWoldXiRelativeLogCoefficient_eq rho e p
  rw [hfun, summable_smul_woldCoeff_add_remainder_iff]

/-- Depth one is the unique useful wall: trace-class summability is exactly criticality. -/
theorem summable_primeDepthBVWoldXiRelativeLogCoefficient_one_iff
    (rho : XiDivisorSupport) :
    Summable (primeDepthBVWoldXiRelativeLogCoefficient rho 1) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [summable_primeDepthBVWoldXiRelativeLogCoefficient_iff]
  have hnot : ¬ 2 ≤ (1 : ℕ) := by omega
  rw [or_iff_left hnot, primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/--
Operator-native cross-route bridge.  Any Schatten-1 target whose basis is prime-labelled and has
the actual depth-one source-atlas diagonal forces the corresponding Xi divisor onto the critical
line.
-/
theorem primeDepthBVWoldXi_re_eq_half_of_schattenOne_relativeLogDiagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (rho : XiDivisorSupport) (T : H →L[ℂ] H)
    (hT : MemSchattenClass 1 T)
    (b : HilbertBasis Nat.Primes ℂ H)
    (hdiag : ∀ p : Nat.Primes,
      inner ℂ (b p) (T (b p)) =
        (primeDepthBVWoldXiRelativeLogCoefficient rho 1 p : ℂ)) :
    (rho : ℂ).re = 1 / 2 := by
  have hsComplex : Summable (fun p : Nat.Primes =>
      (primeDepthBVWoldXiRelativeLogCoefficient rho 1 p : ℂ)) := by
    exact (hT.one_summable_inner_diag_basis b).congr fun p => hdiag p
  have hsReal : Summable (primeDepthBVWoldXiRelativeLogCoefficient rho 1) :=
    Complex.summable_ofReal.mp hsComplex
  exact
    (summable_primeDepthBVWoldXiRelativeLogCoefficient_one_iff rho).mp hsReal

/-- Global source-atlas depth-one summability proposition. -/
def PrimeDepthBVWoldXiDepthOneRelativeLogTraceClass : Prop :=
  ∀ rho : XiDivisorSupport,
    Summable (primeDepthBVWoldXiRelativeLogCoefficient rho 1)

/-- Global depth-one relative-log trace class is exactly RH; this is a classifier, not a proof. -/
theorem primeDepthBVWoldXiDepthOneRelativeLogTraceClass_iff_riemannHypothesis :
    PrimeDepthBVWoldXiDepthOneRelativeLogTraceClass ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hline : z.re = 1 / 2 :=
      (summable_primeDepthBVWoldXiRelativeLogCoefficient_one_iff rho).1 (h rho)
    linarith [mem_rightHalf.mp hz]
  · intro hRH rho
    exact (summable_primeDepthBVWoldXiRelativeLogCoefficient_one_iff rho).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
