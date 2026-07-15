import GaloisForLFunctions.RHTower.SoninCoupledBernsteinCollarQuantumDischarge
import GaloisForLFunctions.HTGeometry.OperatorFredholmGerm

/-!
# The normalized coupled-Sonin determinant defect behind the unit collar

The coupled Bernstein mismatch is not an auxiliary distance with an unspecified meaning.  By
linearity of the moment functional it is exactly the Bernstein purity of the moment defect
between the endpoint prime--Gamma source and the normalized trace coordinates of the actual
coupled Sonin master effect.

After division by the degree, those trace coordinates are precisely the logarithmic coefficients
of the degree-one normalized Fredholm determinant germ.  Thus the open collar estimate is an
estimate on the logarithmic derivative of one concrete relative spectral determinant, not merely
a condition known to imply RH.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open HTGeometry

/-- Bernstein evaluation is linear in the source moment sequence. -/
theorem bernsteinCoefficient_sub_sequence
    (m q : ℕ → ℝ) (n i : ℕ) :
    bernsteinCoefficient (fun k => m k - q k) n i =
      bernsteinCoefficient m n i - bernsteinCoefficient q n i := by
  simp only [bernsteinCoefficient, momentFunctional, Polynomial.sum_def]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The squared distance of two Bernstein packets is the purity of their moment difference. -/
theorem bernsteinCoefficientSquareDiscrepancy_eq_purity_sub_sequence
    (m q : ℕ → ℝ) (n : ℕ) :
    bernsteinCoefficientSquareDiscrepancy m q n =
      bernsteinCoefficientPurity (fun k => m k - q k) n := by
  rw [bernsteinCoefficientSquareDiscrepancy, bernsteinCoefficientPurity]
  apply Finset.sum_congr rfl
  intro i _
  rw [bernsteinCoefficient_sub_sequence]

/-- The exact endpoint-minus-Sonin moment defect. -/
def soninCoupledEndpointMomentDefect
    (a : SoninCoupledNondegenerateAperture) (k : ℕ) : ℝ :=
  radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment k -
    soninCoupledNormalizedReplicaMoment a.1 k

/-- The concrete mismatch is exactly the Bernstein purity of the endpoint-minus-source defect. -/
theorem soninCoupledEndpointBernsteinMismatch_eq_defectPurity
    (a : SoninCoupledNondegenerateAperture) (n : ℕ) :
    soninCoupledEndpointBernsteinMismatch a n =
      bernsteinCoefficientPurity (soninCoupledEndpointMomentDefect a) n := by
  simpa only [soninCoupledEndpointBernsteinMismatch,
    soninCoupledEndpointMomentDefect] using
    bernsteinCoefficientSquareDiscrepancy_eq_purity_sub_sequence
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment)
      (soninCoupledNormalizedReplicaMoment a.1) n

/-- The coefficient of `z^(k+1)` in the positive logarithmic exponent attached to a moment
sequence.  The corresponding determinant has the negative of this exponent. -/
def normalizedFredholmExponentCoefficient (m : ℕ → ℝ) (k : ℕ) : ℝ :=
  m k / (k + 1 : ℝ)

/-- The actual degree-one Fredholm determinant germ of the coupled Sonin master effect, with the
spectral variable divided by the trace mass.  Nondegeneracy makes this normalization genuine. -/
def soninCoupledNormalizedSpectralDeterminant
    (a : SoninCoupledNondegenerateAperture) (z : ℂ) : ℂ :=
  operatorFredholmDet1Germ (soninAllPrimeCoupledCoordinateEnergy a.1)
    (z / ((soninAllPrimeCoupledTraceMoment a.1 0).re : ℂ))

/-- The normalized determinant germ is nonvanishing: it is a product of exponential germs. -/
theorem soninCoupledNormalizedSpectralDeterminant_ne_zero
    (a : SoninCoupledNondegenerateAperture) (z : ℂ) :
    soninCoupledNormalizedSpectralDeterminant a z ≠ 0 := by
  simp only [soninCoupledNormalizedSpectralDeterminant,
    operatorFredholmDet1Germ, operatorFredholmDet2Germ]
  exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

/-- **Local determinant-divisor blindness.**  Multiplication by the normalized positive-source
determinant germ cannot add, remove, or move a zero of any scalar endpoint determinant. -/
theorem mul_soninCoupledNormalizedSpectralDeterminant_eq_zero_iff
    (a : SoninCoupledNondegenerateAperture) (F : ℂ → ℂ) (z : ℂ) :
    F z * soninCoupledNormalizedSpectralDeterminant a z = 0 ↔ F z = 0 := by
  rw [mul_eq_zero]
  simp only [soninCoupledNormalizedSpectralDeterminant_ne_zero a z, or_false]

/-- Logarithmic exponent coefficient of the normalized coupled spectral determinant. -/
def soninCoupledNormalizedSpectralExponentCoefficient
    (a : SoninCoupledNondegenerateAperture) (k : ℕ) : ℝ :=
  normalizedFredholmExponentCoefficient
    (soninCoupledNormalizedReplicaMoment a.1) k

/-- The determinant coefficient is the normalized trace of the actual coupled master effect,
divided by its degree. -/
theorem soninCoupledNormalizedSpectralExponentCoefficient_eq_trace
    (a : SoninCoupledNondegenerateAperture) (k : ℕ) :
    soninCoupledNormalizedSpectralExponentCoefficient a k =
      (soninAllPrimeCoupledTraceMoment a.1 k).re /
        ((soninAllPrimeCoupledTraceMoment a.1 0).re ^ (k + 1) * (k + 1 : ℝ)) := by
  simp only [soninCoupledNormalizedSpectralExponentCoefficient,
    normalizedFredholmExponentCoefficient,
    soninCoupledNormalizedReplicaMoment, div_div]

/-- Coefficientwise logarithmic defect between the endpoint determinant and the normalized
coupled-Sonin spectral determinant. -/
def soninCoupledRelativeNormalizedSpectralExponentCoefficient
    (a : SoninCoupledNondegenerateAperture) (k : ℕ) : ℝ :=
  normalizedFredholmExponentCoefficient
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) k -
    soninCoupledNormalizedSpectralExponentCoefficient a k

/-- Applying the logarithmic derivative recovers exactly the endpoint-minus-Sonin moment defect. -/
def soninCoupledRelativeNormalizedSpectralLogDerivativeMoment
    (a : SoninCoupledNondegenerateAperture) (k : ℕ) : ℝ :=
  (k + 1 : ℝ) * soninCoupledRelativeNormalizedSpectralExponentCoefficient a k

theorem soninCoupledRelativeNormalizedSpectralLogDerivativeMoment_eq_defect
    (a : SoninCoupledNondegenerateAperture) (k : ℕ) :
    soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a k =
      soninCoupledEndpointMomentDefect a k := by
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  simp only [soninCoupledRelativeNormalizedSpectralLogDerivativeMoment,
    soninCoupledRelativeNormalizedSpectralExponentCoefficient,
    soninCoupledNormalizedSpectralExponentCoefficient,
    normalizedFredholmExponentCoefficient,
    soninCoupledEndpointMomentDefect]
  field_simp

/-- **Exact determinant-defect identity.**  The source mismatch is the Bernstein purity of the
logarithmic derivative coefficients of the normalized relative determinant. -/
theorem soninCoupledEndpointBernsteinMismatch_eq_relativeDeterminantPurity
    (a : SoninCoupledNondegenerateAperture) (n : ℕ) :
    soninCoupledEndpointBernsteinMismatch a n =
      bernsteinCoefficientPurity
        (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n := by
  rw [soninCoupledEndpointBernsteinMismatch_eq_defectPurity]
  apply congrArg (fun m : ℕ → ℝ => bernsteinCoefficientPurity m n)
  funext k
  exact (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment_eq_defect a k).symm

/-- The endpoint purity is controlled directly by the normalized relative determinant defect. -/
theorem primeArchEndpointBernsteinPurity_le_two_add_two_relativeDeterminantPurity
    (a : SoninCoupledNondegenerateAperture) (n : ℕ) :
    primeArchEndpointBernsteinPurity n ≤
      2 + 2 * bernsteinCoefficientPurity
        (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n := by
  simpa only [soninCoupledEndpointBernsteinMismatch_eq_relativeDeterminantPurity] using
    primeArchEndpointBernsteinPurity_le_two_add_two_soninCoupledMismatch_quantum a n

/-- **Normalized spectral-determinant collar equivalence.**  The unit collar is exactly the
subexponential Bernstein-purity envelope for the logarithmic derivative of the concrete relative
determinant.  This is an equivalence, not merely an implication to RH. -/
theorem primeArchEndpoint_unitCollarEnvelope_iff_relativeDeterminantPurity
    (a : SoninCoupledNondegenerateAperture) :
    UnitCollarExponentialEnvelope primeArchEndpointBernsteinPurity ↔
      UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n) := by
  have hseq : soninCoupledEndpointBernsteinMismatch a = fun n =>
      bernsteinCoefficientPurity
        (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n := by
    funext n
    exact soninCoupledEndpointBernsteinMismatch_eq_relativeDeterminantPurity a n
  rw [primeArchEndpoint_unitCollarEnvelope_iff_soninCoupledMismatch_quantum a, hseq]

end

end RHTower
