import GaloisForLFunctions.RHTower.DeningerDivisorFlow
import GaloisForLFunctions.RHTower.XiGuinandWeilExplicitFormula

/-!
# Deninger's resolvent Lefschetz trace for `Spec ℤ`

`DeningerDivisorFlow` constructs the multiplicity-exact spectral target. The existing
Guinand--Weil theorem constructs the prime--archimedean source functional independently. This
file identifies the two in operator language.

For the centered generator `A = Theta - 1/2`, the trace-class relative resolvent observable is

`A⁻¹ - (A - z)⁻¹`.

Its spectral trace is an absolutely convergent sum over the divisor. On the source side it is the
continued von-Mangoldt flux minus the Gamma/boundary flux. Their equality is the resolvent form of
the arithmetic Lefschetz trace formula. On the absolute-convergence half-plane the finite-place
term is the honest von-Mangoldt Dirichlet series, so no zero data occur in its definition.

This closes the trace comparison for the regularized Cauchy test algebra. It does not construct a
prime-orbit space, a source cohomology complex, or a positive Hodge metric.
-/

noncomputable section

namespace RHTower

/-- Eigenvalue of the centered divisor generator `Theta - 1/2`. -/
def deningerDivisorCenteredThetaEigen (q : XiZeroCopy) : ℂ :=
  xiSpectralPoint q

/-- Relative resolvent eigenvalue at a centered base point. -/
def deningerDivisorRelativeResolventTerm (z : ℂ) (q : XiZeroCopy) : ℂ :=
  (deningerDivisorCenteredThetaEigen q)⁻¹ -
    (deningerDivisorCenteredThetaEigen q - z)⁻¹

@[simp]
theorem deningerDivisorRelativeResolventTerm_eq
    (z : ℂ) (q : XiZeroCopy) :
    deningerDivisorRelativeResolventTerm z q = xiRelativeResolventTerm z q :=
  rfl

/-- Multiplicity-exact relative resolvent trace of the centered divisor generator. -/
def deningerDivisorRelativeResolventTrace (z : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, deningerDivisorRelativeResolventTerm z q

theorem deningerDivisorRelativeResolventTrace_eq (z : ℂ) :
    deningerDivisorRelativeResolventTrace z = xiRelativeResolventTrace z :=
  rfl

/--
Arithmetic resolvent Lefschetz formula: the cohomological spectral trace equals the independently
defined continued prime--Gamma source trace.
-/
theorem deningerResolventLefschetzTrace
    {z : ℂ} (h : XiExplicitAdmissible z) :
    deningerDivisorRelativeResolventTrace z =
      continuedPrimeArchSourceRelativeTrace z := by
  rw [deningerDivisorRelativeResolventTrace_eq]
  exact (continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    h.re_pos h.ne_one h.zeta_ne).symm

/--
Absolute-convergence form of the arithmetic resolvent Lefschetz formula. Here the finite-place
source is the actual von-Mangoldt `LSeries`.
-/
theorem deningerResolventLefschetzTrace_primeSeries
    {z : ℂ} (hz : 1 < (1 / 2 + z * Complex.I).re) :
    deningerDivisorRelativeResolventTrace z =
      primeArchSourceRelativeTrace z := by
  rw [deningerDivisorRelativeResolventTrace_eq]
  exact (primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace hz).symm

/--
Finite resolvent test algebra: the sum of spectral traces of relative resolvents equals the same
finite combination of continued prime--Gamma source traces.
-/
theorem deningerResolventLefschetzTrace_testAlgebra
    {ι : Type*} (c z : ι → ℂ) (t : Finset ι)
    (hz : ∀ i ∈ t, XiExplicitAdmissible (z i)) :
    (∑' q : XiZeroCopy,
        ∑ i ∈ t, c i * deningerDivisorRelativeResolventTerm (z i) q) =
      ∑ i ∈ t, c i * continuedPrimeArchSourceRelativeTrace (z i) := by
  simpa [xiTestFunction, xiTestPrimeArchFunctional,
    deningerDivisorRelativeResolventTerm] using!
      xiGuinandWeilExplicitFormula c z t hz

/--
The same test-algebra trace identity on the honest Euler half-plane, with source given by the
von-Mangoldt Dirichlet series and the archimedean completion.
-/
theorem deningerResolventLefschetzTrace_testAlgebra_primeSeries
    {ι : Type*} (c z : ι → ℂ) (t : Finset ι)
    (hz : ∀ i ∈ t, 1 < (1 / 2 + z i * Complex.I).re) :
    (∑' q : XiZeroCopy,
        ∑ i ∈ t, c i * deningerDivisorRelativeResolventTerm (z i) q) =
      ∑ i ∈ t, c i * primeArchSourceRelativeTrace (z i) := by
  simpa [xiTestFunction, deningerDivisorRelativeResolventTerm] using!
    xiGuinandWeilExplicitFormula_primeSeries c z t hz

/--
Determinant/trace compatibility: away from the divisor, the relative resolvent trace is the
logarithmic derivative of the centered characteristic determinant.
-/
theorem deningerDivisorRelativeResolventTrace_eq_logDeriv
    {z : ℂ} (hz : XiC z ≠ 0) :
    deningerDivisorRelativeResolventTrace z = logDeriv XiC z := by
  rw [deningerDivisorRelativeResolventTrace_eq]
  exact (logDeriv_XiC_eq_relativeResolventTrace hz).symm

end RHTower
