import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualLaplaceRenormalization
import GaloisForLFunctions.RHTower.SquarefreeCarlemanLogExpansion

/-!
# Prime-zeta symbol of the Route-T Wold Laplace current

The depth-one Wold Euler factor is the cubic finite difference `(1-p⁻¹)^3`.  After Laplace
rotation, its complete prime current is therefore exactly the four-shift finite difference of the
first prime-zeta trace.  Combined with the residual renormalization theorem, this identifies the
safe Route-T carrier as

`(-P'(s+1) + 3P'(s+2) - 3P'(s+3) + P'(s+4)) - mesh(s) - holonomy(s)`.

Thus the Wold side of the physical upper-half-shift problem is an explicit shifted prime-zeta
continuation problem, not an unspecified oscillatory series.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Laplace rotation of a prime-log phase is the corresponding prime-zeta eigenvalue. -/
theorem xiHeatCassiniOrderedPrimeLaplacePhase_eq_coronaPrimeEigenvalue
    (N : ℕ) (s : ℂ) :
    xiHeatCassiniOrderedPrimeLaplacePhase N s =
      coronaPrimeEigenvalue s (nthPrimeSubtype N) := by
  have hp0 : (((nthPrimeSubtype N : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (nthPrimeSubtype N).prop.ne_zero
  rw [xiHeatCassiniOrderedPrimeLaplacePhase,
    xiHeatCassiniOrderedPrimeComplexNegativePhase, coronaPrimeEigenvalue,
    Complex.cpow_def_of_ne_zero hp0, Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- Prime-zeta eigenvalues multiply under spectral translation. -/
theorem coronaPrimeEigenvalue_add_nat
    (s : ℂ) (k : ℕ) (p : Nat.Primes) :
    coronaPrimeEigenvalue (s + k) p =
      coronaPrimeEigenvalue s p * (((p : ℕ) : ℂ)⁻¹) ^ k := by
  have hp0 : (((p : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr p.prop.ne_zero
  rw [coronaPrimeEigenvalue, coronaPrimeEigenvalue,
    show -(s + (k : ℂ)) = -s + -(k : ℂ) by ring,
    Complex.cpow_add _ _ hp0, Complex.cpow_neg,
    Complex.cpow_natCast, inv_pow]

/-- The cubic Wold Euler depletion is the four-shift finite difference of one prime trace. -/
theorem woldCoeff_one_mul_coronaPrimeEigenvalue_eq_fourShift
    (s : ℂ) (p : Nat.Primes) :
    (woldCoeff 1 p : ℂ) * coronaPrimeEigenvalue s p =
      (Real.log (p : ℝ) : ℂ) * coronaPrimeEigenvalue (s + 1) p -
        3 * ((Real.log (p : ℝ) : ℂ) * coronaPrimeEigenvalue (s + 2) p) +
        3 * ((Real.log (p : ℝ) : ℂ) * coronaPrimeEigenvalue (s + 3) p) -
        (Real.log (p : ℝ) : ℂ) * coronaPrimeEigenvalue (s + 4) p := by
  have hp0R : (p : ℝ) ≠ 0 := by positivity
  have hp0C : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp0R
  rw [coronaPrimeEigenvalue_add_nat s 1 p,
    coronaPrimeEigenvalue_add_nat s 2 p,
    coronaPrimeEigenvalue_add_nat s 3 p,
    coronaPrimeEigenvalue_add_nat s 4 p,
    woldCoeff]
  push_cast
  field_simp [hp0C]
  ring

/-- Ordered Wold current is the all-prime current under the canonical prime enumeration. -/
theorem xiHeatCassiniWoldLaplaceCurrent_eq_prime_tsum
    (s : ℂ) :
    xiHeatCassiniWoldLaplaceCurrent s =
      ∑' p : Nat.Primes,
        (woldCoeff 1 p : ℂ) * coronaPrimeEigenvalue s p := by
  rw [xiHeatCassiniWoldLaplaceCurrent]
  calc
    (∑' N : ℕ, xiHeatCassiniWoldLaplaceAtom s N) =
        ∑' N : ℕ,
          (woldCoeff 1 (nthPrimeSubtype N) : ℂ) *
            coronaPrimeEigenvalue s (nthPrimeSubtype N) := by
      apply tsum_congr
      intro N
      rw [xiHeatCassiniWoldLaplaceAtom,
        xiHeatCassiniOrderedPrimeLaplacePhase_eq_coronaPrimeEigenvalue]
    _ = _ := by
      simpa only [nthPrimeEquiv_apply] using
        nthPrimeEquiv.tsum_eq
          (fun p : Nat.Primes =>
            (woldCoeff 1 p : ℂ) * coronaPrimeEigenvalue s p)

/-- **Exact Wold prime-zeta symbol.**  On `Re s > 0`, depth-one Wold current is a cubic finite
difference of the derivative of the prime-zeta defect. -/
theorem xiHeatCassiniWoldLaplaceCurrent_eq_primeZetaDerivFourShift
    {s : ℂ} (hs : 0 < s.re) :
    xiHeatCassiniWoldLaplaceCurrent s =
      -deriv coronaPrimeZeta (s + 1) +
        3 * deriv coronaPrimeZeta (s + 2) -
        3 * deriv coronaPrimeZeta (s + 3) +
        deriv coronaPrimeZeta (s + 4) := by
  have hs1 : 1 < (s + 1).re := by simp; linarith
  have hs2 : 1 < (s + 2).re := by simp; linarith
  have hs3 : 1 < (s + 3).re := by simp; linarith
  have hs4 : 1 < (s + 4).re := by simp; linarith
  have h1 := hasSum_neg_deriv_coronaPrimeZeta hs1
  have h2 := hasSum_neg_deriv_coronaPrimeZeta hs2
  have h3 := hasSum_neg_deriv_coronaPrimeZeta hs3
  have h4 := hasSum_neg_deriv_coronaPrimeZeta hs4
  have hcomb := ((h1.sub (h2.mul_left (3 : ℂ))).add
    (h3.mul_left (3 : ℂ))).sub h4
  have hwold : HasSum
      (fun p : Nat.Primes =>
        (woldCoeff 1 p : ℂ) * coronaPrimeEigenvalue s p)
      ((-deriv coronaPrimeZeta (s + 1) -
          3 * (-deriv coronaPrimeZeta (s + 2))) +
        3 * (-deriv coronaPrimeZeta (s + 3)) -
          (-deriv coronaPrimeZeta (s + 4))) := by
    refine hcomb.congr_fun ?_
    intro p
    exact (woldCoeff_one_mul_coronaPrimeEigenvalue_eq_fourShift s p).symm
  rw [xiHeatCassiniWoldLaplaceCurrent_eq_prime_tsum]
  exact hwold.tsum_eq.trans (by ring)

/-- **Prime-zeta/mesh normal form of the residual Hardy carrier.** -/
theorem xiHeatCassiniWoldResidualLowerHardyKernel_negI_mul_eq_primeZeta_sub_mesh
    {s : ℂ} (hs : 0 < s.re) :
    xiHeatCassiniWoldResidualLowerHardyKernel (-Complex.I * s) =
      (-deriv coronaPrimeZeta (s + 1) +
          3 * deriv coronaPrimeZeta (s + 2) -
          3 * deriv coronaPrimeZeta (s + 3) +
          deriv coronaPrimeZeta (s + 4)) -
        xiHeatCassiniLogMeshLaplaceCurrent s -
        ((xiMassNthPrimeLogHeight 0 + xiHeatCassiniWoldLogHolonomyConstant : ℝ) : ℂ) *
          xiHeatCassiniOrderedPrimeLaplacePhase 0 s := by
  rw [xiHeatCassiniWoldResidualLowerHardyKernel_negI_mul_eq_renormalizedLaplace hs,
    xiHeatCassiniWoldLaplaceCurrent_eq_primeZetaDerivFourShift hs]

/-- Rotation dictionary: the physical upper half-shift is exactly the critical Laplace wall
`Re s = -1/2`. -/
theorem re_I_mul_upperHalfShift (x : ℝ) :
    (Complex.I * ((x : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)).re = -1 / 2 := by
  simp [Complex.mul_re]
  ring

end

end RHTower
