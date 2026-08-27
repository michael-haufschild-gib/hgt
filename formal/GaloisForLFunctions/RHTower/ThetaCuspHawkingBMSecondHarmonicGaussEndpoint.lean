import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicGaussSummation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicRegularSolution

/-!
# Exact BM second-harmonic Gauss endpoint

The global Gauss theorem evaluates the horizon-regular `++` hypergeometric solution at the AdS
endpoint.  Exact parameter complement identities identify the quotient with the forbidden-boundary
connection coefficient, closing the endpoint normalization without analytic-continuation premises.
-/

open Complex Nat Polynomial Filter Topology Set MeasureTheory

namespace RHTower
noncomputable section

theorem d4BMCausalRadialC_sub_hypergeometricA
    (omega chi : ℂ) :
    d4BMCausalRadialC omega - d4BMCausalHypergeometricA omega chi =
      d4BMCausalRadialB omega chi := by
  simp [d4BMCausalRadialC, d4BMCausalHypergeometricA,
    d4BMCausalRadialA, d4BMCausalRadialB]
  ring

theorem d4BMCausalRadialC_sub_hypergeometricB
    (omega chi : ℂ) :
    d4BMCausalRadialC omega - d4BMCausalHypergeometricB omega chi =
      d4BMCausalRadialA omega chi := by
  simp [d4BMCausalRadialC, d4BMCausalHypergeometricB,
    d4BMCausalRadialA, d4BMCausalRadialB]
  ring

theorem d4BMPlusPlusHypergeometric_gaussGap
    (n : ℕ) (chi : ℂ) :
    d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) -
        d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi -
        d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi =
      1 / 2 := by
  have h := d4BMPlusPlusHypergeometric_exponentBalance n chi
  linear_combination -h

theorem d4BMCausalRadialA_plusPlus_ne_negNat_of_re_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (j : ℕ) :
    (j : ℂ) ≠ -d4BMCausalRadialA (d4BMCausalPlusPlusFrequency n chi) chi := by
  intro h
  have him := congrArg Complex.im h
  rw [d4BMCausalRadialA_plusPlus] at him
  norm_num [Complex.mul_im] at him
  exact hchi (by linarith)

theorem d4BMCausalRadialB_plusPlus_ne_negNat_of_re_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (j : ℕ) :
    (j : ℂ) ≠ -d4BMCausalRadialB (d4BMCausalPlusPlusFrequency n chi) chi := by
  intro h
  have him := congrArg Complex.im h
  rw [d4BMCausalRadialB_plusPlus] at him
  norm_num [Complex.mul_im] at him
  exact hchi (by linarith)

theorem tsum_d4BMPlusPlusRegularHypergeometricCoefficient_eq_forbiddenBoundaryCoefficient
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    ∑' j : ℕ, ordinaryHypergeometricCoefficient
        (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi)
        (d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi)
        (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) j =
      d4BMCausalForbiddenBoundaryCoefficient (d4BMCausalPlusPlusFrequency n chi) chi := by
  let omega := d4BMCausalPlusPlusFrequency n chi
  let a := d4BMCausalHypergeometricA omega chi
  let b := d4BMCausalHypergeometricB omega chi
  let c := d4BMCausalRadialC omega
  have hp (j : ℕ) := d4BMPlusPlusRegularHypergeometricParameters_ne_negNat n chi hchi j
  have ha : ∀ j : ℕ, (j : ℂ) ≠ -a := fun j => (hp j).1
  have hb : ∀ j : ℕ, (j : ℂ) ≠ -b := fun j => (hp j).2.1
  have hc : ∀ j : ℕ, (j : ℂ) ≠ -c := fun j => (hp j).2.2
  have hca : ∀ j : ℕ, (j : ℂ) ≠ -(c - a) := by
    intro j
    rw [d4BMCausalRadialC_sub_hypergeometricA]
    exact d4BMCausalRadialB_plusPlus_ne_negNat_of_re_ne_zero n chi hchi j
  have hcb : ∀ j : ℕ, (j : ℂ) ≠ -(c - b) := by
    intro j
    rw [d4BMCausalRadialC_sub_hypergeometricB]
    exact d4BMCausalRadialA_plusPlus_ne_negNat_of_re_ne_zero n chi hchi j
  have hgapEq : c - a - b = 1 / 2 :=
    d4BMPlusPlusHypergeometric_gaussGap n chi
  have hgap : 0 < (c - a - b).re := by
    rw [hgapEq]
    norm_num
  have hgauss := gaussSummation a b c ha hb hc hca hcb hgap
  rw [GaussSummationFormula] at hgauss
  change (∑' j : ℕ, ordinaryHypergeometricCoefficient a b c j) = _
  rw [hgauss, hgapEq, d4BMCausalRadialC_sub_hypergeometricA,
    d4BMCausalRadialC_sub_hypergeometricB]
  rw [d4BMCausalForbiddenBoundaryCoefficient]
  ring

theorem d4BMPlusPlusRegularHypergeometricSolution_one_eq_forbiddenBoundaryCoefficient
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusRegularHypergeometricSolution n chi 1 =
      d4BMCausalForbiddenBoundaryCoefficient (d4BMCausalPlusPlusFrequency n chi) chi := by
  rw [d4BMPlusPlusRegularHypergeometricSolution,
    d4BMPlusPlusRegularHypergeometricSeries,
    ordinaryHypergeometric_sum_eq]
  simp only [one_pow, smul_eq_mul, mul_one]
  change (∑' j : ℕ, ordinaryHypergeometricCoefficient
      (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi)
      (d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi)
      (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) j) = _
  exact tsum_d4BMPlusPlusRegularHypergeometricCoefficient_eq_forbiddenBoundaryCoefficient
    n chi hchi

end
end RHTower
