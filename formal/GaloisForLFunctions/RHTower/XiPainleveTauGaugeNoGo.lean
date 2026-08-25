import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.ExpPolynomialDA
import GaloisForLFunctions.RHTower.XiHypertranscendenceUnconditional

/-!
# Differential-algebraic exclusion of the Painlevé tau bridge to Xi

Finite-dimensional isomonodromic tau-functions are differentially algebraic: their logarithmic
derivatives satisfy the algebraic Hamiltonian sigma equation.  Algebraic changes of variable and
polynomial exponential gauges preserve that class.  The proposed wild `PIII(D₆)` bridge

`xi(s) = exp(Q(s)) * E(s)`

therefore meets an unconditional obstruction when `E` is an entire differentially algebraic
carrier, because completed Xi is hypertranscendental.

This leaf records the exact Xi-side survivor and the closed bridge exclusion.  It deliberately does
not introduce an abstract model of Painlevé or irregular Riemann--Hilbert data: the paper proof
reduces every fixed-monodromy finite-dimensional tau carrier to the quantified analytic/DA class
below.
-/

namespace RHTower

open Complex Set
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

private theorem expPolynomial_analyticOnNhd (Q : Polynomial ℂ) :
    AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp (Q.eval s)) Set.univ :=
  (Bottcher.analyticOnNhd_polyEval Set.univ Q).cexp

/-- **Polynomial-gauge invariant.** Multiplication by the exponential of any complex polynomial
cannot lower completed Xi into the differential-algebraic class.  The degree is unrestricted, so
this strictly includes the quadratic gauge freedom of finite-dimensional isomonodromy. -/
theorem xi_expPolynomialGauge_hypertranscendental (Q : Polynomial ℂ) :
    Hypertranscendental (fun s => Complex.exp (Q.eval s) * xi s) := by
  intro hDA
  have hQ : AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp (Q.eval s)) Set.univ :=
    expPolynomial_analyticOnNhd Q
  have hnegQ : AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp ((-Q).eval s)) Set.univ :=
    expPolynomial_analyticOnNhd (-Q)
  have hproduct : AnalyticOnNhd ℂ
      (fun s : ℂ => Complex.exp (Q.eval s) * xi s) Set.univ :=
    hQ.mul xi_analyticOnNhd_univ
  have hcancelDA := differentiallyAlgebraic_mul hnegQ hproduct
    (differentiallyAlgebraic_exp_polynomial (-Q)) hDA
  apply xi_hypertranscendental
  simpa [Complex.exp_neg] using hcancelDA

/-- **Closed finite-dimensional bridge exclusion.** There is no entire differentially algebraic
factor `E` and no polynomial exponential gauge whose product is completed Xi.  In particular, the
paper reduction excludes every fixed-monodromy `PIII(D₆)` tau-function pulled back by
`t = s(1-s)`, including every quadratic-gauge normalization proposed in the wild-RH bridge. -/
theorem no_entire_differentiallyAlgebraic_expPolynomialBridge_to_xi :
    ¬ ∃ (Q : Polynomial ℂ) (E : ℂ → ℂ),
      AnalyticOnNhd ℂ E Set.univ ∧
      DifferentiallyAlgebraic E ∧
      ∀ s, xi s = Complex.exp (Q.eval s) * E s := by
  rintro ⟨Q, E, hE, hEDA, hbridge⟩
  have hQ : AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp (Q.eval s)) Set.univ :=
    expPolynomial_analyticOnNhd Q
  have hproductDA : DifferentiallyAlgebraic
      (fun s : ℂ => Complex.exp (Q.eval s) * E s) :=
    differentiallyAlgebraic_mul hQ hE
      (differentiallyAlgebraic_exp_polynomial Q) hEDA
  apply xi_hypertranscendental
  rw [show xi = (fun s : ℂ => Complex.exp (Q.eval s) * E s) from funext hbridge]
  exact hproductDA

end

end RHTower
