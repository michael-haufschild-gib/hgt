import GaloisForLFunctions.HTGeometry.DifferentialRelationSigmaDescent

/-!
# Semilinear evaluation of differential polynomials

Evaluation is natural under a differential automorphism which normalizes, rather than fixes, the
coefficient field: coefficients are shifted and the evaluation point is shifted simultaneously.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {iota K R : Type*} [Field K] [CommRing R] [Algebra K R]
  [Differential K] [Differential R]

/-- Differential-polynomial evaluation under simultaneous coefficient and point transport. -/
theorem differentialPolynomialEvalOver_sigma_point
    (sigmaK : K ≃+* K) (sigmaR : R ≃+* R)
    (hcompat : ∀ a : K, sigmaR (algebraMap K R a) = algebraMap K R (sigmaK a))
    (hsigmaDeriv : ∀ z : R,
      sigmaR (Differential.deriv z) = Differential.deriv (sigmaR z))
    (x : iota → R) (P : DifferentialPolynomial iota K) :
    differentialPolynomialEvalOver (K := K) (fun j => sigmaR (x j))
        (differentialPolynomialSigma sigmaK P) =
      sigmaR (differentialPolynomialEvalOver (K := K) x P) := by
  have hjet : ∀ (n : ℕ) (j : iota),
      sigmaR (differentialJet n (x j)) =
        differentialJet n (sigmaR (x j)) := by
    intro n j
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [differentialJet_succ, hsigmaDeriv, ih, differentialJet_succ]
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [differentialPolynomialSigma_C,
        differentialPolynomialEvalOver_C,
        differentialPolynomialEvalOver_C, hcompat]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P q hP =>
      rw [map_mul, differentialPolynomialSigma_X, map_mul, hP, map_mul, map_mul,
        differentialPolynomialEvalOver_X, differentialPolynomialEvalOver_X, hjet]

/-- Iterated simultaneous coefficient and point transport. -/
theorem differentialPolynomialEvalOver_sigma_point_iterate
    (sigmaK : K ≃+* K) (sigmaR : R ≃+* R)
    (hcompat : ∀ a : K, sigmaR (algebraMap K R a) = algebraMap K R (sigmaK a))
    (hsigmaDeriv : ∀ z : R,
      sigmaR (Differential.deriv z) = Differential.deriv (sigmaR z))
    (x : iota → R) (P : DifferentialPolynomial iota K) (m : ℕ) :
    differentialPolynomialEvalOver (K := K)
        (fun j => ((sigmaR : R → R)^[m]) (x j))
        (((differentialPolynomialSigma sigmaK :
          DifferentialPolynomial iota K → DifferentialPolynomial iota K)^[m]) P) =
      ((sigmaR : R → R)^[m])
        (differentialPolynomialEvalOver (K := K) x P) := by
  induction m with
  | zero => rfl
  | succ m hm =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hstep := differentialPolynomialEvalOver_sigma_point sigmaK sigmaR
        hcompat hsigmaDeriv
        (fun j => ((sigmaR : R → R)^[m]) (x j))
        (((differentialPolynomialSigma sigmaK :
          DifferentialPolynomial iota K → DifferentialPolynomial iota K)^[m]) P)
      rw [hm] at hstep
      rw [show (fun j => ((sigmaR : R → R)^[m + 1]) (x j)) =
          (fun j => sigmaR (((sigmaR : R → R)^[m]) (x j))) by
        funext j
        rw [Function.iterate_succ_apply']]
      exact hstep

end

end GaloisForLFunctions.HTGeometry
