import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedOriginalForms
import GaloisForLFunctions.RHTower.Sieve.SelbergHigherLogOriginalAsymptotics

/-!
# Selberg forms with a minimum logarithmic factor

The omitted detector-head boundary is a finite linear combination of the forms
`A^i B^j min(A,B)^k`.  This module gives their generic original/principal convolution interface,
their swap symmetry, and exact reductions of all three omitted boundary moments.
-/

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- Original Möbius/gcd Selberg form with a minimum logarithmic monomial. -/
def selbergOriginalMinLogMonomial (i j k N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
    let A := Real.log ((N : ℝ) / (p.1 : ℝ))
    let B := Real.log ((N : ℝ) / (p.2 : ℝ))
    selbergOriginalCoeff p.1 p.2 * (A ^ i * B ^ j * min A B ^ k)

/-- Fixed-dilation principal Selberg model with a minimum logarithmic monomial. -/
def selbergPrincipalMinLogMonomialModel
    (i j k a b N : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (N / a), ∑ s ∈ Finset.Icc 1 (N / b),
    let A := Real.log ((N : ℝ) / ((a * r : ℕ) : ℝ))
    let B := Real.log ((N : ℝ) / ((b * s : ℕ) : ℝ))
    selbergPrincipalCoeff r s * (A ^ i * B ^ j * min A B ^ k)

/-- Euler-correction convolution for every minimum logarithmic monomial. -/
theorem selbergOriginalMinLogMonomial_eq_correction_principal
    (i j k N : ℕ) :
    selbergOriginalMinLogMonomial i j k N =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b *
          selbergPrincipalMinLogMonomialModel i j k a b N := by
  rw [selbergOriginalMinLogMonomial, Finset.sum_product]
  calc
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      selbergOriginalCoeff m n *
        (Real.log ((N : ℝ) / (m : ℝ)) ^ i *
          Real.log ((N : ℝ) / (n : ℝ)) ^ j *
          min (Real.log ((N : ℝ) / (m : ℝ)))
            (Real.log ((N : ℝ) / (n : ℝ))) ^ k)) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        bivariateDirichletConvolution selbergEulerCorrectionCoeff
          selbergPrincipalCoeff m n *
          (Real.log ((N : ℝ) / (m : ℝ)) ^ i *
            Real.log ((N : ℝ) / (n : ℝ)) ^ j *
            min (Real.log ((N : ℝ) / (m : ℝ)))
              (Real.log ((N : ℝ) / (n : ℝ))) ^ k) := by
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        rw [selbergEulerCorrection_convolution_principal]
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b *
          (∑ r ∈ Finset.Icc 1 (N / a), ∑ s ∈ Finset.Icc 1 (N / b),
            (selbergPrincipalCoeff r s *
              (Real.log ((N : ℝ) / ((a * r : ℕ) : ℝ)) ^ i *
                Real.log ((N : ℝ) / ((b * s : ℕ) : ℝ)) ^ j *
                min (Real.log ((N : ℝ) / ((a * r : ℕ) : ℝ)))
                  (Real.log ((N : ℝ) / ((b * s : ℕ) : ℝ))) ^ k))) :=
      sum_Icc_bivariateDirichletConvolution_mul _ _ _ N N
    _ = _ := by rfl

/-- Swapping the two logarithmic exponents leaves the original minimum form unchanged. -/
theorem selbergOriginalMinLogMonomial_comm
    (i j k N : ℕ) :
    selbergOriginalMinLogMonomial i j k N =
      selbergOriginalMinLogMonomial j i k N := by
  rw [selbergOriginalMinLogMonomial, selbergOriginalMinLogMonomial,
    Finset.sum_product, Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  rw [show selbergOriginalCoeff n m = selbergOriginalCoeff m n by
    rw [selbergOriginalCoeff, selbergOriginalCoeff, Nat.gcd_comm]
    ring,
    min_comm]
  ring

/-- The omitted base boundary is the `(1,1,1)` minimum monomial. -/
theorem selbergOriginalOmittedBaseBoundary_eq_minMonomial
    (M : ℕ) (hM : 0 < M) :
    selbergOriginalOmittedBaseBoundary M =
      selbergOriginalMinLogMonomial 1 1 1 M := by
  rw [selbergOriginalOmittedBaseBoundary_eq_min M hM,
    selbergOriginalMinLogMonomial]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The omitted base/derivative boundary as three minimum monomials. -/
theorem selbergOriginalOmittedCrossBoundary_eq_minMonomials
    (ell : ℝ) (M : ℕ) (hM : 0 < M) :
    selbergOriginalOmittedCrossBoundary ell M =
      (-ell) * selbergOriginalMinLogMonomial 1 1 1 M +
        (-1) * selbergOriginalMinLogMonomial 1 2 1 M +
          (1 / 2 : ℝ) * selbergOriginalMinLogMonomial 1 1 2 M := by
  rw [selbergOriginalOmittedCrossBoundary_eq_min ell M hM,
    selbergOriginalMinLogMonomial, selbergOriginalMinLogMonomial,
    selbergOriginalMinLogMonomial,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only
  ring

/-- The omitted derivative-square boundary as eight minimum monomials. -/
theorem selbergOriginalOmittedDerivativeBoundary_eq_minMonomials
    (ell : ℝ) (M : ℕ) (hM : 0 < M) :
    selbergOriginalOmittedDerivativeBoundary ell M =
      ell ^ (2 : ℕ) * selbergOriginalMinLogMonomial 1 1 1 M +
        ell * selbergOriginalMinLogMonomial 2 1 1 M +
        ell * selbergOriginalMinLogMonomial 1 2 1 M +
        selbergOriginalMinLogMonomial 2 2 1 M -
        ell * selbergOriginalMinLogMonomial 1 1 2 M -
        (1 / 2 : ℝ) * selbergOriginalMinLogMonomial 2 1 2 M -
        (1 / 2 : ℝ) * selbergOriginalMinLogMonomial 1 2 2 M +
        (1 / 3 : ℝ) * selbergOriginalMinLogMonomial 1 1 3 M := by
  rw [selbergOriginalOmittedDerivativeBoundary_eq_min ell M hM,
    selbergOriginalMinLogMonomial, selbergOriginalMinLogMonomial,
    selbergOriginalMinLogMonomial, selbergOriginalMinLogMonomial,
    selbergOriginalMinLogMonomial, selbergOriginalMinLogMonomial,
    selbergOriginalMinLogMonomial, selbergOriginalMinLogMonomial]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

end

end RHTower.Sieve
