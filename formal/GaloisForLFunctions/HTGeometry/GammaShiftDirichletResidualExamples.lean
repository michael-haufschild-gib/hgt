import GaloisForLFunctions.HTGeometry.GammaShiftAugmentedDeterminant

open scoped BigOperators Matrix
namespace GaloisForLFunctions
open Polynomial Filter LSeries
noncomputable section

def singletonGammaShift (lambda : ℂ) : Fin 1 → ℂ := fun _ => lambda
def singletonGammaMult : Fin 1 → ℕ := fun _ => 1

theorem gammaJetOrder_singleton : gammaJetOrder singletonGammaMult = 1 := by
  simp [gammaJetOrder, singletonGammaMult]

theorem gammaJetAnnihilatorCoeff_singleton_zero (s lambda : ℂ) :
    gammaJetAnnihilatorCoeff s (singletonGammaShift lambda) singletonGammaMult 0 =
      -(s + lambda) := by
  rw [gammaJetAnnihilatorCoeff, gammaJetRootPolynomial_zeroCoeff]
  simp [gammaJetOrder_singleton, singletonGammaShift, singletonGammaMult]

theorem gammaJetAnnihilator_singleton (s lambda : ℂ) (f : ℂ → ℂ) :
    gammaJetAnnihilator s (singletonGammaShift lambda) singletonGammaMult f =
      f (s + 1) - (s + lambda) * f s := by
  rw [gammaJetAnnihilator_eq_monic]
  rw [gammaJetOrder_singleton]
  rw [Finset.sum_range_one]
  rw [gammaJetAnnihilatorCoeff_singleton_zero]
  simp
  ring

def pairGammaShift (lambda1 lambda2 : ℂ) : Fin 2 → ℂ :=
  Fin.cases lambda1 (fun _ => lambda2)

@[simp] theorem pairGammaShift_zero (lambda1 lambda2 : ℂ) :
    pairGammaShift lambda1 lambda2 0 = lambda1 := rfl

@[simp] theorem pairGammaShift_one (lambda1 lambda2 : ℂ) :
    pairGammaShift lambda1 lambda2 1 = lambda2 := rfl

def pairGammaMult : Fin 2 → ℕ := fun _ => 1

theorem gammaJetOrder_pair : gammaJetOrder pairGammaMult = 2 := by
  simp [gammaJetOrder, pairGammaMult]

theorem gammaJetAnnihilatorCoeff_pair_zero (s lambda1 lambda2 : ℂ) :
    gammaJetAnnihilatorCoeff s (pairGammaShift lambda1 lambda2) pairGammaMult 0 =
      (s + lambda1) * (s + lambda2) := by
  rw [gammaJetAnnihilatorCoeff, gammaJetRootPolynomial_zeroCoeff]
  simp only [gammaJetOrder_pair, pairGammaMult, pow_one,
    Fin.prod_univ_two, pairGammaShift_zero, pairGammaShift_one, pow_two]
  ring

theorem gammaJetAnnihilatorCoeff_pair_one (s lambda1 lambda2 : ℂ) :
    gammaJetAnnihilatorCoeff s (pairGammaShift lambda1 lambda2) pairGammaMult 1 =
      -(2 * s + lambda1 + lambda2 + 1) := by
  have hexp := gammaJetRootPolynomial_expansion ℂ s
    (pairGammaShift lambda1 lambda2) pairGammaMult
  have hc := congrArg (fun P : ℂ[X] => P.coeff 1) hexp
  have hroot :
      (gammaJetRootPolynomial ℂ s
        (pairGammaShift lambda1 lambda2) pairGammaMult).coeff 1 =
        -(2 * s + lambda1 + lambda2) := by
    rw [gammaJetRootPolynomial]
    simp only [pairGammaMult, pow_one, Fin.prod_univ_two,
      pairGammaShift_zero, pairGammaShift_one]
    rw [Polynomial.coeff_mul]
    rw [show Finset.antidiagonal 1 = {(0, 1), (1, 0)} by rfl]
    simp
    ring
  change (gammaJetRootPolynomial ℂ s
      (pairGammaShift lambda1 lambda2) pairGammaMult).coeff 1 =
    (∑ k ∈ Finset.range (gammaJetOrder pairGammaMult + 1),
      ascPochhammerCoeff ℂ
        (gammaJetRootPolynomial ℂ s
          (pairGammaShift lambda1 lambda2) pairGammaMult) k •
        ascPochhammer ℂ k).coeff 1 at hc
  rw [hroot] at hc
  rw [Polynomial.finsetSum_coeff] at hc
  simp only [gammaJetOrder_pair, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, Polynomial.coeff_smul, smul_eq_mul,
    ascPochhammer_zero, ascPochhammer_one] at hc
  have htop := gammaJetAnnihilatorCoeff_top s
    (pairGammaShift lambda1 lambda2) pairGammaMult
  rw [gammaJetOrder_pair] at htop
  change ascPochhammerCoeff ℂ
      (gammaJetRootPolynomial ℂ s (pairGammaShift lambda1 lambda2) pairGammaMult) 2 = 1
    at htop
  rw [htop] at hc
  change ascPochhammerCoeff ℂ
    (gammaJetRootPolynomial ℂ s (pairGammaShift lambda1 lambda2) pairGammaMult) 1 = _
  simp only [ascPochhammer_succ_left, Polynomial.coeff_mul] at hc
  rw [show Finset.antidiagonal 1 = {(0, 1), (1, 0)} by rfl] at hc
  norm_num [Polynomial.coeff_one] at hc
  linear_combination -hc

theorem gammaJetAnnihilator_pair (s lambda1 lambda2 : ℂ) (f : ℂ → ℂ) :
    gammaJetAnnihilator s (pairGammaShift lambda1 lambda2) pairGammaMult f =
      f (s + 2) - (2 * s + lambda1 + lambda2 + 1) * f (s + 1) +
        (s + lambda1) * (s + lambda2) * f s := by
  rw [gammaJetAnnihilator_eq_monic, gammaJetOrder_pair]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [gammaJetAnnihilatorCoeff_pair_zero,
    gammaJetAnnihilatorCoeff_pair_one]
  norm_num
  ring

theorem det_confluentGammaShiftMatrix_pair (s lambda1 lambda2 : ℂ)
    (hpole : ∀ i (p : ℕ),
      s + pairGammaShift lambda1 lambda2 i ≠ -(p : ℂ)) :
    (confluentGammaShiftMatrix s
      (pairGammaShift lambda1 lambda2) pairGammaMult).det =
      (lambda2 - lambda1) * Complex.Gamma (s + lambda1) *
        Complex.Gamma (s + lambda2) := by
  rw [det_confluentGammaShiftMatrix s
    (pairGammaShift lambda1 lambda2) pairGammaMult hpole]
  simp only [pairGammaMult, pow_one, Fin.prod_univ_two,
    pairGammaShift_zero, pairGammaShift_one]
  norm_num [Finset.prod_eq_mul_prod_diff_singleton (i := (0 : Fin 2))]
  have hlast : Finset.Ioi (1 : Fin 2) = ∅ := by
    ext j
    fin_cases j <;> simp
  rw [hlast]
  simp
  ring

end
end GaloisForLFunctions
