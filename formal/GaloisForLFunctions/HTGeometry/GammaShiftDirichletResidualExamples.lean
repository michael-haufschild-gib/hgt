import GaloisForLFunctions.HTGeometry.GammaShiftAugmentedDeterminant

/-!
# One- and two-shift examples of Gamma-jet annihilators and Casoratians

This module computes the general consecutive-shift Gamma-jet annihilator explicitly for one and
two simple shifts. For a single shift `λ` the annihilator is the first-order operator
`f ↦ f(s + 1) - (s + λ) f(s)`, matching `Γ(s + λ + 1) = (s + λ) Γ(s + λ)`. For two simple shifts
`λ₁, λ₂` it is the second-order operator
`f ↦ f(s + 2) - (2s + λ₁ + λ₂ + 1) f(s + 1) + (s + λ₁)(s + λ₂) f(s)`, and the `2 × 2` Casoratian
of `Γ(s + λ₁), Γ(s + λ₂)` equals `(λ₂ - λ₁) Γ(s + λ₁) Γ(s + λ₂)`.

## Main results

- `gammaJetAnnihilator_singleton`: the one-shift annihilator is `f(s + 1) - (s + λ) f(s)`.
- `gammaJetAnnihilator_pair`: the two-shift annihilator is
  `f(s + 2) - (2s + λ₁ + λ₂ + 1) f(s + 1) + (s + λ₁)(s + λ₂) f(s)`.
- `det_confluentGammaShiftMatrix_pair`: the two-shift Gamma Casoratian determinant is
  `(λ₂ - λ₁) Γ(s + λ₁) Γ(s + λ₂)`.

## Hypotheses

Unconditional. The operator identities hold for every `s`, every shift and every function `f`.
The determinant formula assumes only that `s + λ₁` and `s + λ₂` are not poles of `Γ`.
-/

open scoped BigOperators Matrix
namespace GaloisForLFunctions
open Polynomial Filter LSeries
noncomputable section

/-- The one-element shift packet `{λ}`, used with multiplicity one. -/
def singletonGammaShift (lambda : ℂ) : Fin 1 → ℂ := fun _ => lambda
def singletonGammaMult : Fin 1 → ℕ := fun _ => 1

theorem gammaJetOrder_singleton : gammaJetOrder singletonGammaMult = 1 := by
  simp [gammaJetOrder, singletonGammaMult]

theorem gammaJetAnnihilatorCoeff_singleton_zero (s lambda : ℂ) :
    gammaJetAnnihilatorCoeff s (singletonGammaShift lambda) singletonGammaMult 0 =
      -(s + lambda) := by
  rw [gammaJetAnnihilatorCoeff, gammaJetRootPolynomial_zeroCoeff]
  simp [gammaJetOrder_singleton, singletonGammaShift, singletonGammaMult]

/-- For a single simple shift `λ`, the Gamma-jet annihilator is the first-order difference operator
`f ↦ f(s + 1) - (s + λ) f(s)`. -/
theorem gammaJetAnnihilator_singleton (s lambda : ℂ) (f : ℂ → ℂ) :
    gammaJetAnnihilator s (singletonGammaShift lambda) singletonGammaMult f =
      f (s + 1) - (s + lambda) * f s := by
  rw [gammaJetAnnihilator_eq_monic]
  rw [gammaJetOrder_singleton]
  rw [Finset.sum_range_one]
  rw [gammaJetAnnihilatorCoeff_singleton_zero]
  simp
  ring

/-- The two-element shift packet `(λ₁, λ₂)`, used with multiplicities one. -/
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

/-- The middle coefficient of the two-shift annihilator is `-(2s + λ₁ + λ₂ + 1)`, read off from
the expansion of `(X - (s + λ₁))(X - (s + λ₂))` in the rising-factorial basis. -/
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
    rw [show Finset.HasAntidiagonal.antidiagonal (A := ℕ) 1 =
      {(0, 1), (1, 0)} by rfl]
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
  rw [show Finset.HasAntidiagonal.antidiagonal (A := ℕ) 1 =
    {(0, 1), (1, 0)} by rfl] at hc
  norm_num [Polynomial.coeff_one] at hc
  linear_combination -hc

/-- For two simple shifts `λ₁, λ₂`, the Gamma-jet annihilator is the second-order difference
operator `f ↦ f(s + 2) - (2s + λ₁ + λ₂ + 1) f(s + 1) + (s + λ₁)(s + λ₂) f(s)`. -/
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

/-- The Casoratian `det [Γ(s + λ_a + k)]` for two simple shifts equals
`(λ₂ - λ₁) Γ(s + λ₁) Γ(s + λ₂)`, assuming `hpole`: neither `s + λ₁` nor `s + λ₂` is a pole of `Γ`. -/
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
  norm_num [Finset.prod_eq_mul_prod_sdiff_singleton (i := (0 : Fin 2))]
  have hlast : Finset.Ioi (1 : Fin 2) = ∅ := by
    ext j
    fin_cases j <;> simp
  rw [hlast]
  simp
  ring

end
end GaloisForLFunctions
