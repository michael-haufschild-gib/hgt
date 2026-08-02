import GaloisForLFunctions.HTGeometry.MultipleGammaAnnihilatorExact
import GaloisForLFunctions.HTGeometry.MultipleGammaDifferenceOperatorAlgebra
import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit

/-!
# The multiplicative hypercube specialization

A finite product of integer powers of structurally translated multiple elliptic gamma functions has
logarithmic derivative equal to the corresponding difference operator applied to the source.  Since
a nonzero germ and its logarithmic derivative are mutually differentially algebraic, such a product
is differentially algebraic exactly when its exponent operator lies in the squarefree Veronese
ideal.

This is the multiplicative form of the exact translation annihilator: the classification of finite
integer translate products by ideal membership.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry VeroneseIdeal

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

attribute [local instance] relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential
  relativeGaugeDifferentialAlgebra relativeGaugeCharZeroBase

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Translated gamma factors -/

/-- The multiple elliptic gamma function translated by an exponent vector. -/
def translateGamma (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (n : ι →₀ ℕ) :
    meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv (natShift τ n) (multipleEllipticGammaMero τ hτ)

omit [DecidableEq ι] in
theorem translateGamma_ne_zero (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (n : ι →₀ ℕ) :
    translateGamma τ hτ n ≠ 0 := by
  intro hzero
  refine multipleEllipticGammaMero_ne_zero τ hτ ?_
  have h := congrArg (addTranslationMeroEquiv (-(natShift τ n))) hzero
  rw [translateGamma, addTranslationMeroEquiv_add, neg_add_cancel,
    addTranslationMeroEquiv_zero_apply, map_zero] at h
  exact h

omit [DecidableEq ι] in
/-- Translation commutes with logarithmic differentiation. -/
theorem logDeriv_translateGamma (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (n : ι →₀ ℕ) :
    Differential.logDeriv (translateGamma τ hτ n) =
      addTranslationMeroEquiv (natShift τ n) (multipleEllipticGammaLogDerivMero τ hτ) := by
  rw [translateGamma, Differential.logDeriv, multipleEllipticGammaLogDerivMero,
    Differential.logDeriv, ← addTranslationMeroEquiv_deriv, ← map_div₀]

omit [Fintype ι] in
theorem xApply_finsetSum (τ : ι → ℂ) {κ : Type} (s : Finset κ) (P : κ → MvPolynomial ι ℂ)
    (y : meroField (Set.univ : Set ℂ)) :
    xApply τ (∑ k ∈ s, P k) y = ∑ k ∈ s, xApply τ (P k) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [xApply]
  | @insert a s ha ih => rw [Finset.sum_insert ha, xApply_add, ih, Finset.sum_insert ha]

/-! ## Finite integer products -/

/-- A finite product of integer powers of translated gamma functions. -/
def translateGammaProduct (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (c : (ι →₀ ℕ) →₀ ℤ) : meroField (Set.univ : Set ℂ) :=
  ∏ n ∈ c.support, translateGamma τ hτ n ^ (c n)

omit [DecidableEq ι] in
theorem translateGammaProduct_ne_zero (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (c : (ι →₀ ℕ) →₀ ℤ) : translateGammaProduct τ hτ c ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun n _ => zpow_ne_zero _ (translateGamma_ne_zero τ hτ n)

/-- The exponent operator of a finite integer translate product. -/
def translateProductOperator (c : (ι →₀ ℕ) →₀ ℤ) : MvPolynomial ι ℂ :=
  ∑ n ∈ c.support, MvPolynomial.C ((c n : ℂ)) * translationMonomial n

/-- **Logarithmic derivative of a translate product.**  It is the exponent operator applied to the
source. -/
theorem logDeriv_translateGammaProduct (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (c : (ι →₀ ℕ) →₀ ℤ) :
    Differential.logDeriv (translateGammaProduct τ hτ c) =
      xApply τ (translateProductOperator c) (multipleEllipticGammaLogDerivMero τ hτ) := by
  classical
  rw [translateGammaProduct,
    Differential.logDeriv_prod _ c.support _
      (fun n _ => zpow_ne_zero _ (translateGamma_ne_zero τ hτ n)),
    translateProductOperator]
  rw [xApply_finsetSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [differential_logDeriv_zpow _ (translateGamma_ne_zero τ hτ n), logDeriv_translateGamma,
    MvPolynomial.C_apply, xApply_monomial_mul, xMonomialApply_zero, xApply_translationMonomial,
    map_intCast]

/-! ## The multiplicative classification -/

/-- **Multiplicative hypercube specialization.**  A finite product of integer powers of
structurally translated multiple elliptic gamma functions is differentially algebraic exactly when
its exponent operator lies in the squarefree Veronese ideal. -/
theorem differentialAlgebraicOver_translateGammaProduct_iff_mem_veroneseIdeal
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (r : ℕ) (hcard : Fintype.card ι = r + 1)
    (c : (ι →₀ ℕ) →₀ ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (translateGammaProduct τ hτ c) ↔
      translateProductOperator c ∈ veroneseIdeal ℂ ι r := by
  rw [← differentialAlgebraicOver_xApply_iff_mem_veroneseIdeal τ hτ hQ r hcard,
    ← logDeriv_translateGammaProduct]
  constructor
  · intro hDA
    exact differentialAlgebraicOver_deriv_div_self hDA
  · intro hDA
    by_contra hnot
    exact (hypertranscendentalOver_deriv_div_self_iff
      (translateGammaProduct τ hτ c)).mpr hnot hDA

end

end GaloisForLFunctions
