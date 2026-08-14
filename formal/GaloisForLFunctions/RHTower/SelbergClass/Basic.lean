import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Exact carrier for the extended Selberg class

This module encodes the first three Selberg axioms without assigning false finite values at poles.
An entire finite-order regularization represents the meromorphic continuation.  Functional-equation
equality uses the codiscrete filter, matching Mathlib's convention that values of meromorphic
functions at their poles are irrelevant.

Degree, conductor, and internal shift below belong to a concrete gamma presentation.  They are not
yet promoted to invariants of the represented Dirichlet series: that requires the separate gamma-
presentation uniqueness theorem.
-/

open scoped BigOperators
open Complex Filter Set

namespace RHTower

noncomputable section

/-- An entire complex function with a global exponential-power growth bound. -/
structure EntireFiniteOrder where
  toFun : ℂ → ℂ
  analytic : AnalyticOnNhd ℂ toFun univ
  growth : ∃ A B ρ : ℝ, 0 < A ∧ 0 < B ∧ 0 ≤ ρ ∧
    ∀ z : ℂ, ‖toFun z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)

instance : CoeFun EntireFiniteOrder (fun _ ↦ ℂ → ℂ) := ⟨EntireFiniteOrder.toFun⟩

/-- Pole-safe analytic-continuation data for an extended Selberg-class Dirichlet series. -/
structure SelbergAnalyticContinuation where
  poleOrder : ℕ
  regularized : EntireFiniteOrder

/-- Totalized represented value. Its value at `s=1` is irrelevant to meromorphic equality. -/
def SelbergAnalyticContinuation.value (A : SelbergAnalyticContinuation) (s : ℂ) : ℂ :=
  A.regularized s / (s - 1) ^ A.poleOrder

/-- The pole-safe represented value is genuinely meromorphic. -/
theorem SelbergAnalyticContinuation.meromorphic_value (A : SelbergAnalyticContinuation) :
    Meromorphic A.value := by
  have hnum : Meromorphic fun s : ℂ ↦ A.regularized s := fun z ↦
    (A.regularized.analytic z (mem_univ z)).meromorphicAt
  have hden : Meromorphic fun s : ℂ ↦ (s - 1) ^ A.poleOrder := fun z ↦
    (by fun_prop : AnalyticAt ℂ (fun s : ℂ ↦ (s - 1) ^ A.poleOrder) z).meromorphicAt
  exact hnum.div hden

/-- A concrete Selberg-type gamma presentation and root number. -/
structure SelbergGammaData where
  Q : ℝ
  Q_pos : 0 < Q
  rank : ℕ
  lambda : Fin rank → ℝ
  lambda_pos : ∀ j, 0 < lambda j
  mu : Fin rank → ℂ
  mu_re_nonneg : ∀ j, 0 ≤ (mu j).re
  rootNumber : ℂ
  rootNumber_norm : ‖rootNumber‖ = 1

/-- Gamma factor attached to a concrete Selberg functional-equation presentation. -/
def SelbergGammaData.gammaFactor (G : SelbergGammaData) : ℂ → ℂ :=
  (fun s : ℂ ↦ (G.Q : ℂ) ^ s) *
    (∏ j, (fun s : ℂ ↦ Complex.Gamma ((G.lambda j : ℂ) * s + G.mu j)))

/-- Every concrete Selberg gamma factor is meromorphic. -/
theorem SelbergGammaData.meromorphic_gammaFactor (G : SelbergGammaData) :
    Meromorphic G.gammaFactor := by
  have hQdiff : Differentiable ℂ fun s : ℂ ↦ (G.Q : ℂ) ^ s :=
    differentiable_id.const_cpow (.inl (ofReal_ne_zero.mpr G.Q_pos.ne'))
  have hQanalytic : AnalyticOnNhd ℂ (fun s : ℂ ↦ (G.Q : ℂ) ^ s) univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hQdiff
  have hQ : Meromorphic fun s : ℂ ↦ (G.Q : ℂ) ^ s := fun z ↦
    (hQanalytic z (mem_univ z)).meromorphicAt
  have hGamma (j : Fin G.rank) :
      Meromorphic fun s : ℂ ↦ Complex.Gamma ((G.lambda j : ℂ) * s + G.mu j) := by
    intro z
    simpa only [Function.comp_def] using
      (Meromorphic.Gamma ((G.lambda j : ℂ) * z + G.mu j)).comp_analyticAt
        (x := z) (g := fun s : ℂ ↦ (G.lambda j : ℂ) * s + G.mu j) (by fun_prop)
  exact hQ.mul (Meromorphic.prod (s := Finset.univ) fun j _ ↦ hGamma j)

/-- Degree of a concrete gamma presentation. -/
def SelbergGammaData.degree (G : SelbergGammaData) : ℝ :=
  2 * ∑ j, G.lambda j

/-- Conductor of a concrete gamma presentation. -/
def SelbergGammaData.conductor (G : SelbergGammaData) : ℝ :=
  (2 * Real.pi) ^ G.degree * G.Q ^ 2 * ∏ j, G.lambda j ^ (2 * G.lambda j)

/-- Internal shift of a concrete gamma presentation. -/
def SelbergGammaData.internalShift (G : SelbergGammaData) : ℝ :=
  (2 / G.degree) * (∑ j, G.mu j).im

/-- Completed meromorphic value attached to concrete continuation and gamma data. -/
def selbergCompletedValue (G : SelbergGammaData) (A : SelbergAnalyticContinuation)
    (s : ℂ) : ℂ :=
  G.gammaFactor s * A.value s

/-- Reflection used in Selberg-type functional equations. -/
def selbergConjugateReflection (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  star (f (1 - star s))

/-- Exact carrier for the extended Selberg class `S♯`. -/
structure ExtendedSelbergClass where
  coeff : ArithmeticFunction ℂ
  coeff_ne_zero : coeff ≠ 0
  lSeriesSummable : ∀ s : ℂ, 1 < s.re → LSeriesSummable coeff s
  continuation : SelbergAnalyticContinuation
  lSeries_eq_value : ∀ s : ℂ, 1 < s.re → LSeries coeff s = continuation.value s
  gammaData : SelbergGammaData
  functionalEquation :
    selbergCompletedValue gammaData continuation =ᶠ[codiscrete ℂ]
      fun s ↦ gammaData.rootNumber *
        selbergConjugateReflection (selbergCompletedValue gammaData continuation) s

/-- Represented meromorphic function. -/
def ExtendedSelbergClass.value (F : ExtendedSelbergClass) : ℂ → ℂ :=
  F.continuation.value

instance : CoeFun ExtendedSelbergClass (fun _ ↦ ℂ → ℂ) := ⟨ExtendedSelbergClass.value⟩

/-- Every extended Selberg-class carrier represents a meromorphic function. -/
theorem ExtendedSelbergClass.meromorphic_value (F : ExtendedSelbergClass) : Meromorphic F :=
  F.continuation.meromorphic_value

/-- Completed function of every extended Selberg-class carrier is meromorphic. -/
theorem ExtendedSelbergClass.meromorphic_completedValue (F : ExtendedSelbergClass) :
    Meromorphic (selbergCompletedValue F.gammaData F.continuation) := by
  exact F.gammaData.meromorphic_gammaFactor.mul F.continuation.meromorphic_value

end


end RHTower
