import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryMultiplicity
import Mathlib.Analysis.Analytic.Order

/-!
# Analytic order of the full Baker auxiliary polynomial

This packages the algebraic initial-multiplicity result as analytic order, in precisely the form
required by multipoint Schwarz.  It also records that the auxiliary curve and every full
component-jet auxiliary function are entire.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Each coordinate of the full analytic auxiliary curve is entire. -/
theorem SolvedRelation.analyticAt_auxiliaryPoint
    (R : SolvedRelation) (z : ℂ) (v : R.Variable) :
    AnalyticAt ℂ (fun w => R.auxiliaryPoint w v) z := by
  rcases v with _ | i
  · change AnalyticAt ℂ id z
    exact analyticAt_id
  · have hlin : AnalyticAt ℂ (fun w : ℂ => R.lambda i * w) z :=
      analyticAt_const.mul analyticAt_id
    simpa [SolvedRelation.auxiliaryPoint] using hlin.cexp'

/-- Evaluation of a number-field auxiliary polynomial on the auxiliary curve is entire. -/
theorem SolvedRelation.analyticAt_auxiliaryFunction
    (R : SolvedRelation) (P : MvPolynomial R.Variable R.CoefficientField) (z : ℂ) :
    AnalyticAt ℂ (R.auxiliaryFunction P) z := by
  unfold SolvedRelation.auxiliaryFunction
  change AnalyticAt ℂ
    (fun w => MvPolynomial.aeval (R.auxiliaryPoint w) (R.complexify P)) z
  exact AnalyticAt.aeval_mvPolynomial
    (fun v => R.analyticAt_auxiliaryPoint z v) (R.complexify P)

/-- Every component-jet auxiliary function is entire. -/
theorem SolvedRelation.analyticAt_polynomialComponentJetAuxiliaryFunction
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (z : ℂ) :
    AnalyticAt ℂ (R.polynomialComponentJetAuxiliaryFunction c nu eta) z := by
  change AnalyticAt ℂ
    (R.auxiliaryFunction (R.polynomialComponentJetAuxiliaryPolynomial c nu eta)) z
  exact R.analyticAt_auxiliaryFunction
    (R.polynomialComponentJetAuxiliaryPolynomial c nu eta) z

/-- Any rectangular component budget gives the corresponding analytic-order lower bound. -/
theorem SolvedRelation.polynomialComponentJetAuxiliaryFunction_analyticOrderAt_ge
    (R : SolvedRelation) (c d : ℤ) (hc : c ≠ 0)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0)
    (hd : d ≠ 0) (sample : Fin S) (nu : R.Direction → ℕ) (q : ℕ)
    (hnuq : ∀ dir, nu dir + q ≤ T) :
    q ≤ analyticOrderAt (R.polynomialComponentJetAuxiliaryFunction c nu eta) (sample : ℂ) := by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (R.analyticAt_polynomialComponentJetAuxiliaryFunction c nu eta (sample : ℂ))]
  intro k hk
  apply R.polynomialComponentJetAuxiliaryFunction_iteratedDeriv_eq_zero_of_box
    c d hc hcomp hbase eta hker hd sample k nu
  intro dir
  exact lt_of_lt_of_le (Nat.add_lt_add_left hk (nu dir)) (hnuq dir)

/-- At every initial sample, the base full auxiliary function has at least the row cutoff order. -/
theorem SolvedRelation.polynomialAuxiliaryFunction_analyticOrderAt_ge
    (R : SolvedRelation) (c d : ℤ) (hc : c ≠ 0)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0)
    (hd : d ≠ 0) (sample : Fin S) :
    T ≤ analyticOrderAt
      (R.polynomialComponentJetAuxiliaryFunction c (fun _ => 0) eta) (sample : ℂ) := by
  apply R.polynomialComponentJetAuxiliaryFunction_analyticOrderAt_ge
    c d hc hcomp hbase eta hker hd sample (fun _ => 0) T
  intro dir
  simp

end GaloisForLFunctions.RHTower.BakerGeneralProof
