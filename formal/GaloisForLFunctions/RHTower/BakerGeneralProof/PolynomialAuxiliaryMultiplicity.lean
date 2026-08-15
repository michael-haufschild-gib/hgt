import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryFunction

/-!
# Initial multiplicity of the full Baker auxiliary polynomial

The kernel gives a rectangular box of exact solved-component jet zeros.  This module turns that
box into ordinary derivative multiplicity.  The induction is deliberately coordinatewise: after
`k` ordinary derivatives, each component index can have increased by at most `k`, so the box
condition needed at every step is `ν d + k < T` for every direction `d`.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Every full component-jet auxiliary function is complex differentiable everywhere. -/
theorem SolvedRelation.polynomialComponentJetAuxiliaryFunction_differentiable
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (nu : R.Direction → ℕ) (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField) :
    Differentiable ℂ (R.polynomialComponentJetAuxiliaryFunction c nu eta) := by
  intro z
  change DifferentiableAt ℂ
    (fun w => MvPolynomial.eval (R.auxiliaryPoint w)
      (R.complexify (R.polynomialComponentJetAuxiliaryPolynomial c nu eta))) z
  exact R.differentiableAt_eval_auxiliaryPoint z
    (R.complexify (R.polynomialComponentJetAuxiliaryPolynomial c nu eta))

/-- Any index inside the initial component box gives an exact zero at an initial sample. -/
theorem SolvedRelation.polynomialComponentJetAuxiliaryFunction_eq_zero_of_box
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0)
    (hd : d ≠ 0) (sample : Fin S) (nu : R.Direction → ℕ)
    (hnu : ∀ dir, nu dir < T) :
    R.polynomialComponentJetAuxiliaryFunction c nu eta (sample : ℂ) = 0 := by
  let row : R.AuxiliaryRow S T := ⟨sample, fun dir => ⟨nu dir, hnu dir⟩⟩
  have h := R.auxiliaryFunction_polynomialComponentJet_eq_zero
    c d hcomp hbase eta hker hd row
  simpa [SolvedRelation.polynomialComponentJetAuxiliaryFunction, row] using h

/-- A component-index box of kernel zeros propagates to all allowed ordinary derivatives. -/
theorem SolvedRelation.polynomialComponentJetAuxiliaryFunction_iteratedDeriv_eq_zero_of_box
    (R : SolvedRelation) (c d : ℤ) (hc : c ≠ 0)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0)
    (hd : d ≠ 0) (sample : Fin S) :
    ∀ (k : ℕ) (nu : R.Direction → ℕ),
      (∀ dir, nu dir + k < T) →
      iteratedDeriv k (R.polynomialComponentJetAuxiliaryFunction c nu eta) (sample : ℂ) = 0 := by
  intro k
  induction k with
  | zero =>
      intro nu hbudget
      rw [iteratedDeriv_zero]
      apply R.polynomialComponentJetAuxiliaryFunction_eq_zero_of_box
        c d hcomp hbase eta hker hd sample nu
      intro dir
      simpa using hbudget dir
  | succ k ih =>
      intro nu hbudget
      have hbump : ∀ dir e, R.componentBump nu dir e + k < T := by
        intro dir e
        by_cases he : e = dir
        · subst e
          simp only [SolvedRelation.componentBump, if_pos]
          rw [show (nu dir + 1) + k = nu dir + (k + 1) by ac_rfl]
          exact hbudget dir
        · rw [SolvedRelation.componentBump, if_neg he]
          exact lt_trans (Nat.add_lt_add_left (Nat.lt_succ_self k) (nu e)) (hbudget e)
      have hzero_none :
          iteratedDeriv k
            (R.polynomialComponentJetAuxiliaryFunction c (R.componentBump nu none) eta)
            (sample : ℂ) = 0 :=
        ih (R.componentBump nu none) (hbump none)
      have hzero_some : ∀ i : R.NonPivot,
          iteratedDeriv k
            (R.polynomialComponentJetAuxiliaryFunction c (R.componentBump nu (some i)) eta)
            (sample : ℂ) = 0 := fun i =>
        ih (R.componentBump nu (some i)) (hbump (some i))
      have hcont (mu : R.Direction → ℕ) :
          ContDiffAt ℂ (↑k)
            (R.polynomialComponentJetAuxiliaryFunction c mu eta) (sample : ℂ) :=
        (R.polynomialComponentJetAuxiliaryFunction_differentiable c mu eta).contDiff.contDiffAt
      have hcont_sum : ContDiffAt ℂ (↑k)
          (fun z => ∑ i : R.NonPivot, R.lambda i *
            R.polynomialComponentJetAuxiliaryFunction c (R.componentBump nu (some i)) eta z)
          (sample : ℂ) := by
        apply ContDiffAt.sum
        intro i hi
        simpa only [smul_eq_mul] using
          ContDiffAt.const_smul (R.lambda i) (hcont (R.componentBump nu (some i)))
      have hright : iteratedDeriv k
          (fun z => R.polynomialComponentJetAuxiliaryFunction c (R.componentBump nu none) eta z +
            ∑ i : R.NonPivot, R.lambda i *
              R.polynomialComponentJetAuxiliaryFunction c (R.componentBump nu (some i)) eta z)
          (sample : ℂ) = 0 := by
        rw [iteratedDeriv_fun_add (hcont (R.componentBump nu none)) hcont_sum,
          iteratedDeriv_fun_sum]
        · simp_rw [iteratedDeriv_const_mul_field]
          simp [hzero_none, hzero_some]
        · intro i hi
          simpa only [smul_eq_mul] using
            ContDiffAt.const_smul (R.lambda i) (hcont (R.componentBump nu (some i)))
      have hrec_fun :
          (fun z => (c : ℂ) * deriv
            (R.polynomialComponentJetAuxiliaryFunction c nu eta) z) =
          (fun z => R.polynomialComponentJetAuxiliaryFunction c (R.componentBump nu none) eta z +
            ∑ i : R.NonPivot, R.lambda i *
              R.polynomialComponentJetAuxiliaryFunction c (R.componentBump nu (some i)) eta z) := by
        funext z
        exact R.polynomialComponentJetAuxiliaryFunction_scaled_deriv c nu eta z
      have hiter := congrFun (congrArg (iteratedDeriv k) hrec_fun) (sample : ℂ)
      rw [iteratedDeriv_const_mul_field, ← iteratedDeriv_succ'] at hiter
      rw [hright] at hiter
      exact (mul_eq_zero.mp hiter).resolve_left (Int.cast_ne_zero.mpr hc)

/-- The base full auxiliary function has order at least the row cutoff at every initial sample. -/
theorem SolvedRelation.polynomialAuxiliaryFunction_iteratedDeriv_eq_zero
    (R : SolvedRelation) (c d : ℤ) (hc : c ≠ 0)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    {U V S T : ℕ} (eta : R.AuxiliaryColumn U V → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase U V S T) eta = 0)
    (hd : d ≠ 0) (sample : Fin S) (k : ℕ) (hk : k < T) :
    iteratedDeriv k
      (R.polynomialComponentJetAuxiliaryFunction c (fun _ => 0) eta) (sample : ℂ) = 0 := by
  apply R.polynomialComponentJetAuxiliaryFunction_iteratedDeriv_eq_zero_of_box
    c d hc hcomp hbase eta hker hd sample k (fun _ => 0)
  intro dir
  simpa using hk

end GaloisForLFunctions.RHTower.BakerGeneralProof
