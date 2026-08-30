import GaloisForLFunctions.HTGeometry.SumExponentialSineOrderLedger

/-!
# Equal differential rank, opposite cap cost

A function whose realization is a polynomial has all its jets inside `ℂ(z)`, so its differential
rank is one; hence a function of rank different from one is not a polynomial.  This supplies the
side conditions of the shadow law for `exp + sin`.

The exponential cap then costs a full state on `exp + sin`, whose primitive defect is zero, and
nothing on the Gaussian primitive, whose primitive defect is one — although both inputs have
differential rank three.  The derivative-shadow signature, not the scalar order, governs the cost.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-! ### Polynomials have differential rank one -/

theorem iteratedDeriv_polynomial (p : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun z : ℂ => p.eval z)
      = fun z : ℂ => (Polynomial.derivative^[k] p).eval z := by
  induction k generalizing p with
  | zero => rw [iteratedDeriv_zero, Function.iterate_zero_apply]
  | succ k ih =>
      have hstep : iteratedDeriv (k + 1) (fun z : ℂ => p.eval z)
          = iteratedDeriv k (deriv fun z : ℂ => p.eval z) := iteratedDeriv_succ'
      have hderiv : (deriv fun z : ℂ => p.eval z) = fun z : ℂ => p.derivative.eval z := by
        funext z
        exact Polynomial.deriv p
      rw [hstep, hderiv, ih p.derivative, Function.iterate_succ_apply]

theorem jetElem_mem_coordField_of_poly {u : ℂ → ℂ} (hu : Differentiable ℂ u)
    {p : Polynomial ℂ} (hp : ∀ z : ℂ, u z = p.eval z) (k : ℕ) :
    jetElem hu k
      ∈ IntermediateField.adjoin ℂ ({coordElem} : Set (meroField (Set.univ : Set ℂ))) := by
  have hfun : iteratedDeriv k u = fun z : ℂ => (Polynomial.derivative^[k] p).eval z := by
    have hu' : u = fun z : ℂ => p.eval z := funext hp
    rw [hu', iteratedDeriv_polynomial]
  have hjet : jetElem hu k = Polynomial.aeval coordElem (Polynomial.derivative^[k] p) := by
    rw [jetElem, coordElem, aeval_analyticMeroElement analyticOnNhd_coord]
    exact analyticMeroElement_congr _ _ hfun
  rw [hjet]
  have hmem : Polynomial.aeval coordElem (Polynomial.derivative^[k] p)
      ∈ Algebra.adjoin ℂ ({coordElem} : Set (meroField (Set.univ : Set ℂ))) :=
    Polynomial.aeval_mem_adjoin_singleton ℂ coordElem
  exact IntermediateField.algebra_adjoin_le_adjoin ℂ
    ({coordElem} : Set (meroField (Set.univ : Set ℂ))) hmem

/-- **A function of differential rank other than one is not a polynomial.** -/
theorem not_exists_poly_of_daRank_ne_one {u : ℂ → ℂ} (hu : Differentiable ℂ u)
    (h : daRank hu ≠ 1) : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, u z = p.eval z := by
  rintro ⟨p, hp⟩
  refine h ?_
  have heq : IntermediateField.adjoin ℂ (insert coordElem (Set.range fun k : ℕ => jetElem hu k))
      = IntermediateField.adjoin ℂ ({coordElem} : Set (meroField (Set.univ : Set ℂ))) := by
    refine le_antisymm ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      rintro y (rfl | ⟨k, rfl⟩)
      · exact IntermediateField.subset_adjoin ℂ _ rfl
      · exact jetElem_mem_coordField_of_poly hu hp k
    · rw [IntermediateField.adjoin_le_iff]
      rintro y rfl
      exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)
  rw [daRank, heq]
  exact trdeg_adjoin_coordElem

/-! ### The side conditions for `exp + sin` -/

theorem not_poly_sumES : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, sumES z = p.eval z := by
  refine not_exists_poly_of_daRank_ne_one differentiable_sumES ?_
  rw [daRank_sumES]
  norm_num

theorem deriv_sumES_zero : deriv sumES 0 = 2 := by
  have hd : HasDerivAt sumES (Complex.exp 0 + Complex.cos 0) 0 :=
    (Complex.hasDerivAt_exp 0).add (Complex.hasDerivAt_sin 0)
  rw [hd.deriv]
  norm_num

theorem not_const_sumES : ¬ ∃ c : ℂ, ∀ z : ℂ, sumES z = c := by
  refine not_const_of_deriv_ne_zero (z₀ := 0) ?_
  rw [deriv_sumES_zero]
  norm_num

theorem differentiable_expSumES : Differentiable ℂ (fun w : ℂ => Complex.exp (sumES w)) :=
  Complex.differentiable_exp.comp differentiable_sumES

theorem not_const_expSumES : ¬ ∃ c : ℂ, ∀ z : ℂ, Complex.exp (sumES z) = c := by
  refine not_const_of_deriv_ne_zero (z₀ := 0) ?_
  have hd0 : HasDerivAt sumES (Complex.exp 0 + Complex.cos 0) 0 :=
    (Complex.hasDerivAt_exp 0).add (Complex.hasDerivAt_sin 0)
  have hd : HasDerivAt (fun w : ℂ => Complex.exp (sumES w))
      (Complex.exp (sumES 0) * (Complex.exp 0 + Complex.cos 0)) 0 := hd0.cexp
  rw [hd.deriv]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  norm_num

/-! ### The cap cost -/

/-- **The exponential cap on `exp + sin` costs a full differential state.** -/
theorem daRank_expSumES : daRank differentiable_expSumES = 4 := by
  have h := daRank_comp Complex.differentiable_exp differentiable_sumES autonomousFirstOrder_exp
    differentiable_expSumES not_poly_cexp not_poly_sumES not_const_expSumES not_const_sumES
  exact h.trans
    ((congrArg (fun c : Cardinal => c + 1) shadowRank_sumES).trans (by norm_num))

/-- **Two entire inputs of equal differential rank with opposite composition cost.**  The Gaussian
primitive and `exp + sin` both have differential rank three, but the same autonomous first-order cap
raises the rank of one and not of the other, because their primitive defects differ. -/
theorem cap_cost_differs_at_equal_rank :
    daRank differentiable_sumES = daRank differentiable_gaussPrimitive
      ∧ daRank differentiable_expSumES ≠ daRank differentiable_expGauss := by
  refine ⟨by rw [daRank_sumES, daRank_gaussPrimitive], ?_⟩
  rw [daRank_expSumES, daRank_expGauss]
  norm_num

/-- The primitive defects of the two inputs are opposite: zero for `exp + sin`, one for the Gaussian
primitive. -/
theorem primitive_defects_differ :
    daRank differentiable_sumES = shadowRank' differentiable_sumES
      ∧ daRank differentiable_gaussPrimitive = shadowRank' differentiable_gaussPrimitive + 1 :=
  ⟨daRank_eq_shadowRank_sumES, daRank_eq_shadowRank_add_one_gaussPrimitive⟩

end

end GaloisForLFunctions.HTGeometry
