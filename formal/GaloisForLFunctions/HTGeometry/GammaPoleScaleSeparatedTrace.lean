import GaloisForLFunctions.HTGeometry.GammaInversePoleBranchScaleFreeness
import GaloisForLFunctions.HTGeometry.MvPolynomialHomogeneousDehomogenization
import GaloisForLFunctions.HTGeometry.SimplePoleJetScaleSeparatedHorizon

/-!
# The scale-separated simple-pole trace on the actual Gamma tower

The universal simple-pole trace uses a moving scale `S` and regular-unit jets
`U₀,U₁,...`.  The factorially rescaled Gamma pole family has `U₀ = 1`; its positive derivatives,
together with `S`, are algebraically independent as pole-index germs.

This module closes the interface between those two descriptions.  It proves that dehomogenizing
`U₀` is faithful on every weighted-homogeneous boundary sector, converts the known free Taylor
coefficients to actual derivatives by a nonzero factorial diagonal, and specializes the universal
particle trace to the analytic Gamma boundary.  Consequently the particle-number coefficient of
every nonzero homogeneous differential source remains nonzero on the actual Gamma pole tower.

This is the homogeneous associated-graded Gamma bridge.  It does not yet perform the
polynomial-in-pole-position Taylor shift or the maximal-weight descent between distinct source
degrees required by the global `ℂ[z]` simple-pole intersection theorem.
-/

open MvPolynomial Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reindex `0,1,2,...` as a distinguished head followed by `0,1,2,...`. -/
def natSuccOptionEquiv : ℕ ≃ Option ℕ where
  toFun
    | 0 => none
    | k + 1 => some k
  invFun
    | none => 0
    | some k => k + 1
  left_inv k := by cases k <;> rfl
  right_inv o := by cases o <;> rfl

@[simp] theorem natSuccOptionEquiv_zero : natSuccOptionEquiv 0 = none := rfl
@[simp] theorem natSuccOptionEquiv_succ (k : ℕ) :
    natSuccOptionEquiv (k + 1) = some k := rfl

/-- Set coordinate zero to one and shift every positive coordinate down by one. -/
def natHeadDehomogenize : MvPolynomial ℕ ℂ →+* MvPolynomial ℕ ℂ :=
  GaloisForLFunctions.optionHeadDehomogenize.comp
    (MvPolynomial.renameEquiv ℂ natSuccOptionEquiv).toRingHom

@[simp] theorem natHeadDehomogenize_X_zero :
    natHeadDehomogenize (MvPolynomial.X 0) = 1 := by
  simp [natHeadDehomogenize, GaloisForLFunctions.optionHeadDehomogenize]

@[simp] theorem natHeadDehomogenize_X_succ (k : ℕ) :
    natHeadDehomogenize (MvPolynomial.X (k + 1)) = MvPolynomial.X k := by
  simp [natHeadDehomogenize, GaloisForLFunctions.optionHeadDehomogenize]

theorem natHeadDehomogenize_ne_zero_of_isHomogeneous
    {d : ℕ} {P : MvPolynomial ℕ ℂ}
    (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    natHeadDehomogenize P ≠ 0 := by
  let E := MvPolynomial.renameEquiv ℂ natSuccOptionEquiv
  have hEP : (E P).IsHomogeneous d := by
    simpa [E] using hP.rename_isHomogeneous
  have hEP0 : E P ≠ 0 := E.injective.ne hP0
  exact GaloisForLFunctions.optionHeadDehomogenize_ne_zero_of_isHomogeneous hEP hEP0

/-- Set the regular-unit value `U₀` to one, retain the scale, and reindex positive derivatives. -/
def scaleSeparatedPoleUnitDehomogenize :
    ScaleSeparatedPoleBoundaryRing →+* MvPolynomial (Option ℕ) ℂ :=
  (MvPolynomial.optionEquivLeft ℂ ℕ).symm.toRingHom.comp
    ((Polynomial.mapRingHom natHeadDehomogenize).comp
      (MvPolynomial.optionEquivLeft ℂ ℕ).toRingHom)

@[simp] theorem scaleSeparatedPoleUnitDehomogenize_C (c : ℂ) :
    scaleSeparatedPoleUnitDehomogenize (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [scaleSeparatedPoleUnitDehomogenize, natHeadDehomogenize,
    GaloisForLFunctions.optionHeadDehomogenize]

@[simp] theorem scaleSeparatedPoleUnitDehomogenize_X_none :
    scaleSeparatedPoleUnitDehomogenize (MvPolynomial.X none) =
      MvPolynomial.X none := by
  simp [scaleSeparatedPoleUnitDehomogenize, natHeadDehomogenize]

@[simp] theorem scaleSeparatedPoleUnitDehomogenize_X_some_zero :
    scaleSeparatedPoleUnitDehomogenize (MvPolynomial.X (some 0)) = 1 := by
  simp [scaleSeparatedPoleUnitDehomogenize, natHeadDehomogenize]

@[simp] theorem scaleSeparatedPoleUnitDehomogenize_X_some_succ (k : ℕ) :
    scaleSeparatedPoleUnitDehomogenize (MvPolynomial.X (some (k + 1))) =
      MvPolynomial.X (some k) := by
  simp [scaleSeparatedPoleUnitDehomogenize, natHeadDehomogenize]

/-- Dehomogenizing the unit value cannot kill a scale-separated weighted-homogeneous sector. -/
theorem scaleSeparatedPoleUnitDehomogenize_ne_zero_of_isWeightedHomogeneous
    {d : ℕ} {Q : ScaleSeparatedPoleBoundaryRing}
    (hQ : MvPolynomial.IsWeightedHomogeneous simplePoleBoundaryWeight Q d)
    (hQ0 : Q ≠ 0) :
    scaleSeparatedPoleUnitDehomogenize Q ≠ 0 := by
  let p : Polynomial (MvPolynomial ℕ ℂ) := MvPolynomial.optionEquivLeft ℂ ℕ Q
  have hp0 : p ≠ 0 := (MvPolynomial.optionEquivLeft ℂ ℕ).injective.ne hQ0
  let j := p.natDegree
  have hj : p.coeff j ≠ 0 := by
    simpa [j] using Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hjhom : (p.coeff j).IsHomogeneous d := by
    exact coeff_isHomogeneous_of_boundaryWeightedHomogeneous hQ j
  have hjdehom : natHeadDehomogenize (p.coeff j) ≠ 0 :=
    natHeadDehomogenize_ne_zero_of_isHomogeneous hjhom hj
  have hmap : p.map natHeadDehomogenize ≠ 0 := by
    intro hzero
    apply hjdehom
    have hcoeff := congrArg (Polynomial.coeff · j) hzero
    simpa using hcoeff
  have hinv :
      (MvPolynomial.optionEquivLeft ℂ ℕ).symm
          (p.map natHeadDehomogenize) ≠ 0 :=
    by simpa using (MvPolynomial.optionEquivLeft ℂ ℕ).symm.injective.ne hmap
  simpa [scaleSeparatedPoleUnitDehomogenize, p] using hinv

local instance gammaScaleTraceNatGermAlgebra : Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

/-- Diagonal conversion from positive Taylor coefficients to positive derivatives. -/
def gammaPoleUnitDerivativeScale : Option ℕ → ℂ
  | none => 1
  | some k => ((k + 1).factorial : ℂ)

theorem gammaPoleUnitDerivativeScale_ne_zero (o : Option ℕ) :
    gammaPoleUnitDerivativeScale o ≠ 0 := by
  rcases o with (_ | k)
  · exact one_ne_zero
  · simpa [gammaPoleUnitDerivativeScale] using
      (show (((k + 1).factorial : ℂ)) ≠ 0 by
        exact_mod_cast Nat.factorial_ne_zero (k + 1))

/-- The factorial scale followed by every positive derivative of the actual Gamma regular unit. -/
def gammaPoleScaleAndUnitDerivativeFamily : Option ℕ → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some k => algebraMap ℂ NatGerm (((k + 1).factorial : ℂ)) *
      gammaPoleUnitPositiveCoefficientGerm k

/-- The actual positive derivatives of the analytic Gamma regular units, as pole-index germs. -/
def gammaPoleUnitPositiveDerivativeGerm (k : ℕ) : NatGerm :=
  fun N : ℕ => iteratedDeriv (k + 1) (gammaPoleRegularUnit (N - 1)) 0

/-- Value reflection from the coefficient coordinates to the actual analytic derivatives. -/
theorem gammaPoleScaleAndUnitDerivativeFamily_some_eq_actual (k : ℕ) :
    gammaPoleScaleAndUnitDerivativeFamily (some k) =
      gammaPoleUnitPositiveDerivativeGerm k := by
  rw [gammaPoleScaleAndUnitDerivativeFamily,
    gammaPoleUnitPositiveCoefficientGerm_eq_actualTaylorCoefficient]
  change complexNatGerm (((k + 1).factorial : ℂ)) *
      (↑(fun N : ℕ => (((k + 1).factorial : ℂ)⁻¹) *
        iteratedDeriv (k + 1) (gammaPoleRegularUnit (N - 1)) 0) : NatGerm) =
      (↑(fun N : ℕ =>
        iteratedDeriv (k + 1) (gammaPoleRegularUnit (N - 1)) 0) : NatGerm)
  rw [complexNatGerm_eq_constGerm, ← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun N => by
    dsimp [gammaPoleUnitPositiveDerivativeGerm]
    have hf : (((k + 1).factorial : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (k + 1)
    rw [← mul_assoc, mul_inv_cancel₀ hf, one_mul]

/-- Evaluation on the factorial scale and every actual positive regular-unit derivative. -/
def gammaPoleScaleAndUnitDerivativeEval :
    MvPolynomial (Option ℕ) ℂ →+* NatGerm :=
  MvPolynomial.eval₂Hom complexNatGerm gammaPoleScaleAndUnitDerivativeFamily

theorem gammaPoleScaleAndUnitDerivativeEval_eq_comp :
    gammaPoleScaleAndUnitDerivativeEval =
      gammaPoleScaleAndUnitPositiveCoefficientEval.comp
        (GaloisForLFunctions.mvPolynomialDiagonalScaleRing
          gammaPoleUnitDerivativeScale).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndUnitDerivativeEval,
      gammaPoleScaleAndUnitPositiveCoefficientEval, complexNatGerm]
  · intro o
    rcases o with (_ | k)
    · simp [gammaPoleScaleAndUnitDerivativeEval,
        gammaPoleScaleAndUnitDerivativeFamily,
        gammaPoleScaleAndUnitPositiveCoefficientEval,
        gammaPoleScaleAndUnitPositiveCoefficientFamily,
        GaloisForLFunctions.mvPolynomialDiagonalScaleRing,
        gammaPoleUnitDerivativeScale]
    · simp [gammaPoleScaleAndUnitDerivativeEval,
        gammaPoleScaleAndUnitDerivativeFamily,
        gammaPoleScaleAndUnitPositiveCoefficientEval,
        gammaPoleScaleAndUnitPositiveCoefficientFamily,
        GaloisForLFunctions.mvPolynomialDiagonalScaleRing,
        gammaPoleUnitDerivativeScale]

/-- The factorial scale and all actual positive regular-unit derivatives are algebraically free. -/
theorem gammaPoleScaleAndUnitDerivativeEval_injective :
    Function.Injective gammaPoleScaleAndUnitDerivativeEval := by
  rw [gammaPoleScaleAndUnitDerivativeEval_eq_comp]
  apply gammaPoleScaleAndUnitPositiveCoefficientEval_injective.comp
  intro P Q hPQ
  have hPQ' :
      GaloisForLFunctions.mvPolynomialDiagonalScaleRing gammaPoleUnitDerivativeScale P =
        GaloisForLFunctions.mvPolynomialDiagonalScaleRing gammaPoleUnitDerivativeScale Q := hPQ
  have h := congrArg
    (GaloisForLFunctions.mvPolynomialDiagonalScaleRing
      (fun o => (gammaPoleUnitDerivativeScale o)⁻¹)) hPQ'
  simpa only [GaloisForLFunctions.mvPolynomialDiagonalScaleRing_inv_apply
    gammaPoleUnitDerivativeScale gammaPoleUnitDerivativeScale_ne_zero P,
    GaloisForLFunctions.mvPolynomialDiagonalScaleRing_inv_apply
      gammaPoleUnitDerivativeScale gammaPoleUnitDerivativeScale_ne_zero Q] using h

theorem algebraicIndependent_gammaPoleScaleAndUnitDerivativeFamily :
    AlgebraicIndependent ℂ gammaPoleScaleAndUnitDerivativeFamily := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndUnitDerivativeEval, MvPolynomial.aeval_def] using
    gammaPoleScaleAndUnitDerivativeEval_injective

/-- Evaluate the scale-separated boundary on the actual factorially scaled Gamma pole family. -/
def gammaScaleSeparatedPoleBoundaryEval :
    ScaleSeparatedPoleBoundaryRing →+* NatGerm :=
  gammaPoleScaleAndUnitDerivativeEval.comp scaleSeparatedPoleUnitDehomogenize

@[simp] theorem gammaScaleSeparatedPoleBoundaryEval_C (c : ℂ) :
    gammaScaleSeparatedPoleBoundaryEval (MvPolynomial.C c) = complexNatGerm c := by
  simp [gammaScaleSeparatedPoleBoundaryEval, gammaPoleScaleAndUnitDerivativeEval]

@[simp] theorem gammaScaleSeparatedPoleBoundaryEval_X_none :
    gammaScaleSeparatedPoleBoundaryEval (MvPolynomial.X none) =
      reciprocalSignedFactorialGerm := by
  simp [gammaScaleSeparatedPoleBoundaryEval, gammaPoleScaleAndUnitDerivativeEval,
    gammaPoleScaleAndUnitDerivativeFamily]

@[simp] theorem gammaScaleSeparatedPoleBoundaryEval_X_some_zero :
    gammaScaleSeparatedPoleBoundaryEval (MvPolynomial.X (some 0)) = 1 := by
  simp [gammaScaleSeparatedPoleBoundaryEval]

@[simp] theorem gammaScaleSeparatedPoleBoundaryEval_X_some_succ (k : ℕ) :
    gammaScaleSeparatedPoleBoundaryEval (MvPolynomial.X (some (k + 1))) =
      algebraMap ℂ NatGerm (((k + 1).factorial : ℂ)) *
        gammaPoleUnitPositiveCoefficientGerm k := by
  simp [gammaScaleSeparatedPoleBoundaryEval, gammaPoleScaleAndUnitDerivativeEval,
    gammaPoleScaleAndUnitDerivativeFamily]

/-- The actual Gamma boundary evaluation is faithful on each weighted-homogeneous sector. -/
theorem gammaScaleSeparatedPoleBoundaryEval_ne_zero_of_isWeightedHomogeneous
    {d : ℕ} {Q : ScaleSeparatedPoleBoundaryRing}
    (hQ : MvPolynomial.IsWeightedHomogeneous simplePoleBoundaryWeight Q d)
    (hQ0 : Q ≠ 0) :
    gammaScaleSeparatedPoleBoundaryEval Q ≠ 0 := by
  have hdehom :=
    scaleSeparatedPoleUnitDehomogenize_ne_zero_of_isWeightedHomogeneous hQ hQ0
  exact gammaPoleScaleAndUnitDerivativeEval_injective.ne hdehom

/-- The universal scale-separated profile, specialized to the actual Gamma boundary germs. -/
def gammaScaleSeparatedSimplePoleProfileEval (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* Polynomial NatGerm :=
  (Polynomial.mapRingHom gammaScaleSeparatedPoleBoundaryEval).comp
    (finiteScaleSeparatedSimplePoleProfileEval n)

/-- The particle-number coefficient is exactly the actual Gamma evaluation of the universal
scale-separated boundary trace. -/
theorem gammaScaleSeparatedSimplePoleProfileEval_coeff_particleNumber
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous d) :
    (gammaScaleSeparatedSimplePoleProfileEval n P).coeff d =
      gammaScaleSeparatedPoleBoundaryEval
        (scaleSeparatedSimplePoleBoundaryTrace n P) := by
  change ((finiteScaleSeparatedSimplePoleProfileEval n P).map
    gammaScaleSeparatedPoleBoundaryEval).coeff d = _
  rw [Polynomial.coeff_map,
    finiteScaleSeparatedSimplePoleProfileEval_coeff_particleNumber hP]

/-- **Actual Gamma homogeneous particle trace.**  The particle-number coefficient of every
nonzero homogeneous differential source survives on the factorially scaled Gamma pole tower. -/
theorem gammaScaleSeparatedSimplePoleProfileEval_coeff_particleNumber_ne_zero
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    (gammaScaleSeparatedSimplePoleProfileEval n P).coeff d ≠ 0 := by
  rw [gammaScaleSeparatedSimplePoleProfileEval_coeff_particleNumber hP]
  exact gammaScaleSeparatedPoleBoundaryEval_ne_zero_of_isWeightedHomogeneous
    (scaleSeparatedSimplePoleBoundaryTrace_isWeightedHomogeneous hP)
    (scaleSeparatedSimplePoleBoundaryTrace_ne_zero hP0)

/-- The actual Gamma scale-separated pole degree is bounded below by particle number. -/
theorem particleNumber_le_gammaScaleSeparatedSimplePoleProfileEval_natDegree
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    d ≤ (gammaScaleSeparatedSimplePoleProfileEval n P).natDegree :=
  Polynomial.le_natDegree_of_ne_zero
    (gammaScaleSeparatedSimplePoleProfileEval_coeff_particleNumber_ne_zero hP hP0)

end

end GaloisForLFunctions.HTGeometry
