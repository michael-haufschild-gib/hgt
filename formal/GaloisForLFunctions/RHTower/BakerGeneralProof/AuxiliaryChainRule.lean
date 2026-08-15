import GaloisForLFunctions.RHTower.BakerGeneralProof.ComponentOperator
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Analytic chain rule for Baker auxiliary polynomials

The analytic auxiliary function evaluates a polynomial at the point
`(z, exp (λ₀z), …, exp (λₙ₋₁z))`.  Its ordinary complex derivative is first represented by a
derivation over `ℂ`.  The solved relation then decomposes that derivation into the commuting,
number-field-valued component operators from `ComponentOperator`.

This is the exact bridge between the analytic zero estimates and the algebraic auxiliary
polynomial construction.  The pivot relation is used only in
`analyticVector_eq_componentSum_X`; all chosen logarithm branches remain untouched.
-/

open scoped Classical

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Point of the analytic auxiliary curve: one additive and one exponential coordinate. -/
noncomputable def SolvedRelation.auxiliaryPoint
    (R : SolvedRelation) (z : ℂ) : R.Variable → ℂ
  | none => z
  | some i => Complex.exp (R.lambda i * z)

/-- Vector field of ordinary differentiation along the analytic auxiliary curve. -/
noncomputable def SolvedRelation.analyticVector
    (R : SolvedRelation) (v : R.Variable) : MvPolynomial R.Variable ℂ :=
  match v with
  | none => 1
  | some i => MvPolynomial.C (R.lambda i) * MvPolynomial.X (some i)

/-- Derivation of complex auxiliary polynomials induced by ordinary differentiation. -/
noncomputable def SolvedRelation.analyticDerivation
    (R : SolvedRelation) :
    Derivation ℂ (MvPolynomial R.Variable ℂ) (MvPolynomial R.Variable ℂ) :=
  MvPolynomial.mkDerivation ℂ R.analyticVector

@[simp] theorem SolvedRelation.analyticDerivation_X
    (R : SolvedRelation) (v : R.Variable) :
    R.analyticDerivation (MvPolynomial.X v) = R.analyticVector v := by
  exact MvPolynomial.mkDerivation_X (R := ℂ) R.analyticVector v

theorem SolvedRelation.differentiableAt_auxiliaryPoint
    (R : SolvedRelation) (z : ℂ) (v : R.Variable) :
    DifferentiableAt ℂ (fun w => R.auxiliaryPoint w v) z := by
  rcases v with _ | i
  · exact differentiableAt_id
  · exact (((hasDerivAt_id z).const_mul (R.lambda i)).cexp).differentiableAt

theorem SolvedRelation.deriv_auxiliaryPoint
    (R : SolvedRelation) (z : ℂ) (v : R.Variable) :
    deriv (fun w => R.auxiliaryPoint w v) z =
      MvPolynomial.eval (R.auxiliaryPoint z) (R.analyticVector v) := by
  rcases v with _ | i
  · simp [SolvedRelation.auxiliaryPoint, SolvedRelation.analyticVector]
  · simp [SolvedRelation.auxiliaryPoint, SolvedRelation.analyticVector, mul_comm]

theorem SolvedRelation.differentiableAt_eval_auxiliaryPoint
    (R : SolvedRelation) (z : ℂ) (P : MvPolynomial R.Variable ℂ) :
    DifferentiableAt ℂ
      (fun w => MvPolynomial.eval (R.auxiliaryPoint w) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval_C]
      exact differentiableAt_const a
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
  | mul_X p v hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      exact hp.mul (R.differentiableAt_auxiliaryPoint z v)

/-- Differentiating an evaluated complex auxiliary polynomial evaluates its analytic derivation. -/
theorem SolvedRelation.deriv_eval_auxiliaryPoint
    (R : SolvedRelation) (z : ℂ) (P : MvPolynomial R.Variable ℂ) :
    deriv (fun w => MvPolynomial.eval (R.auxiliaryPoint w) P) z =
      MvPolynomial.eval (R.auxiliaryPoint z) (R.analyticDerivation P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval_C]
      rw [show R.analyticDerivation (MvPolynomial.C a) = 0 from
        MvPolynomial.derivation_C R.analyticDerivation a, map_zero]
      exact deriv_const z a
  | add p q hp hq =>
      have hdp := R.differentiableAt_eval_auxiliaryPoint z p
      have hdq := R.differentiableAt_eval_auxiliaryPoint z q
      simp only [map_add]
      rw [deriv_fun_add hdp hdq, hp, hq]
  | mul_X p v hp =>
      have hdp := R.differentiableAt_eval_auxiliaryPoint z p
      have hdv := R.differentiableAt_auxiliaryPoint z v
      simp only [map_mul, MvPolynomial.eval_X]
      rw [deriv_fun_mul hdp hdv, hp, R.deriv_auxiliaryPoint z v]
      simp only [Derivation.leibniz, R.analyticDerivation_X, smul_eq_mul,
        map_add, map_mul, MvPolynomial.eval_X]
      ring

@[simp] theorem SolvedRelation.embedding_integerScalar
    (R : SolvedRelation) (c : ℤ) :
    R.embedding (R.integerScalar c) = (c : ℂ) := by
  simp [SolvedRelation.integerScalar]

@[simp] theorem SolvedRelation.embedding_scaledComponentCoeff
    (R : SolvedRelation) (c : ℤ) (d : R.Direction) :
    R.embedding (R.scaledComponentCoeff c d) =
      (c : ℂ) * match d with
        | none => R.constantCoeff
        | some i => R.coeff i := by
  rcases d with _ | i <;>
    simp [SolvedRelation.scaledComponentCoeff]

/-- Extend coefficients of a number-field auxiliary polynomial to the chosen complex embedding. -/
noncomputable def SolvedRelation.complexify
    (R : SolvedRelation) (P : MvPolynomial R.Variable R.CoefficientField) :
    MvPolynomial R.Variable ℂ :=
  MvPolynomial.map R.embedding P

/-- Complex total of the algebraic component derivations for unit integer scale. -/
noncomputable def SolvedRelation.componentSum
    (R : SolvedRelation) (P : MvPolynomial R.Variable R.CoefficientField) :
    MvPolynomial R.Variable ℂ :=
  R.complexify (R.componentDerivation 1 none P) +
    ∑ i : R.NonPivot,
      MvPolynomial.C (R.lambda i) *
        R.complexify (R.componentDerivation 1 (some i) P)

private theorem finite_component_leibniz
    {ι A : Type*} [Fintype ι] [CommSemiring A]
    (a x b d : A) (l bi di : ι → A) :
    a * b + x * d + ∑ i, l i * (a * bi i + x * di i) =
      a * (b + ∑ i, l i * bi i) + x * (d + ∑ i, l i * di i) := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  have ha : (∑ i, l i * (a * bi i)) = ∑ i, a * (l i * bi i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hx : (∑ i, l i * (x * di i)) = ∑ i, x * (l i * di i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [ha, hx]
  ac_rfl

private theorem finite_component_add
    {ι A : Type*} [Fintype ι] [NonUnitalNonAssocSemiring A]
    (a b : A) (l u v : ι → A) :
    a + b + ∑ i, l i * (u i + v i) =
      (a + ∑ i, l i * u i) + (b + ∑ i, l i * v i) := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ac_rfl

/-- The analytic vector field is exactly the sum of the solved relation components on generators. -/
theorem SolvedRelation.analyticVector_eq_componentSum_X
    (R : SolvedRelation) (v : R.Variable) :
    R.analyticVector v = R.componentSum (MvPolynomial.X v) := by
  rcases v with _ | j
  · simp [SolvedRelation.analyticVector, SolvedRelation.componentSum,
      SolvedRelation.complexify, SolvedRelation.componentVector]
  · by_cases hj : j = R.pivot
    · subst j
      have hne (i : R.NonPivot) : R.pivot ≠ (i : Fin R.n) := Ne.symm i.property
      simp [SolvedRelation.analyticVector, SolvedRelation.componentSum,
        SolvedRelation.complexify, SolvedRelation.componentVector, hne, R.pivot_eq]
      rw [add_mul, Finset.sum_mul]
      apply congrArg (fun Q =>
        MvPolynomial.C R.constantCoeff * MvPolynomial.X (some R.pivot) + Q)
      apply Finset.sum_congr rfl
      intro i _
      ring
    · let j' : R.NonPivot := ⟨j, hj⟩
      rw [SolvedRelation.componentSum]
      rw [Finset.sum_eq_single j']
      · simp [SolvedRelation.analyticVector, SolvedRelation.complexify,
          SolvedRelation.componentVector, hj, j']
      · intro i _ hne
        have hji : j ≠ (i : Fin R.n) := by
          intro h
          apply hne
          exact Subtype.ext h.symm
        simp [SolvedRelation.complexify, SolvedRelation.componentVector, hj, hji]
      · simp

/-- The complex component sum satisfies the product rule on an adjoining generator. -/
theorem SolvedRelation.componentSum_mul_X
    (R : SolvedRelation) (p : MvPolynomial R.Variable R.CoefficientField)
    (v : R.Variable) :
    R.componentSum (p * MvPolynomial.X v) =
      R.complexify p * R.componentSum (MvPolynomial.X v) +
        MvPolynomial.X v * R.componentSum p := by
  have hcomponent (d : R.Direction) :
      R.complexify (R.componentDerivation 1 d (p * MvPolynomial.X v)) =
        R.complexify p * R.complexify (R.componentDerivation 1 d (MvPolynomial.X v)) +
          MvPolynomial.X v * R.complexify (R.componentDerivation 1 d p) := by
    simp [SolvedRelation.complexify, Derivation.leibniz, smul_eq_mul]
  unfold SolvedRelation.componentSum
  rw [hcomponent none]
  simp_rw [hcomponent]
  exact finite_component_leibniz
    (R.complexify p) (MvPolynomial.X v)
    (R.complexify (R.componentDerivation 1 none (MvPolynomial.X v)))
    (R.complexify (R.componentDerivation 1 none p))
    (fun i : R.NonPivot => MvPolynomial.C (R.lambda i))
    (fun i : R.NonPivot =>
      R.complexify (R.componentDerivation 1 (some i) (MvPolynomial.X v)))
    (fun i : R.NonPivot => R.complexify (R.componentDerivation 1 (some i) p))

/-- The complex component sum is additive. -/
theorem SolvedRelation.componentSum_add
    (R : SolvedRelation) (p q : MvPolynomial R.Variable R.CoefficientField) :
    R.componentSum (p + q) = R.componentSum p + R.componentSum q := by
  unfold SolvedRelation.componentSum SolvedRelation.complexify
  simp only [map_add]
  exact finite_component_add
    (MvPolynomial.map R.embedding (R.componentDerivation 1 none p))
    (MvPolynomial.map R.embedding (R.componentDerivation 1 none q))
    (fun i : R.NonPivot => MvPolynomial.C (R.lambda i))
    (fun i : R.NonPivot =>
      MvPolynomial.map R.embedding (R.componentDerivation 1 (some i) p))
    (fun i : R.NonPivot =>
      MvPolynomial.map R.embedding (R.componentDerivation 1 (some i) q))

/-- Ordinary differentiation along the auxiliary curve is the complexified component sum. -/
theorem SolvedRelation.analyticDerivation_complexify_eq_componentSum
    (R : SolvedRelation) (P : MvPolynomial R.Variable R.CoefficientField) :
    R.analyticDerivation (R.complexify P) = R.componentSum P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp [SolvedRelation.complexify, SolvedRelation.componentSum]
  | add p q hp hq =>
      rw [show R.complexify (p + q) = R.complexify p + R.complexify q by
        simp [SolvedRelation.complexify], map_add, hp, hq, R.componentSum_add]
  | mul_X p v hp =>
      rw [show R.complexify (p * MvPolynomial.X v) =
        R.complexify p * MvPolynomial.X v by
          simp [SolvedRelation.complexify]]
      rw [Derivation.leibniz, R.analyticDerivation_X, hp,
        R.analyticVector_eq_componentSum_X, R.componentSum_mul_X]
      simp only [smul_eq_mul]

end GaloisForLFunctions.RHTower.BakerGeneralProof
