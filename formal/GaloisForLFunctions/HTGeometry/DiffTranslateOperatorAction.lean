import GaloisForLFunctions.HTGeometry.LadderTranslateOperatorRow
import GaloisForLFunctions.HTGeometry.MeroGaugeCurvatureNecessity
import GaloisForLFunctions.HTGeometry.MultipleGammaTransverseDifference
import GaloisForLFunctions.HTGeometry.MeromorphicTranslationDifferentialOperator
import GaloisForLFunctions.HTGeometry.MeromorphicRankThreeSourceBoundary
import GaloisForLFunctions.HTGeometry.SourceBoundaryQuotientMatroid

/-!
# The constant-coefficient differential-translation operator ring in action

An element of `ℂ[δ, T₁,…,T_N]` is a polynomial in the translations with one-variable differential
operators as coefficients — that is, an element of `MvPolynomial (Fin N) ℂ[δ]`.  The monomial `n`
translates by `∑ₖ nₖ ωₖ` and its coefficient is the differential operator applied afterwards.

The action is a ring action: it is additive in the operator and in the argument, the unit acts as
the identity, and a product acts by composition, because translations commute with every
constant-coefficient differential operator and compose additively.

Two further laws govern it.

*It preserves the differentially algebraic sector.*  Translations, the derivation and multiplication
by constants all preserve differential algebraicity.  This is the forward inclusion of the
annihilator theorem, once the full ladder product has made the source differentially algebraic.

*A nonzero operator avoiding one direction is hypertranscendental on a solution of that direction's
ladder equation.*  The monomials then translate through shifts in distinct classes modulo `ω_j ℤ`,
so the value is a nonzero constant-coefficient differential-linear form in differentially
independent translates.  This is the reverse inclusion.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic zeroNomeScalarTower

/-! ## The action -/

/-- The action of a constant-coefficient differential-translation operator: the translation
monomials carry differential operators as coefficients. -/
def diffTranslateApply {N : ℕ} (ω : Fin N → ℂ) (P : MvPolynomial (Fin N) (Polynomial ℂ))
    (y : meroField (Set.univ : Set ℂ)) : meroField (Set.univ : Set ℂ) :=
  ∑ n ∈ P.support, differentialOperatorApply (MvPolynomial.coeff n P)
    (addTranslationMeroEquiv (monomialShift ω n) y)

/-- The action computed over any finite set containing the support. -/
theorem diffTranslateApply_eq_sum_of_subset {N : ℕ} (ω : Fin N → ℂ)
    (P : MvPolynomial (Fin N) (Polynomial ℂ)) (y : meroField (Set.univ : Set ℂ))
    {s : Finset (Fin N →₀ ℕ)} (hsub : P.support ⊆ s) :
    diffTranslateApply ω P y = ∑ n ∈ s, differentialOperatorApply (MvPolynomial.coeff n P)
      (addTranslationMeroEquiv (monomialShift ω n) y) := by
  rw [diffTranslateApply]
  refine Finset.sum_subset hsub fun n _ hn => ?_
  rw [MvPolynomial.notMem_support_iff.mp hn]
  exact differentialOperatorApply_zero _

theorem diffTranslateApply_zero_op {N : ℕ} (ω : Fin N → ℂ) (y : meroField (Set.univ : Set ℂ)) :
    diffTranslateApply ω 0 y = 0 := by
  rw [diffTranslateApply, MvPolynomial.support_zero, Finset.sum_empty]

theorem diffTranslateApply_monomial {N : ℕ} (ω : Fin N → ℂ) (n : Fin N →₀ ℕ) (L : Polynomial ℂ)
    (y : meroField (Set.univ : Set ℂ)) :
    diffTranslateApply ω (MvPolynomial.monomial n L) y
      = differentialOperatorApply L (addTranslationMeroEquiv (monomialShift ω n) y) := by
  classical
  by_cases hL : L = 0
  · subst hL
    rw [MvPolynomial.monomial_zero, diffTranslateApply_zero_op, differentialOperatorApply_zero]
  · rw [diffTranslateApply, MvPolynomial.support_monomial, if_neg hL, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]

/-! ## The action is a ring action -/

theorem monomialShift_add {N : ℕ} (ω : Fin N → ℂ) (a b : Fin N →₀ ℕ) :
    monomialShift ω (a + b) = monomialShift ω a + monomialShift ω b := by
  rw [monomialShift, monomialShift, monomialShift, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finsupp.add_apply]
  push_cast
  ring

theorem diffTranslateApply_add {N : ℕ} (ω : Fin N → ℂ)
    (P Q : MvPolynomial (Fin N) (Polynomial ℂ)) (y : meroField (Set.univ : Set ℂ)) :
    diffTranslateApply ω (P + Q) y = diffTranslateApply ω P y + diffTranslateApply ω Q y := by
  classical
  rw [diffTranslateApply_eq_sum_of_subset ω (P + Q) y (MvPolynomial.support_add),
    diffTranslateApply_eq_sum_of_subset ω P y Finset.subset_union_left,
    diffTranslateApply_eq_sum_of_subset ω Q y Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.coeff_add]
  exact differentialOperatorApply_add _ _ _

theorem diffTranslateApply_add_input {N : ℕ} (ω : Fin N → ℂ)
    (P : MvPolynomial (Fin N) (Polynomial ℂ)) (y z : meroField (Set.univ : Set ℂ)) :
    diffTranslateApply ω P (y + z) = diffTranslateApply ω P y + diffTranslateApply ω P z := by
  rw [diffTranslateApply, diffTranslateApply, diffTranslateApply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_add, differentialOperatorApply_add_input]

theorem diffTranslateApply_one {N : ℕ} (ω : Fin N → ℂ) (y : meroField (Set.univ : Set ℂ)) :
    diffTranslateApply ω 1 y = y := by
  have h1 : (1 : MvPolynomial (Fin N) (Polynomial ℂ)) = MvPolynomial.monomial 0 1 := by
    rw [MvPolynomial.monomial_zero', MvPolynomial.C_1]
  rw [h1, diffTranslateApply_monomial, monomialShift, differentialOperatorApply_one]
  simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_mul, Finset.sum_const_zero]
  exact addTranslationMeroEquiv_zero_apply y

/-- **A product of operators acts by composition.** -/
theorem diffTranslateApply_mul {N : ℕ} (ω : Fin N → ℂ)
    (P Q : MvPolynomial (Fin N) (Polynomial ℂ)) (y : meroField (Set.univ : Set ℂ)) :
    diffTranslateApply ω (P * Q) y = diffTranslateApply ω P (diffTranslateApply ω Q y) := by
  revert Q
  refine MvPolynomial.induction_on' P ?_ ?_
  · intro a L Q
    refine MvPolynomial.induction_on' Q ?_ ?_
    · intro b M
      rw [MvPolynomial.monomial_mul, diffTranslateApply_monomial, diffTranslateApply_monomial,
        diffTranslateApply_monomial, monomialShift_add, ← addTranslationMeroEquiv_add,
        addTranslationMeroEquiv_differentialOperatorApply,
        differentialOperatorApply_mul deriv_algebraMap_complex]
    · intro Q₁ Q₂ h₁ h₂
      rw [mul_add, diffTranslateApply_add, diffTranslateApply_add, diffTranslateApply_add_input,
        h₁, h₂]
  · intro P₁ P₂ h₁ h₂ Q
    rw [add_mul, diffTranslateApply_add, diffTranslateApply_add, h₁, h₂]

theorem diffTranslateApply_zero_input {N : ℕ} (ω : Fin N → ℂ)
    (P : MvPolynomial (Fin N) (Polynomial ℂ)) :
    diffTranslateApply ω P 0 = 0 := by
  rw [diffTranslateApply]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [map_zero, differentialOperatorApply_zero_input]

theorem diffTranslateApply_neg_input {N : ℕ} (ω : Fin N → ℂ)
    (P : MvPolynomial (Fin N) (Polynomial ℂ)) (y : meroField (Set.univ : Set ℂ)) :
    diffTranslateApply ω P (-y) = - diffTranslateApply ω P y := by
  have h := diffTranslateApply_add_input ω P y (-y)
  rw [add_neg_cancel, diffTranslateApply_zero_input] at h
  linear_combination -h

/-! ## Constants pass through the action -/

theorem differentialJet_algebraMap_complex_mul (c : ℂ) (n : ℕ)
    (y : meroField (Set.univ : Set ℂ)) :
    differentialJet n (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * y)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * differentialJet n y := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hd : (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c)′ = 0 := deriv_algebraMap_complex c
      rw [differentialJet_succ, differentialJet_succ, ih]
      simp [hd]

theorem differentialOperatorApply_algebraMap_complex_mul (L : Polynomial ℂ) (c : ℂ)
    (y : meroField (Set.univ : Set ℂ)) :
    differentialOperatorApply L (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * y)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * differentialOperatorApply L y := by
  classical
  rw [differentialOperatorApply, differentialOperatorApply, Polynomial.sum_def,
    Polynomial.sum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [differentialJet_algebraMap_complex_mul]
  ring

theorem diffTranslateApply_algebraMap_complex_mul {N : ℕ} (ω : Fin N → ℂ)
    (P : MvPolynomial (Fin N) (Polynomial ℂ)) (c : ℂ) (y : meroField (Set.univ : Set ℂ)) :
    diffTranslateApply ω P (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * y)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * diffTranslateApply ω P y := by
  rw [diffTranslateApply, diffTranslateApply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, addTranslationMeroEquiv_algebraMap_complex,
    differentialOperatorApply_algebraMap_complex_mul]

/-! ## The differentially algebraic sector is preserved -/

theorem differentialAlgebraicOver_differentialJet {n : ℕ} {y : meroField (Set.univ : Set ℂ)}
    (hy : DifferentialAlgebraicOver (RatFunc ℂ) y) :
    DifferentialAlgebraicOver (RatFunc ℂ) (differentialJet n y) := by
  induction n with
  | zero => simpa using hy
  | succ n ih =>
      rw [differentialJet_succ]
      exact differentialAlgebraicOver_deriv ih

/-- A constant-coefficient differential operator preserves differential algebraicity. -/
theorem differentialAlgebraicOver_differentialOperatorApply (L : Polynomial ℂ)
    {y : meroField (Set.univ : Set ℂ)} (hy : DifferentialAlgebraicOver (RatFunc ℂ) y) :
    DifferentialAlgebraicOver (RatFunc ℂ) (differentialOperatorApply L y) := by
  classical
  rw [differentialOperatorApply, Polynomial.sum_def]
  refine differentialAlgebraicOver_finset_sum fun n _ => ?_
  exact differentialAlgebraicOver_mul (differentialAlgebraicOver_algebraMap_complex _)
    (differentialAlgebraicOver_differentialJet hy)

/-- **The operator ring preserves the differentially algebraic sector.**  This is the forward
inclusion of the annihilator theorem: once the ladder product has made the source differentially
algebraic, every further operator keeps it there. -/
theorem differentialAlgebraicOver_diffTranslateApply {N : ℕ} (ω : Fin N → ℂ)
    (P : MvPolynomial (Fin N) (Polynomial ℂ)) {y : meroField (Set.univ : Set ℂ)}
    (hy : DifferentialAlgebraicOver (RatFunc ℂ) y) :
    DifferentialAlgebraicOver (RatFunc ℂ) (diffTranslateApply ω P y) := by
  refine differentialAlgebraicOver_finset_sum fun n _ => ?_
  exact differentialAlgebraicOver_differentialOperatorApply _
    (differentialAlgebraicOver_addTranslationMeroEquiv _ hy)

/-! ## A nonzero operator avoiding one direction -/

/-- **The reverse inclusion, in operator form.**  For rationally independent periods, a nonzero
constant-coefficient differential-translation operator that uses no `T_j` sends a solution of the
`ω_j` ladder equation outside the differentially algebraic sector. -/
theorem hypertranscendentalOver_diffTranslateApply_of_avoid {N : ℕ} (ω : Fin N → ℂ)
    (hQ : ∀ n : Fin N → ℤ, ∑ k, (n k : ℂ) * ω k = 0 → ∀ k, n k = 0)
    (j : Fin N) (b : ℂ) (φ : meroField (Set.univ : Set ℂ))
    (hφ : addTranslationMeroEquiv (ω j) φ
      = φ + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
        (1 / (RatFunc.X + RatFunc.C b)))
    (P : MvPolynomial (Fin N) (Polynomial ℂ)) (hP : P ≠ 0)
    (havoid : ∀ n ∈ P.support, n j = 0) :
    HypertranscendentalOver (RatFunc ℂ) (diffTranslateApply ω P φ) := by
  obtain ⟨n₀, hn₀⟩ := MvPolynomial.support_nonempty.mpr hP
  exact hypertranscendentalOver_ladderMonomialOperatorSum ω hQ j b φ hφ P.support havoid
    (fun n => MvPolynomial.coeff n P) hn₀ (MvPolynomial.mem_support_iff.mp hn₀)

end

end GaloisForLFunctions.HTGeometry
