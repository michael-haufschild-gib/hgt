import GaloisForLFunctions.RHTower.BakerGeneralStatement

/-!
# Solved relations for full Baker theorem

A hypothetical inhomogeneous relation is solved at an arbitrary pivot logarithm. The structure
retains arbitrary chosen branches, their `ℚ`-linear independence, algebraicity of every exponential,
and algebraicity of the solved coefficients. One canonical number field contains both families,
with independent simultaneous integral scales for coefficients and bases.
-/

open scoped Classical

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- A hypothetical inhomogeneous algebraic relation solved for one chosen logarithm. -/
structure SolvedRelation where
  n : ℕ
  lambda : Fin n → ℂ
  exp_algebraic : ∀ i, IsAlgebraic ℚ (Complex.exp (lambda i))
  lambda_independent : LinearIndependent ℚ lambda
  pivot : Fin n
  constantCoeff : ℂ
  coeff : {i : Fin n // i ≠ pivot} → ℂ
  constantCoeff_algebraic : IsAlgebraic ℚ constantCoeff
  coeff_algebraic : ∀ i, IsAlgebraic ℚ (coeff i)
  pivot_eq : lambda pivot = constantCoeff +
    ∑ i : {i : Fin n // i ≠ pivot}, coeff i * lambda i

abbrev SolvedRelation.NonPivot (R : SolvedRelation) :=
  {i : Fin R.n // i ≠ R.pivot}

/-- Indices for all algebraic data: exponential bases and solved coefficients. -/
abbrev SolvedRelation.DataIndex (R : SolvedRelation) :=
  Sum (Fin R.n) (Option R.NonPivot)

noncomputable def SolvedRelation.data (R : SolvedRelation) : R.DataIndex → ℂ
  | Sum.inl i => Complex.exp (R.lambda i)
  | Sum.inr none => R.constantCoeff
  | Sum.inr (some i) => R.coeff i

theorem SolvedRelation.data_algebraic (R : SolvedRelation) (i : R.DataIndex) :
    IsAlgebraic ℚ (R.data i) := by
  rcases i with i | (_ | i)
  · exact R.exp_algebraic i
  · exact R.constantCoeff_algebraic
  · exact R.coeff_algebraic i

/-- Canonical number field containing every exponential base and solved coefficient. -/
abbrev SolvedRelation.CoefficientField (R : SolvedRelation) : Type :=
  AlgebraicFamilyField R.data

noncomputable instance (R : SolvedRelation) : NumberField R.CoefficientField :=
  algebraicFamilyNumberField R.data R.data_algebraic

noncomputable def SolvedRelation.embedding (R : SolvedRelation) :
    R.CoefficientField →+* ℂ :=
  algebraicFamilyEmbedding R.data

noncomputable def SolvedRelation.baseLift (R : SolvedRelation) (i : Fin R.n) :
    R.CoefficientField :=
  algebraicFamilyLift R.data (Sum.inl i)

noncomputable def SolvedRelation.componentCoeffLift
    (R : SolvedRelation) (i : Option R.NonPivot) : R.CoefficientField :=
  algebraicFamilyLift R.data (Sum.inr i)

@[simp] theorem SolvedRelation.embedding_baseLift (R : SolvedRelation) (i : Fin R.n) :
    R.embedding (R.baseLift i) = Complex.exp (R.lambda i) := rfl

@[simp] theorem SolvedRelation.embedding_componentCoeffLift
    (R : SolvedRelation) (i : Option R.NonPivot) :
    R.embedding (R.componentCoeffLift i) =
      match i with
      | none => R.constantCoeff
      | some j => R.coeff j := by
  cases i <;> rfl

/-- One nonzero integer clears every solved-relation coefficient, including the constant term. -/
theorem SolvedRelation.exists_component_common_integer_scale (R : SolvedRelation) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ i, IsIntegral ℤ (c • R.componentCoeffLift i) := by
  let s : Finset R.CoefficientField :=
    Finset.univ.image R.componentCoeffLift
  obtain ⟨c, hc, hint⟩ :=
    exists_integral_multiples ℤ ℚ (L := R.CoefficientField) s
  refine ⟨c, hc, fun i => hint (R.componentCoeffLift i) ?_⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- One nonzero integer clears every algebraic exponential base. -/
theorem SolvedRelation.exists_base_common_integer_scale (R : SolvedRelation) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ i, IsIntegral ℤ (d • R.baseLift i) := by
  let s : Finset R.CoefficientField := Finset.univ.image R.baseLift
  obtain ⟨d, hd, hint⟩ :=
    exists_integral_multiples ℤ ℚ (L := R.CoefficientField) s
  refine ⟨d, hd, fun i => hint (R.baseLift i) ?_⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

end GaloisForLFunctions.RHTower.BakerGeneralProof
