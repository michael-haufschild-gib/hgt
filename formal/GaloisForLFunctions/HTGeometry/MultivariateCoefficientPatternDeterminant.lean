import GaloisForLFunctions.HTGeometry.CoefficientPatternDeterminant
import GaloisForLFunctions.HTGeometry.MultivariateMultiIndexJet

/-!
# Multivariate coefficient-pattern determinants

The one-variable determinant infrastructure treats a coefficient monomial as a power of one base
coordinate.  Affine jet packets on `ℂᵈ` instead carry an arbitrary coordinate monomial.  This
file combines a coordinate exponent and a jet exponent into one monomial, proves the exact
evaluation formula, obtains a finite full-rank joint packet, and packages the determinant as a
polynomial in the row-jet variables after the base points are fixed.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Combine a coordinate monomial and a jet monomial on the disjoint union of their variables. -/
def multivariateExpandedMonomialExponent {d : ℕ} {σ : Type*}
    (coordinateExponent : Fin d →₀ ℕ) (jetExponent : σ →₀ ℕ) :
    Sum (Fin d) σ →₀ ℕ :=
  Finsupp.embDomain Function.Embedding.inl coordinateExponent +
    Finsupp.embDomain Function.Embedding.inr jetExponent

@[simp]
theorem multivariateExpandedMonomialExponent_inl {d : ℕ} {σ : Type*}
    (coordinateExponent : Fin d →₀ ℕ) (jetExponent : σ →₀ ℕ) (i : Fin d) :
    multivariateExpandedMonomialExponent coordinateExponent jetExponent (Sum.inl i) =
      coordinateExponent i := by
  classical
  simp [multivariateExpandedMonomialExponent, Finsupp.embDomain_apply]

@[simp]
theorem multivariateExpandedMonomialExponent_inr {d : ℕ} {σ : Type*}
    (coordinateExponent : Fin d →₀ ℕ) (jetExponent : σ →₀ ℕ) (i : σ) :
    multivariateExpandedMonomialExponent coordinateExponent jetExponent (Sum.inr i) =
      jetExponent i := by
  classical
  simp [multivariateExpandedMonomialExponent, Finsupp.embDomain_apply]

/-- The combined exponent remembers both of its disjoint components. -/
theorem multivariateExpandedMonomialExponent_injective {d : ℕ} {κ σ : Type*}
    (coordinateExponent : κ → Fin d →₀ ℕ) (jetExponent : κ → σ →₀ ℕ)
    (hpair : Function.Injective (fun k ↦ (coordinateExponent k, jetExponent k))) :
    Function.Injective (fun k ↦
      multivariateExpandedMonomialExponent (coordinateExponent k) (jetExponent k)) := by
  intro k l h
  apply hpair
  apply Prod.ext
  · apply Finsupp.ext
    intro i
    simpa using congrArg (fun e ↦ e (Sum.inl i)) h
  · apply Finsupp.ext
    intro i
    simpa using congrArg (fun e ↦ e (Sum.inr i)) h

/-- Evaluation of the combined monomial splits into the coordinate and jet monomial values. -/
theorem eval_multivariateExpandedMonomial {d : ℕ} {σ : Type*}
    (coordinateExponent : Fin d →₀ ℕ) (jetExponent : σ →₀ ℕ)
    (point : Sum (Fin d) σ → ℂ) :
    MvPolynomial.eval point
        (MvPolynomial.monomial
          (multivariateExpandedMonomialExponent coordinateExponent jetExponent) 1) =
      coordinateExponent.prod (fun i e ↦ point (Sum.inl i) ^ e) *
        jetExponent.prod (fun i e ↦ point (Sum.inr i) ^ e) := by
  classical
  rw [MvPolynomial.eval_monomial, one_mul]
  simp only [multivariateExpandedMonomialExponent]
  rw [Finsupp.prod_add_index]
  · rw [Finsupp.prod_embDomain, Finsupp.prod_embDomain]
  · intro a ha
    cases a <;> simp
  · intro a ha b₁ b₂
    simp [pow_add]

/-- Distinct decorated monomials admit a square joint packet of base-coordinate and jet values
with invertible evaluation matrix. -/
theorem exists_fullRank_multivariateExpandedMonomial_packet
    {d : ℕ} {row σ : Type*} [Fintype row] [DecidableEq row]
    (coordinateExponent : row → Fin d →₀ ℕ) (jetExponent : row → σ →₀ ℕ)
    (hpair : Function.Injective (fun k ↦ (coordinateExponent k, jetExponent k))) :
    ∃ base : row → Fin d → ℂ, ∃ target : row → σ → ℂ,
      IsUnit (Matrix.of fun a b ↦
        (coordinateExponent b).prod (fun i e ↦ base a i ^ e) *
          (jetExponent b).prod (fun i e ↦ target a i ^ e) : Matrix row row ℂ) := by
  let exponent : row → Sum (Fin d) σ →₀ ℕ := fun k ↦
    multivariateExpandedMonomialExponent (coordinateExponent k) (jetExponent k)
  have hexponent : Function.Injective exponent :=
    multivariateExpandedMonomialExponent_injective coordinateExponent jetExponent hpair
  obtain ⟨points, hfull⟩ := exists_fullRank_restrictedMonomialEvaluation_packet exponent
    hexponent (fun _ ↦ Set.univ) (fun _ ↦ Set.infinite_univ)
  refine ⟨fun a i ↦ points a (Sum.inl i), fun a i ↦ points a (Sum.inr i), ?_⟩
  simpa [exponent, eval_multivariateExpandedMonomial] using hfull

/-- The determinant polynomial for fixed multivariate base points and decorated jet monomials. -/
def multivariateCoefficientPatternDeterminant
    {d : ℕ} {row σ : Type*} [Fintype row] [DecidableEq row]
    (base : row → Fin d → ℂ)
    (coordinateExponent : row → Fin d →₀ ℕ) (jetExponent : row → σ →₀ ℕ) :
    MvPolynomial (row × σ) ℂ :=
  (Matrix.of fun a b ↦
    MvPolynomial.C ((coordinateExponent b).prod (fun i e ↦ base a i ^ e)) *
      rowJetMonomial a (jetExponent b)).det

/-- Evaluating the determinant polynomial gives the decorated-monomial evaluation determinant. -/
theorem eval_multivariateCoefficientPatternDeterminant
    {d : ℕ} {row σ : Type*} [Fintype row] [DecidableEq row]
    (base : row → Fin d → ℂ)
    (coordinateExponent : row → Fin d →₀ ℕ) (jetExponent : row → σ →₀ ℕ)
    (target : row × σ → ℂ) :
    MvPolynomial.eval target
        (multivariateCoefficientPatternDeterminant base coordinateExponent jetExponent) =
      (Matrix.of fun a b ↦
        (coordinateExponent b).prod (fun i e ↦ base a i ^ e) *
          (jetExponent b).prod (fun i e ↦ target (a, i) ^ e) : Matrix row row ℂ).det := by
  rw [multivariateCoefficientPatternDeterminant]
  change (MvPolynomial.eval target)
      (Matrix.det (Matrix.of fun a b ↦
        MvPolynomial.C ((coordinateExponent b).prod (fun i e ↦ base a i ^ e)) *
          rowJetMonomial a (jetExponent b))) = _
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [eval_rowJetMonomial]

/-- One invertible target packet certifies that the multivariate determinant polynomial is
nonzero. -/
theorem multivariateCoefficientPatternDeterminant_ne_zero_of_isUnit
    {d : ℕ} {row σ : Type*} [Fintype row] [DecidableEq row]
    (base : row → Fin d → ℂ)
    (coordinateExponent : row → Fin d →₀ ℕ) (jetExponent : row → σ →₀ ℕ)
    (target : row × σ → ℂ)
    (hfull : IsUnit (Matrix.of fun a b ↦
      (coordinateExponent b).prod (fun i e ↦ base a i ^ e) *
        (jetExponent b).prod (fun i e ↦ target (a, i) ^ e) : Matrix row row ℂ)) :
    multivariateCoefficientPatternDeterminant base coordinateExponent jetExponent ≠ 0 := by
  intro hzero
  have heval := congrArg (MvPolynomial.eval target) hzero
  rw [eval_multivariateCoefficientPatternDeterminant] at heval
  have hdet : (Matrix.of fun a b ↦
      (coordinateExponent b).prod (fun i e ↦ base a i ^ e) *
        (jetExponent b).prod (fun i e ↦ target (a, i) ^ e) : Matrix row row ℂ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hfull).ne_zero
  exact hdet (by simpa using heval)

end

end GaloisForLFunctions.HTGeometry
