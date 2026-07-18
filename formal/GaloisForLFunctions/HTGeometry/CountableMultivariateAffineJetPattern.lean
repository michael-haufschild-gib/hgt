import GaloisForLFunctions.HTGeometry.BaireGenericAvoidance
import GaloisForLFunctions.HTGeometry.ContinuousPolynomialDefect
import GaloisForLFunctions.HTGeometry.MultivariateCoefficientPatternDeterminant
import Mathlib.Tactic.DeriveCountable

/-!
# Countable multivariate affine-jet patterns

A finite differential relation on a countable affine palette is encoded without its complex
coefficient vector: the code records only the finite frame packet, the coordinate and mixed-jet
monomial exponents, and their distinctness.  One determinant condition then excludes every
coefficient vector on that support simultaneously.  This file packages the pattern, its continuous
jet-observation map, the closed polynomial defect, coefficient rigidity, and the countable Baire
assembly.  Construction of a full-rank witness from affine node separation and Hermite
interpolation is kept as the next geometric layer.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coordinate multi-indices of total order strictly below `m`. -/
abbrev MultiIndexBelow (d m : ℕ) := {a : Fin d →₀ ℕ // Finsupp.degree a < m}

noncomputable instance multiIndexBelowFintype (d m : ℕ) : Fintype (MultiIndexBelow d m) :=
  Finsupp.finite_of_degree_lt m |>.fintype

/-- Raw finite support of decorated monomials on a labelled affine-frame packet. -/
structure RawFiniteMultivariateAffineJetPattern (Λ : Type*) (d : ℕ) where
  frameCount : ℕ
  frameCode : Fin frameCount → Λ
  orders : Fin frameCount → ℕ
  monomialCount : ℕ
  coordinateExponent : Fin monomialCount → Fin d →₀ ℕ
  jetExponent : Fin monomialCount →
    ((Σ i, MultiIndexBelow d (orders i)) →₀ ℕ)
  deriving Countable

/-- Canonical finite pattern: frames do not collide and decorated monomials are distinct. -/
structure FiniteMultivariateAffineJetPattern (Λ : Type*) (d : ℕ)
    extends RawFiniteMultivariateAffineJetPattern Λ d where
  frameCode_injective : Function.Injective frameCode
  decoratedExponent_injective :
    Function.Injective (fun b ↦ (coordinateExponent b, jetExponent b))

noncomputable instance [Countable Λ] : Countable (FiniteMultivariateAffineJetPattern Λ d) := by
  have h : Function.Injective
      (FiniteMultivariateAffineJetPattern.toRawFiniteMultivariateAffineJetPattern :
        FiniteMultivariateAffineJetPattern Λ d → RawFiniteMultivariateAffineJetPattern Λ d) := by
    intro p q hpq
    cases p
    cases q
    simp_all
  exact h.countable

/-- Square row type belonging to a finite decorated-monomial support. -/
abbrev MultivariateAffinePatternRow {d : ℕ} {Λ : Type*}
    (p : FiniteMultivariateAffineJetPattern Λ d) := Fin p.monomialCount

/-- Finite mixed-jet variable set belonging to a pattern. -/
abbrev MultivariateAffinePatternJet {d : ℕ} {Λ : Type*}
    (p : FiniteMultivariateAffineJetPattern Λ d) :=
  Σ i, MultiIndexBelow d (p.orders i)

/-- Value of one coordinate monomial at a base point. -/
def multivariateCoordinateMonomial {d : ℕ}
    (a : Fin d →₀ ℕ) (z : Fin d → ℂ) : ℂ :=
  a.prod fun i e ↦ z i ^ e

/-- A mixed partial of an affine pullback, as a continuous linear observation of the source. -/
def affineMultiIndexJetEvalCLM {d : ℕ}
    (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (x : Fin d → ℂ) (a : Fin d →₀ ℕ) : MultivariateEntire d →L[ℂ] ℂ :=
  (multiIndexJetEvalCLM x a).comp (multivariateEntireAffinePullbackCLE e).toContinuousLinearMap

@[simp]
theorem affineMultiIndexJetEvalCLM_apply {d : ℕ}
    (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (x : Fin d → ℂ) (a : Fin d →₀ ℕ) (f : MultivariateEntire d) :
    affineMultiIndexJetEvalCLM e x a f =
      multiIndexJetEvalCLM x a (multivariateEntireAffinePullback e f) :=
  rfl

/-- All row-by-frame mixed jets occurring in a pattern, observed continuously from one source. -/
def multivariateAffinePatternObservationCLM {d : ℕ} {Λ : Type*}
    (frame : Λ → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (p : FiniteMultivariateAffineJetPattern Λ d)
    (base : MultivariateAffinePatternRow p → Fin d → ℂ) :
    MultivariateEntire d →L[ℂ]
      (MultivariateAffinePatternRow p × MultivariateAffinePatternJet p → ℂ) :=
  ContinuousLinearMap.pi fun x ↦
    affineMultiIndexJetEvalCLM (frame (p.frameCode x.2.1)) (base x.1) x.2.2.1

/-- The determinant defect associated with fixed sample bases for one finite pattern. -/
def multivariateAffinePatternDefect {d : ℕ} {Λ : Type*}
    (frame : Λ → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (p : FiniteMultivariateAffineJetPattern Λ d)
    (base : MultivariateAffinePatternRow p → Fin d → ℂ) : Set (MultivariateEntire d) :=
  {f | MvPolynomial.eval (multivariateAffinePatternObservationCLM frame p base f)
      (multivariateCoefficientPatternDeterminant
        base p.coordinateExponent p.jetExponent) = 0}

theorem multivariateAffinePatternDefect_isClosed {d : ℕ} {Λ : Type*}
    (frame : Λ → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (p : FiniteMultivariateAffineJetPattern Λ d)
    (base : MultivariateAffinePatternRow p → Fin d → ℂ) :
    IsClosed (multivariateAffinePatternDefect frame p base) :=
  isClosed_continuousLinearMap_mvPolynomial_zero
    (multivariateAffinePatternObservationCLM frame p base)
    (multivariateCoefficientPatternDeterminant base p.coordinateExponent p.jetExponent)

/-- Chosen finite witness data for a decorated pattern. -/
structure MultivariateAffinePatternWitness {d : ℕ} {Λ : Type*}
    (frame : Λ → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (p : FiniteMultivariateAffineJetPattern Λ d) where
  base : MultivariateAffinePatternRow p → Fin d → ℂ
  source : MultivariateEntire d
  escapes : MvPolynomial.eval
    (multivariateAffinePatternObservationCLM frame p base source)
    (multivariateCoefficientPatternDeterminant
      base p.coordinateExponent p.jetExponent) ≠ 0
  defect_interior_empty :
    interior (multivariateAffinePatternDefect frame p base) = ∅

/-- Avoid every chosen finite decorated-monomial determinant defect. -/
def multivariateAffinePatternResidualSet {d : ℕ} {Λ : Type*}
    (frame : Λ → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (witness : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      MultivariateAffinePatternWitness frame p) : Set (MultivariateEntire d) :=
  {f | ∀ p, f ∉ multivariateAffinePatternDefect frame p (witness p).base}

/-- **Countable multivariate pattern Baire law.** Given one genuine escaping source for each
finite decorated support, simultaneous determinant avoidance is dense residual. -/
theorem multivariateAffinePatternResidualSet_dense_residual
    {d : ℕ} {Λ : Type*} [Countable Λ]
    (frame : Λ → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (witness : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      MultivariateAffinePatternWitness frame p) :
    Dense (multivariateAffinePatternResidualSet frame witness) ∧
      multivariateAffinePatternResidualSet frame witness ∈ residual (MultivariateEntire d) := by
  let D : FiniteMultivariateAffineJetPattern Λ d → Set (MultivariateEntire d) :=
    fun p ↦ multivariateAffinePatternDefect frame p (witness p).base
  have hclosed : ∀ p, IsClosed (D p) := fun p ↦
    multivariateAffinePatternDefect_isClosed frame p (witness p).base
  have hnowhere : ∀ p, IsNowhereDense (D p) := fun p ↦
    GaloisForLFunctions.isNowhereDense_of_isClosed_of_interior_eq_empty
      (hclosed p) (witness p).defect_interior_empty
  have hopen : ∀ p, IsOpen (D p)ᶜ := fun p ↦ (hclosed p).isOpen_compl
  have hdense : ∀ p, Dense (D p)ᶜ := fun p ↦
    interior_eq_empty_iff_dense_compl.mp
      ((hclosed p).isNowhereDense_iff.mp (hnowhere p))
  have hset : multivariateAffinePatternResidualSet frame witness = ⋂ p, (D p)ᶜ := by
    ext f
    simp [multivariateAffinePatternResidualSet, D]
  rw [hset]
  exact ⟨dense_iInter_of_isOpen hopen hdense,
    countable_iInter_mem.mpr (fun p ↦ (hnowhere p).isMeagre)⟩

end

end GaloisForLFunctions.HTGeometry
