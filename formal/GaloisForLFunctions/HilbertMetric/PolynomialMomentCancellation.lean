import GaloisForLFunctions.HilbertMetric.UnisolventEvaluation
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Polynomial moment cancellation for coherent collisions

Distinct multivariate monomials are independent as real-valued functions.  Combining this fact
with the unconditional unisolvent-node theorem produces distinct Euclidean nodes and exact dual
coefficients: every selected coefficient row kills all truncated monomial moments except one.

The final theorem specializes the construction to all multi-indices of total degree at most `M`.
This is the algebraic cancellation mechanism needed before applying coherent-kernel jets; no
sampling points, inverse matrices, or rank certificates are assumed.
-/

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Evaluation of real multivariate polynomials as a linear map into real-valued functions. -/
def monomialEvaluationLinearMap (τ : Type*) :
    MvPolynomial τ ℝ →ₗ[ℝ] ((τ → ℝ) → ℝ) where
  toFun P x := MvPolynomial.eval x P
  map_add' P Q := by funext x; simp
  map_smul' c P := by funext x; simp

/-- A real multivariate polynomial is determined by all of its real evaluations. -/
theorem monomialEvaluationLinearMap_injective (τ : Type*) :
    Function.Injective (monomialEvaluationLinearMap τ) := by
  intro P Q h
  apply MvPolynomial.funext
  intro x
  exact congrFun h x

/-- The monomial feature attached to a finitely supported exponent vector. -/
def monomialFeature {κ τ : Type*} (exponent : κ → (τ →₀ ℕ))
    (i : κ) (x : τ → ℝ) : ℝ :=
  MvPolynomial.eval x (MvPolynomial.monomial (exponent i) 1)

/-- Any injectively indexed family of real monomials is linearly independent as a family of
functions on the full real coordinate space. -/
theorem monomialFeature_linearIndependent {κ τ : Type*}
    (exponent : κ → (τ →₀ ℕ)) (hexponent : Function.Injective exponent) :
    LinearIndependent ℝ (monomialFeature exponent) := by
  have hmono : LinearIndependent ℝ
      (fun e : τ →₀ ℕ => MvPolynomial.monomial e (1 : ℝ)) :=
    (MvPolynomial.basisMonomials τ ℝ).linearIndependent
  have hfamily := hmono.comp exponent hexponent
  have hmapped := hfamily.map' (monomialEvaluationLinearMap τ)
    (LinearMap.ker_eq_bot.mpr (monomialEvaluationLinearMap_injective τ))
  simpa [monomialFeature, monomialEvaluationLinearMap, Function.comp_def] using hmapped

/-- A finite family of distinct monomials admits distinct nodes and exact Kronecker-delta moment
coefficients. -/
theorem exists_injective_nodes_monomial_delta {κ τ : Type*}
    [Fintype κ] [DecidableEq κ]
    (exponent : κ → (τ →₀ ℕ)) (hexponent : Function.Injective exponent) :
    ∃ (nodes : κ → (τ → ℝ)) (coefficient : κ → κ → ℝ), Function.Injective nodes ∧
      ∀ q r, ∑ i, coefficient q i * monomialFeature exponent r (nodes i) =
        if q = r then 1 else 0 :=
  exists_injective_nodes_delta_moments _
    (monomialFeature_linearIndependent exponent hexponent)

/-- Multi-indices on `d` coordinates whose total degree is at most `M`. -/
abbrev TruncatedMultiIndex (d M : ℕ) :=
  {e : Fin d → Fin (M + 1) // ∑ i, (e i : ℕ) ≤ M}

instance (d M : ℕ) : Fintype (TruncatedMultiIndex d M) := inferInstance
instance (d M : ℕ) : DecidableEq (TruncatedMultiIndex d M) := inferInstance

/-- A bounded multi-index as a finitely supported exponent vector. -/
def TruncatedMultiIndex.exponent {d M : ℕ} (e : TruncatedMultiIndex d M) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e.1 i : ℕ))

/-- Distinct bounded multi-indices have distinct finitely supported exponent vectors. -/
theorem TruncatedMultiIndex.exponent_injective {d M : ℕ} :
    Function.Injective (TruncatedMultiIndex.exponent (d := d) (M := M)) := by
  intro e f h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact DFunLike.congr_fun h i

/-- **Truncated polynomial cancellation law.**  There are pairwise distinct nodes in `ℝ^d` and
dual coefficient rows that isolate every monomial of total degree at most `M` exactly. -/
theorem exists_truncatedMonomial_unisolvent_delta (d M : ℕ) :
    ∃ (nodes : TruncatedMultiIndex d M → (Fin d → ℝ))
      (coefficient : TruncatedMultiIndex d M → TruncatedMultiIndex d M → ℝ),
      Function.Injective nodes ∧
      ∀ q r, ∑ i, coefficient q i *
          monomialFeature TruncatedMultiIndex.exponent r (nodes i) =
        if q = r then 1 else 0 :=
  exists_injective_nodes_monomial_delta _ TruncatedMultiIndex.exponent_injective

end

end GaloisForLFunctions.HilbertMetric
