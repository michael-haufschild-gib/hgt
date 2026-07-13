import GaloisForLFunctions.HTGeometry.PureSingularCarrierTrichotomy
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# The global orthonormal-polynomial carrier

This module proves the infinite-dimensional carrier statement that is only implicit in finite
inverse-Cholesky matrices.  For a finite circle measure with infinite support, the analytic
monomials are linearly independent.  If their span is dense, normalized Gram--Schmidt therefore
produces a Hilbert basis of `L²(mu)` and hence a unitary map from coefficient `ell²` onto
`L²(mu)`.

The density hypothesis is then discharged from the exact Riesz-brothers interface for a measure
singular to circle Lebesgue measure.  Thus the literature input ends at one-sided Fourier
rigidity; the Hilbert-basis and unitary conclusions are unconditional Lean deductions.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix MeasureTheory Polynomial Submodule
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- Infinite support makes the full analytic monomial sequence linearly independent in
`L²(mu)`. -/
theorem linearIndependent_circleMonomialLp_of_infiniteSupport
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite) :
    LinearIndependent ℂ (circleMonomialLp mu) := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  let p : Polynomial ℂ :=
    ∑ n ∈ s, Polynomial.C (c n) * Polynomial.X ^ n
  let f : Circle → ℂ := fun z => p.eval (z : ℂ)
  have hfcont : Continuous f :=
    p.continuous.comp continuous_subtype_val
  have hsumcoe_general : ∀ t : Finset ℕ,
      ⇑(∑ n ∈ t, c n • circleMonomialLp mu n) =ᵐ[mu]
        fun z : Circle => ∑ n ∈ t, c n * (z : ℂ) ^ n := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 mu)
    | @insert a u ha ih =>
        rw [Finset.sum_insert ha]
        filter_upwards [Lp.coeFn_add
            (c a • circleMonomialLp mu a)
            (∑ n ∈ u, c n • circleMonomialLp mu n),
          Lp.coeFn_smul (c a) (circleMonomialLp mu a),
          circleMonomialLp_coeFn_ae mu a, ih] with z hadd hsmul hmono htail
        rw [hadd]
        change ⇑(c a • circleMonomialLp mu a) z +
          ⇑(∑ n ∈ u, c n • circleMonomialLp mu n) z = _
        rw [hsmul, Pi.smul_apply, hmono, htail]
        simp [Finset.sum_insert ha]
  have hsumcoe :
      ⇑(∑ n ∈ s, c n • circleMonomialLp mu n) =ᵐ[mu] f := by
    simpa [f, p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] using hsumcoe_general s
  have hfzero : f =ᵐ[mu] 0 :=
    hsumcoe.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hc)
  have hsuppzero : ∀ z ∈ mu.support, f z = 0 :=
    circle_continuous_eq_zero_on_support_of_ae_eq_zero mu f hfcont hfzero
  let rootsOnSupport : Set ℂ := ((fun z : Circle => (z : ℂ)) '' mu.support)
  have hrootsInfinite : rootsOnSupport.Infinite := by
    apply hmu.image
    exact Subtype.val_injective.injOn
  have hroot : rootsOnSupport ⊆ {z : ℂ | p.IsRoot z} := by
    rintro z ⟨w, hw, rfl⟩
    exact hsuppzero w hw
  have hpzero : p = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot p (hrootsInfinite.mono hroot)
  have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff i) hpzero
  simpa [p, hi] using hcoeff

/-- The canonical infinite orthonormal-polynomial sequence obtained by normalized Gram--Schmidt
from `1,z,z²,...` in `L²(mu)`. -/
noncomputable def circleOrthonormalPolynomial
    (mu : Measure Circle) [IsFiniteMeasure mu] (n : ℕ) : Lp ℂ 2 mu :=
  InnerProductSpace.gramSchmidtNormed ℂ (circleMonomialLp mu) n

/-- Infinite support makes the canonical orthonormal-polynomial sequence orthonormal. -/
theorem circleOrthonormalPolynomial_orthonormal_of_infiniteSupport
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite) :
    Orthonormal ℂ (circleOrthonormalPolynomial mu) := by
  exact InnerProductSpace.gramSchmidtNormed_orthonormal
    (linearIndependent_circleMonomialLp_of_infiniteSupport mu hmu)

/-- Normalized Gram--Schmidt preserves the algebraic analytic-polynomial span. -/
theorem span_circleOrthonormalPolynomial_eq_analyticMonomialSpan
    (mu : Measure Circle) [IsFiniteMeasure mu] :
    Submodule.span ℂ (Set.range (circleOrthonormalPolynomial mu)) =
      analyticMonomialSpan mu := by
  unfold circleOrthonormalPolynomial analyticMonomialSpan
  rw [InnerProductSpace.span_gramSchmidtNormed_range,
    InnerProductSpace.span_gramSchmidt]

/-- The polynomial synthesized by one row of the finite canonical inverse-Cholesky frame.  The
coefficient is conjugated because mathlib's complex inner product is conjugate-linear in its
first argument. -/
noncomputable def circleCanonicalFramePolynomial
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (N : ℕ) (i : Fin (N + 1)) : Lp ℂ 2 mu :=
  ∑ k : Fin (N + 1),
    star (circleMeasureCanonicalFrameTower mu hmu N i k) • circleMonomialLp mu k

/-- Every finite canonical inverse-Cholesky frame synthesizes an actual orthonormal polynomial
family in `L²(mu)`.  This is the exact Hilbert-space meaning of `C G Cᴴ = I`. -/
theorem circleCanonicalFramePolynomial_orthonormal
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (hmu : mu.support.Infinite) (N : ℕ) :
    Orthonormal ℂ (circleCanonicalFramePolynomial mu hmu N) := by
  rw [orthonormal_iff_ite]
  intro i j
  let C := circleMeasureCanonicalFrameTower mu hmu N
  let b : Fin (N + 1) → Lp ℂ 2 mu := fun k => circleMonomialLp mu k
  let x : Fin (N + 1) → ℂ := fun k => star (C i k)
  let y : Fin (N + 1) → ℂ := fun k => star (C j k)
  calc
    inner ℂ (circleCanonicalFramePolynomial mu hmu N i)
        (circleCanonicalFramePolynomial mu hmu N j) =
        star x ⬝ᵥ (Matrix.gram ℂ b) *ᵥ y := by
      exact (Matrix.star_dotProduct_gram_mulVec b x y).symm
    _ = (C * circleMeasureGramTower mu N * Cᴴ) i j := by
      rw [circleMeasureGramTower_eq_gram]
      simp [C, b, x, y, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul, mul_assoc]
    _ = if i = j then 1 else 0 := by
      have h := congrFun (congrFun
        (circleMeasureCanonicalFrameTower_isCanonical mu hmu N).1 i) j
      simpa [C, Matrix.one_apply] using h

/-- Passing from level `N` to level `N+1` leaves every previously synthesized polynomial
unchanged.  This is the Hilbert-space form of leading-principal frame coherence. -/
theorem circleCanonicalFramePolynomial_castSucc
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (hmu : mu.support.Infinite) (N : ℕ) (i : Fin (N + 1)) :
    circleCanonicalFramePolynomial mu hmu (N + 1) i.castSucc =
      circleCanonicalFramePolynomial mu hmu N i := by
  unfold circleCanonicalFramePolynomial
  rw [Fin.sum_univ_castSucc]
  have hcoh := circleMeasureCanonicalFrameTower_leadingPrincipal mu hmu N
  have hentry : ∀ k : Fin (N + 1),
      circleMeasureCanonicalFrameTower mu hmu (N + 1) i.castSucc k.castSucc =
        circleMeasureCanonicalFrameTower mu hmu N i k := by
    intro k
    exact congrFun (congrFun hcoh i) k
  simp_rw [hentry]
  have hlast : circleMeasureCanonicalFrameTower mu hmu (N + 1)
      i.castSucc (Fin.last (N + 1)) = 0 := by
    exact (circleMeasureCanonicalFrameTower_isCanonical mu hmu (N + 1)).2.1 (by simp)
  rw [hlast, star_zero, zero_smul, add_zero]
  rfl

/-- One-sided Fourier rigidity makes the canonical orthonormal polynomials complete. -/
theorem circleOrthonormalPolynomial_closure_eq_top_of_oneSidedFourierRigid
    (mu : Measure Circle) [IsFiniteMeasure mu] (hrigid : IsOneSidedFourierRigid mu) :
    (Submodule.span ℂ (Set.range (circleOrthonormalPolynomial mu))).topologicalClosure = ⊤ := by
  rw [span_circleOrthonormalPolynomial_eq_analyticMonomialSpan]
  exact analyticMonomialSpan_closure_eq_top_of_oneSidedFourierRigid mu hrigid

/-- Infinite support plus one-sided Fourier rigidity upgrades the canonical orthonormal
polynomials to a Hilbert basis of `L²(mu)`. -/
noncomputable def circlePolynomialHilbertBasis
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hrigid : IsOneSidedFourierRigid mu) :
    HilbertBasis ℕ ℂ (Lp ℂ 2 mu) :=
  HilbertBasis.mk
    (circleOrthonormalPolynomial_orthonormal_of_infiniteSupport mu hmu)
    (circleOrthonormalPolynomial_closure_eq_top_of_oneSidedFourierRigid mu hrigid).ge

@[simp]
theorem circlePolynomialHilbertBasis_apply
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hrigid : IsOneSidedFourierRigid mu) (n : ℕ) :
    circlePolynomialHilbertBasis mu hmu hrigid n =
      circleOrthonormalPolynomial mu n := by
  exact congrFun (HilbertBasis.coe_mk
    (circleOrthonormalPolynomial_orthonormal_of_infiniteSupport mu hmu)
    (circleOrthonormalPolynomial_closure_eq_top_of_oneSidedFourierRigid mu hrigid).ge) n

/-- The global canonical carrier: coefficient `ell²` is unitarily identified with `L²(mu)` by
sending the standard basis to the canonical orthonormal polynomials. -/
noncomputable def circlePolynomialCarrierUnitary
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hrigid : IsOneSidedFourierRigid mu) :
    CoefficientL2 ≃ₗᵢ[ℂ] Lp ℂ 2 mu :=
  (circlePolynomialHilbertBasis mu hmu hrigid).repr.symm

@[simp]
theorem circlePolynomialCarrierUnitary_apply_single
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hrigid : IsOneSidedFourierRigid mu) (n : ℕ) :
    circlePolynomialCarrierUnitary mu hmu hrigid (lp.single 2 n 1) =
      circleOrthonormalPolynomial mu n := by
  rw [circlePolynomialCarrierUnitary, HilbertBasis.repr_symm_single,
    circlePolynomialHilbertBasis_apply]

/-- **Pure-singular unitary carrier law.**  The exact Riesz-brothers conclusion and singularity
produce the global unitary carrier entirely inside Lean. -/
theorem exists_circlePolynomialCarrierUnitary_of_rieszBrothers
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hsing : mu ⟂ₘ circleLebesgue)
    (hriesz : HasRieszBrothersDensityConclusion mu circleLebesgue) :
    ∃ U : CoefficientL2 ≃ₗᵢ[ℂ] Lp ℂ 2 mu,
      ∀ n : ℕ, U (lp.single 2 n 1) = circleOrthonormalPolynomial mu n := by
  let hrigid : IsOneSidedFourierRigid mu :=
    oneSidedFourierRigid_of_mutuallySingular_of_rieszBrothers
      mu circleLebesgue hsing hriesz
  exact ⟨circlePolynomialCarrierUnitary mu hmu hrigid,
    circlePolynomialCarrierUnitary_apply_single mu hmu hrigid⟩

end

end GaloisForLFunctions.HTGeometry
