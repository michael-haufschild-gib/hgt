import GaloisForLFunctions.RHTower.EntireExponentialMomentPolynomialDensity
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Exponential-moment polynomial sign cone

Let `mu` be a finite real measure whose bilateral moment-generating function exists on the
whole real axis.  A bounded measurable multiplier `J` defines a continuous quadratic form on
`L²(mu)`.  Since the real polynomials are dense, positivity of that form on polynomials already
forces `J >= 0` almost everywhere.  If `mu` is positive on nonempty open sets and `J` is
continuous, the conclusion is pointwise.

This is the complete cone theorem behind Gaussian-window moment tests: an infinite polynomial
moment tower does not merely approximate the sign cone; it equals it.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RHTower

variable {mu : Measure ℝ}

/-- A bounded measurable function represented in `L∞(mu)`. -/
def linftyMultiplier (J : ℝ → ℝ) (hJ : MemLp J ∞ mu) : Lp ℝ ∞ mu :=
  hJ.toLp J

theorem linftyMultiplier_ae (J : ℝ → ℝ) (hJ : MemLp J ∞ mu) :
    linftyMultiplier J hJ =ᵐ[mu] J :=
  hJ.coeFn_toLp

/-- Multiplication by an `L∞` function, as a bounded operator on `L²`. -/
def linftyMultiplierOperator (J : ℝ → ℝ) (hJ : MemLp J ∞ mu) :
    Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu :=
  ((ContinuousLinearMap.lsmul ℝ ℝ).holderL mu ∞ 2 2) (linftyMultiplier J hJ)

theorem linftyMultiplierOperator_ae (J : ℝ → ℝ) (hJ : MemLp J ∞ mu)
    (v : Lp ℝ 2 mu) :
    linftyMultiplierOperator J hJ v =ᵐ[mu] fun x ↦ J x * v x := by
  refine ((ContinuousLinearMap.lsmul ℝ ℝ).coeFn_holder
    (linftyMultiplier J hJ) v).trans ?_
  filter_upwards [linftyMultiplier_ae J hJ] with x hx
  rw [hx]
  exact ContinuousLinearMap.lsmul_apply ℝ ℝ _ _

/-- The bounded multiplier quadratic form on `L²(mu)`. -/
def linftyMultiplierQuadratic (J : ℝ → ℝ) (hJ : MemLp J ∞ mu)
    (v : Lp ℝ 2 mu) : ℝ :=
  inner ℝ v (linftyMultiplierOperator J hJ v)

theorem continuous_linftyMultiplierQuadratic (J : ℝ → ℝ) (hJ : MemLp J ∞ mu) :
    Continuous (linftyMultiplierQuadratic J hJ) :=
  continuous_id.inner (linftyMultiplierOperator J hJ).continuous

theorem linftyMultiplierQuadratic_eq_integral (J : ℝ → ℝ) (hJ : MemLp J ∞ mu)
    (v : Lp ℝ 2 mu) :
    linftyMultiplierQuadratic J hJ v = ∫ x, (v x) ^ 2 * J x ∂mu := by
  rw [linftyMultiplierQuadratic, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [linftyMultiplierOperator_ae J hJ v] with x hx
  rw [hx, RCLike.inner_apply]
  simp
  ring

/-- Every vector in the real monomial span has an almost-everywhere polynomial representative. -/
theorem exists_polynomial_ae_eq_of_mem_realMonomialSpan
    (hmu : HasEntireExponentialMoments mu) {v : Lp ℝ 2 mu}
    (hv : v ∈ realMonomialSpan mu hmu) :
    ∃ p : Polynomial ℝ, v =ᵐ[mu] fun x ↦ p.eval x := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨n, rfl⟩ := hv
      refine ⟨Polynomial.X ^ n, ?_⟩
      simpa only [Polynomial.eval_X_pow] using realMonomialLp_ae mu hmu n
  | zero =>
      refine ⟨0, ?_⟩
      filter_upwards [Lp.coeFn_zero ℝ 2 mu] with x hx
      simpa using hx
  | add u v _ _ hu hv =>
      obtain ⟨p, hp⟩ := hu
      obtain ⟨q, hq⟩ := hv
      refine ⟨p + q, ?_⟩
      filter_upwards [Lp.coeFn_add u v, hp, hq] with x huv hup hvq
      rw [huv]
      change u x + v x = _
      rw [hup, hvq, Polynomial.eval_add]
  | smul c v _ hv =>
      obtain ⟨p, hp⟩ := hv
      refine ⟨c • p, ?_⟩
      filter_upwards [Lp.coeFn_smul c v, hp] with x hcv hvp
      rw [hcv]
      change c * v x = _
      rw [hvp, Polynomial.eval_smul]
      rfl

/-- Polynomial-square positivity extends to the whole `L²` space whenever polynomials are
dense. -/
theorem linftyMultiplierQuadratic_nonnegative_of_polynomial
    [IsFiniteMeasure mu] (hmu : HasEntireExponentialMoments mu)
    (J : ℝ → ℝ) (hJ : MemLp J ∞ mu)
    (hpoly : ∀ p : Polynomial ℝ, 0 ≤ ∫ x, (p.eval x) ^ 2 * J x ∂mu) :
    ∀ v : Lp ℝ 2 mu, 0 ≤ linftyMultiplierQuadratic J hJ v := by
  have hspan : ↑(realMonomialSpan mu hmu) ⊆
      {v : Lp ℝ 2 mu | 0 ≤ linftyMultiplierQuadratic J hJ v} := by
    intro v hv
    obtain ⟨p, hp⟩ := exists_polynomial_ae_eq_of_mem_realMonomialSpan hmu hv
    change 0 ≤ linftyMultiplierQuadratic J hJ v
    rw [linftyMultiplierQuadratic_eq_integral]
    have hcongr : (∫ x, (v x) ^ 2 * J x ∂mu) =
        ∫ x, (p.eval x) ^ 2 * J x ∂mu := by
      apply integral_congr_ae
      filter_upwards [hp] with x hx
      rw [hx]
    rw [hcongr]
    exact hpoly p
  have hclosed : IsClosed {v : Lp ℝ 2 mu | 0 ≤ linftyMultiplierQuadratic J hJ v} :=
    isClosed_le continuous_const (continuous_linftyMultiplierQuadratic J hJ)
  have hdense : Dense (↑(realMonomialSpan mu hmu) : Set (Lp ℝ 2 mu)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (realMonomialSpan_closure_eq_top mu hmu)
  intro v
  have hvcl : v ∈ closure (↑(realMonomialSpan mu hmu) : Set (Lp ℝ 2 mu)) := by
    rw [hdense.closure_eq]
    exact Set.mem_univ v
  exact closure_minimal hspan hclosed hvcl

/-- **Almost-everywhere polynomial sign-cone theorem.** Under an entire bilateral exponential
moment window, positivity against every polynomial square is equivalent to nonnegativity of the
bounded multiplier almost everywhere. -/
theorem polynomialSquareIntegral_nonnegative_iff_ae
    [IsFiniteMeasure mu] (hmu : HasEntireExponentialMoments mu)
    (J : ℝ → ℝ) (hJ : MemLp J ∞ mu) :
    (∀ p : Polynomial ℝ, 0 ≤ ∫ x, (p.eval x) ^ 2 * J x ∂mu) ↔
      0 ≤ᵐ[mu] J := by
  constructor
  · intro hpoly
    have hall := linftyMultiplierQuadratic_nonnegative_of_polynomial hmu J hJ hpoly
    have hJint : Integrable J mu := memLp_one_iff_integrable.mp
      (hJ.mono_exponent (by simp))
    apply ae_nonneg_of_forall_setIntegral_nonneg hJint
    intro s hs hsmu
    let v : Lp ℝ 2 mu := indicatorConstLp 2 hs hsmu.ne (1 : ℝ)
    have hv := hall v
    rw [linftyMultiplierQuadratic_eq_integral] at hv
    have hind : (fun x ↦ (v x) ^ 2 * J x) =ᵐ[mu] s.indicator J := by
      filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := mu)
        (s := s) (hs := hs) (hμs := hsmu.ne) (c := (1 : ℝ))] with x hx
      by_cases hxs : x ∈ s
      · rw [hx, Set.indicator_of_mem hxs]
        simp [hxs]
      · rw [hx, Set.indicator_of_notMem hxs]
        simp [hxs]
    rw [integral_congr_ae hind] at hv
    simpa only [integral_indicator hs] using hv
  · intro hJnonneg p
    exact integral_nonneg_of_ae
      (hJnonneg.mono fun x hx ↦ mul_nonneg (sq_nonneg _) hx)

/-- A continuous function which is nonnegative almost everywhere for an open-positive measure is
nonnegative at every point. -/
theorem continuous_nonnegative_of_ae [mu.IsOpenPosMeasure]
    {J : ℝ → ℝ} (hJ : Continuous J) (hae : 0 ≤ᵐ[mu] J) :
    ∀ x, 0 ≤ J x := by
  have hnull : mu {x | J x < 0} = 0 := by
    simpa only [not_le] using! (ae_iff.mp hae)
  intro x
  by_contra hx
  have hxneg : J x < 0 := lt_of_not_ge hx
  have hopen : IsOpen {y | J y < 0} := isOpen_lt hJ continuous_const
  have hne : ({y | J y < 0} : Set ℝ).Nonempty := ⟨x, hxneg⟩
  exact (hopen.measure_ne_zero mu hne) hnull

/-- **Pointwise exponential-moment polynomial sign-cone theorem.** For a finite measure positive
on open sets and with an entire bilateral exponential-moment window, a continuous bounded
multiplier is pointwise nonnegative exactly when all of its polynomial-square moments are
nonnegative. -/
theorem polynomialSquareIntegral_nonnegative_iff
    [IsFiniteMeasure mu] [mu.IsOpenPosMeasure]
    (hmu : HasEntireExponentialMoments mu)
    (J : ℝ → ℝ) (hJcont : Continuous J) (hJ : MemLp J ∞ mu) :
    (∀ p : Polynomial ℝ, 0 ≤ ∫ x, (p.eval x) ^ 2 * J x ∂mu) ↔
      ∀ x, 0 ≤ J x := by
  rw [polynomialSquareIntegral_nonnegative_iff_ae hmu J hJ]
  constructor
  · exact continuous_nonnegative_of_ae hJcont
  · exact fun h ↦ Filter.Eventually.of_forall h

end RHTower
