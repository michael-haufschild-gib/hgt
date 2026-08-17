import GaloisForLFunctions.HTGeometry.StieltjesMomentDetermination
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Moment convergence is weak convergence on the unit interval

A uniformly bounded family of finite sources on `[0,1]` whose moments converge integrates every
continuous function to the limit: polynomials are dense in the sup norm by Weierstrass, the
integral against each source is a bounded functional with a common bound, and a polynomial's
integral is the finite combination of moments.

This is the step that turns a countable trace hierarchy into weak convergence of the occupancy
measures, and it needs no tightness argument because the interval is already compact.
-/

open MeasureTheory Filter Topology Polynomial

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Every continuous function on the compactified ordinate is integrable against a finite
source. -/
theorem integrable_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (σ : Measure HausdorffSourceSpace) [IsFiniteMeasure σ] :
    Integrable (fun y : HausdorffSourceSpace => f (y : ℝ)) σ := by
  have hcont : Continuous fun y : HausdorffSourceSpace => f (y : ℝ) :=
    continuousOn_iff_continuous_restrict.mp hf
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The integral of a polynomial is the finite combination of the moments. -/
theorem integral_polynomial_eq_sum_moments (p : ℝ[X]) (σ : Measure HausdorffSourceSpace)
    [IsFiniteMeasure σ] :
    ∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂σ
      = ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * hausdorffMoment σ j := by
  have hpoint : ∀ y : HausdorffSourceSpace,
      p.eval (y : ℝ) = ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * (y : ℝ) ^ j := by
    intro y
    exact eval_eq_sum_range (y : ℝ)
  have hint : ∀ j ∈ Finset.range (p.natDegree + 1),
      Integrable (fun y : HausdorffSourceSpace => p.coeff j * (y : ℝ) ^ j) σ := by
    intro j _
    have hcont : Continuous fun y : HausdorffSourceSpace => p.coeff j * (y : ℝ) ^ j :=
      continuous_const.mul (continuous_subtype_val.pow j)
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂σ
      = ∫ y : HausdorffSourceSpace,
          ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * (y : ℝ) ^ j ∂σ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ j ∈ Finset.range (p.natDegree + 1),
          ∫ y : HausdorffSourceSpace, p.coeff j * (y : ℝ) ^ j ∂σ :=
        integral_finsetSum _ hint
    _ = ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * hausdorffMoment σ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul, hausdorffMoment]

/-- A uniform mass bound turns a sup-norm bound into an integral bound. -/
theorem abs_integral_sub_le_of_sup_le {f g : ℝ → ℝ} {δ M : ℝ} (hδ : 0 ≤ δ)
    (σ : Measure HausdorffSourceSpace) [IsFiniteMeasure σ]
    (hM : (σ Set.univ).toReal ≤ M)
    (hf : ContinuousOn f (Set.Icc 0 1)) (hg : ContinuousOn g (Set.Icc 0 1))
    (hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x - g x| ≤ δ) :
    |(∫ y : HausdorffSourceSpace, f (y : ℝ) ∂σ)
      - ∫ y : HausdorffSourceSpace, g (y : ℝ) ∂σ| ≤ δ * M := by
  have hfi := integrable_of_continuousOn hf σ
  have hgi := integrable_of_continuousOn hg σ
  have hsub : (∫ y : HausdorffSourceSpace, f (y : ℝ) ∂σ)
      - ∫ y : HausdorffSourceSpace, g (y : ℝ) ∂σ
      = ∫ y : HausdorffSourceSpace, (f (y : ℝ) - g (y : ℝ)) ∂σ :=
    (integral_sub hfi hgi).symm
  rw [hsub]
  have hbound : ∀ y : HausdorffSourceSpace, ‖f (y : ℝ) - g (y : ℝ)‖ ≤ δ := by
    intro y
    rw [Real.norm_eq_abs]
    exact hsup _ ⟨y.property.1, y.property.2⟩
  have h := norm_integral_le_of_norm_le_const (μ := σ)
    (f := fun y : HausdorffSourceSpace => f (y : ℝ) - g (y : ℝ)) (C := δ)
    (Filter.Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at h
  have hmass : (σ Set.univ).toReal ≤ M := hM
  have hmnn : (0 : ℝ) ≤ (σ Set.univ).toReal := ENNReal.toReal_nonneg
  calc |∫ y : HausdorffSourceSpace, (f (y : ℝ) - g (y : ℝ)) ∂σ|
      ≤ δ * (σ Set.univ).toReal := by simpa [measureReal_def] using h
    _ ≤ δ * M := mul_le_mul_of_nonneg_left hmass hδ

/-- **Moment convergence is weak convergence.**  A uniformly bounded family of finite sources on
the compactified ordinate whose moments converge integrates every continuous function to the
limit. -/
theorem tendsto_integral_of_tendsto_moments
    {σ : ℕ → Measure HausdorffSourceSpace} {τ : Measure HausdorffSourceSpace}
    [∀ n, IsFiniteMeasure (σ n)] [IsFiniteMeasure τ] {M : ℝ}
    (hM : ∀ n, (σ n Set.univ).toReal ≤ M) (hτM : (τ Set.univ).toReal ≤ M)
    (hmom : ∀ j : ℕ, Tendsto (fun n => hausdorffMoment (σ n) j) atTop
      (𝓝 (hausdorffMoment τ j)))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun n => ∫ y : HausdorffSourceSpace, f (y : ℝ) ∂(σ n)) atTop
      (𝓝 (∫ y : HausdorffSourceSpace, f (y : ℝ) ∂τ)) := by
  have hM0 : 0 ≤ M := le_trans ENNReal.toReal_nonneg hτM
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (4 * (M + 1)) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf δ hδ
  have hpcont : ContinuousOn (fun x => p.eval x) (Set.Icc 0 1) :=
    (p.continuous_aeval).continuousOn
  have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x - p.eval x| ≤ δ := by
    intro x hx
    have := hp x hx
    rw [abs_sub_comm] at this
    exact this.le
  -- the polynomial integrals converge
  have hpoly : Tendsto (fun n => ∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂(σ n)) atTop
      (𝓝 (∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂τ)) := by
    have hsum : Tendsto
        (fun n => ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * hausdorffMoment (σ n) j)
        atTop (𝓝 (∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * hausdorffMoment τ j)) := by
      refine tendsto_finsetSum _ fun j _ => ?_
      exact (hmom j).const_mul _
    rw [integral_polynomial_eq_sum_moments p τ]
    refine hsum.congr fun n => ?_
    exact (integral_polynomial_eq_sum_moments p (σ n)).symm
  rw [Metric.tendsto_atTop] at hpoly
  obtain ⟨N, hN⟩ := hpoly (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : |(∫ y : HausdorffSourceSpace, f (y : ℝ) ∂(σ n))
      - ∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂(σ n)| ≤ δ * M :=
    abs_integral_sub_le_of_sup_le hδ.le (σ n) (hM n) hf hpcont hsup
  have h2 : |(∫ y : HausdorffSourceSpace, f (y : ℝ) ∂τ)
      - ∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂τ| ≤ δ * M :=
    abs_integral_sub_le_of_sup_le hδ.le τ hτM hf hpcont hsup
  have h3 := hN n hn
  rw [Real.dist_eq] at h3 ⊢
  have hδM : δ * M ≤ ε / 4 := by
    rw [hδdef]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
    nlinarith [hM0, hε.le]
  calc |(∫ y : HausdorffSourceSpace, f (y : ℝ) ∂(σ n))
        - ∫ y : HausdorffSourceSpace, f (y : ℝ) ∂τ|
      ≤ |(∫ y : HausdorffSourceSpace, f (y : ℝ) ∂(σ n))
          - ∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂(σ n)|
        + |(∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂(σ n))
          - ∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂τ|
        + |(∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂τ)
          - ∫ y : HausdorffSourceSpace, f (y : ℝ) ∂τ| := by
        have := abs_sub_le (∫ y : HausdorffSourceSpace, f (y : ℝ) ∂(σ n))
          (∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂(σ n))
          (∫ y : HausdorffSourceSpace, f (y : ℝ) ∂τ)
        have h4 := abs_sub_le (∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂(σ n))
          (∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂τ)
          (∫ y : HausdorffSourceSpace, f (y : ℝ) ∂τ)
        linarith
    _ < ε := by
        have h2' : |(∫ y : HausdorffSourceSpace, p.eval (y : ℝ) ∂τ)
            - ∫ y : HausdorffSourceSpace, f (y : ℝ) ∂τ| ≤ δ * M := by
          rw [abs_sub_comm]
          exact h2
        linarith

end GaloisForLFunctions.HTGeometry
