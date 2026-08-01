import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Moment determinacy on a compact interval

A finite measure carried by a compact interval is determined by its moments.  Equal moments give
equal integrals of every polynomial; Weierstrass approximation makes the polynomial functions dense
in the continuous functions on the interval; the integral is a Lipschitz functional there, so the
two integrals agree on all continuous functions and the measures coincide.

Nothing about the origin of the measure enters, so this applies verbatim to a pushforward.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- A continuous function on a compact space is integrable against a finite measure. -/
theorem integrable_of_continuous (ρ : Measure X) [IsFiniteMeasure ρ] {f : X → ℝ}
    (hf : Continuous f) : Integrable f ρ :=
  BoundedContinuousFunction.integrable ρ (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩)

/-- Integration against a finite measure is a Lipschitz, hence continuous, functional on the
continuous functions of a compact space. -/
theorem continuous_integral_continuousMap (ρ : Measure X) [IsFiniteMeasure ρ] :
    Continuous (fun g : C(X, ℝ) => ∫ x, g x ∂ρ) := by
  have hnn : 0 ≤ ρ.real Set.univ := measureReal_nonneg
  refine (LipschitzWith.of_dist_le_mul (K := (ρ.real Set.univ).toNNReal) ?_).continuous
  intro g₁ g₂
  have hi1 : Integrable (fun x => g₁ x) ρ := integrable_of_continuous ρ g₁.continuous
  have hi2 : Integrable (fun x => g₂ x) ρ := integrable_of_continuous ρ g₂.continuous
  have hbound : ‖∫ x, (g₁ x - g₂ x) ∂ρ‖ ≤ dist g₁ g₂ * ρ.real Set.univ := by
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs, Real.dist_eq] using
      ContinuousMap.dist_apply_le_dist (f := g₁) (g := g₂) x
  rw [Real.dist_eq, ← integral_sub hi1 hi2]
  calc ‖∫ x, (g₁ x - g₂ x) ∂ρ‖ ≤ dist g₁ g₂ * ρ.real Set.univ := hbound
    _ = ((ρ.real Set.univ).toNNReal : ℝ) * dist g₁ g₂ := by
        rw [Real.coe_toNNReal _ hnn]
        ring

/-- **Moment determinacy on a compact interval.**  Two finite measures on `Icc a b` with the same
moments are equal. -/
theorem ext_of_forall_integral_pow_eq {a b : ℝ} {μ ν : Measure (Set.Icc a b)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ℕ, (∫ x, ((x : ℝ)) ^ n ∂μ) = ∫ x, ((x : ℝ)) ^ n ∂ν) :
    μ = ν := by
  have hpoly : ∀ p : Polynomial ℝ,
      (∫ x : Set.Icc a b, p.eval (x : ℝ) ∂μ) = ∫ x : Set.Icc a b, p.eval (x : ℝ) ∂ν := by
    intro p
    have hexp : ∀ (ρ : Measure (Set.Icc a b)), ∀ _ : IsFiniteMeasure ρ,
        (∫ x : Set.Icc a b, p.eval (x : ℝ) ∂ρ)
          = ∑ i ∈ Finset.range (p.natDegree + 1),
              p.coeff i * ∫ x : Set.Icc a b, ((x : ℝ)) ^ i ∂ρ := by
      intro ρ _
      have hcongr : (∫ x : Set.Icc a b, p.eval (x : ℝ) ∂ρ)
          = ∫ x : Set.Icc a b,
              (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ((x : ℝ)) ^ i) ∂ρ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact Polynomial.eval_eq_sum_range (p := p) ((x : ℝ))
      rw [hcongr, integral_finsetSum]
      · exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      · intro i _
        refine (integrable_of_continuous ρ ?_).const_mul _
        fun_prop
    rw [hexp μ inferInstance, hexp ν inferInstance]
    exact Finset.sum_congr rfl fun i _ => by rw [h i]
  have hdense : Dense ((polynomialFunctions (Set.Icc a b) : Subalgebra ℝ _) :
      Set C(Set.Icc a b, ℝ)) := by
    have := polynomialFunctions_closure_eq_top a b
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, this]
    rfl
  have key : (fun g : C(Set.Icc a b, ℝ) => ∫ x, g x ∂μ)
      = fun g : C(Set.Icc a b, ℝ) => ∫ x, g x ∂ν := by
    refine Continuous.ext_on hdense (continuous_integral_continuousMap μ)
      (continuous_integral_continuousMap ν) ?_
    rintro g ⟨p, -, rfl⟩
    exact hpoly p
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  exact congrFun key f.toContinuousMap

end

end GaloisForLFunctions.HTGeometry
