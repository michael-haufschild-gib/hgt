import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatConvexPotential
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Weak lower semicontinuity of the flat integral energy

The flat potential defines a finite convex energy on every real L² space.
Its tangent error is bounded by half the squared L² displacement. Explicit
supporting affine functionals give weakly closed sublevels, hence weak
lower semicontinuity. This is the convex scalar mechanism behind the
lower-semicontinuity criterion of arXiv:2611.02792, applied to the flat
potential of arXiv:2611.08616.
-/

open MeasureTheory Set
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The flat pointwise gradient, as an actual element of L². -/
def gradientLp (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  gradient_contraction.compLp gradient_zero f

/-- The flat integral energy, finite on arbitrary measure spaces. -/
def integralEnergy (f : Lp ℝ 2 μ) : ℝ := ∫ x, potential (f x) ∂μ

theorem integrable_potential (f : Lp ℝ 2 μ) : Integrable (fun x => potential (f x)) μ := by
  refine ((Lp.memLp f).integrable_sq.div_const 2).mono'
    ((potential_contDiff 0).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f)) ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (potential_bounds (f x)).1]
    exact (potential_bounds (f x)).2

private theorem integral_sq_eq_norm (f : Lp ℝ 2 μ) :
    (∫ x, f x ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by change f x ^ 2 = f x * f x; ring

private theorem integrated_tangent (f g : Lp ℝ 2 μ) :
    Integrable (fun x => gradient (g x) * (f x - g x)) μ ∧
      (∫ x, gradient (g x) * (f x - g x) ∂μ) = inner ℝ (gradientLp g) (f - g) := by
  have he : (fun x => inner ℝ ((gradientLp g) x) ((f - g) x)) =ᵐ[μ]
      (fun x => gradient (g x) * (f x - g x)) := by
    filter_upwards [gradient_contraction.coeFn_compLp gradient_zero g, Lp.coeFn_sub f g]
      with x hx hd
    change inner ℝ ((gradient_contraction.compLp gradient_zero g) x) ((f - g) x) = _
    rw [hx, hd]
    change (f x - g x) * gradient (g x) = gradient (g x) * (f x - g x)
    ring
  exact ⟨(L2.integrable_inner (gradientLp g) (f - g)).congr he,
    (integral_congr_ae he).symm.trans (L2.inner_def _ _).symm⟩

/-- A quadratic Taylor bound with no regularity assumptions on the L² profiles. -/
theorem integral_tangent_error_bounds (f g : Lp ℝ 2 μ) :
    0 ≤ integralEnergy f - integralEnergy g - inner ℝ (gradientLp g) (f - g) ∧
      integralEnergy f - integralEnergy g - inner ℝ (gradientLp g) (f - g) ≤
        ‖f - g‖ ^ 2 / 2 := by
  have hi : Integrable (fun x => potential (f x) - potential (g x)) μ :=
    (integrable_potential f).sub (integrable_potential g)
  have ht := integrated_tangent f g
  have hr : Integrable (fun x => potential (f x) - potential (g x) -
      gradient (g x) * (f x - g x)) μ := hi.sub ht.1
  have he : (∫ x, potential (f x) - potential (g x) -
      gradient (g x) * (f x - g x) ∂μ) =
      integralEnergy f - integralEnergy g - inner ℝ (gradientLp g) (f - g) := by
    rw [integral_sub hi ht.1, integral_sub (integrable_potential f) (integrable_potential g), ht.2]
    rfl
  have hs : Integrable (fun x => (f x - g x) ^ 2 / 2) μ := by
    apply ((Lp.memLp (f - g)).integrable_sq.div_const 2).congr
    filter_upwards [Lp.coeFn_sub f g] with x hx
    exact congrArg (fun t : ℝ => t ^ 2 / 2) hx
  have hsn : (∫ x, (f x - g x) ^ 2 / 2 ∂μ) = ‖f - g‖ ^ 2 / 2 := by
    rw [integral_div]
    congr 1
    calc
      (∫ x, (f x - g x) ^ 2 ∂μ) = ∫ x, (f - g) x ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub f g] with x hx
        exact (congrArg (fun t : ℝ => t ^ 2) hx).symm
      _ = _ := integral_sq_eq_norm _
  constructor
  · rw [← he]
    exact integral_nonneg fun x => (tangent_error_bounds (f x) (g x)).1
  · rw [← he, ← hsn]
    exact integral_mono hr hs fun x => (tangent_error_bounds (f x) (g x)).2

/-- Every profile supplies an exact global affine support. -/
theorem integral_support (f g : Lp ℝ 2 μ) :
    integralEnergy g + inner ℝ (gradientLp g) (f - g) ≤ integralEnergy f := by
  linarith only [(integral_tangent_error_bounds f g).1]

/-- Arbitrary measure spaces require no extra integrability or finite-volume premise. -/
theorem integral_energy_bounds (f : Lp ℝ 2 μ) :
    0 ≤ integralEnergy f ∧ integralEnergy f ≤ ‖f‖ ^ 2 / 2 := by
  constructor
  · exact integral_nonneg fun x => (potential_bounds (f x)).1
  · rw [← integral_sq_eq_norm, ← integral_div]
    exact integral_mono (integrable_potential f) ((Lp.memLp f).integrable_sq.div_const 2)
      fun x => (potential_bounds (f x)).2

/-- Convexity follows directly from the global supports, with no bounded-profile restriction. -/
theorem integral_energy_convex : ConvexOn ℝ univ (integralEnergy : Lp ℝ 2 μ → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro f _ g _ a b ha hb hab
  let z := a • f + b • g
  have hf := mul_le_mul_of_nonneg_left (integral_support f z) ha
  have hg := mul_le_mul_of_nonneg_left (integral_support g z) hb
  have hv : a • (f - z) + b • (g - z) = 0 := by
    rw [smul_sub, smul_sub, ← add_sub_add_comm, ← add_smul, hab, one_smul]
    exact sub_self z
  have hi : a * inner ℝ (gradientLp z) (f - z) +
      b * inner ℝ (gradientLp z) (g - z) = 0 := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hv,
      inner_zero_right]
  have he : a * integralEnergy z + b * integralEnergy z = integralEnergy z := by
    rw [← add_mul, hab, one_mul]
  change integralEnergy z ≤ a * integralEnergy f + b * integralEnergy g
  nlinarith only [hf, hg, hi, he]

/-- The nonlinear L² gradient is itself a contraction. -/
theorem gradientLp_contraction : LipschitzWith 1 (gradientLp : Lp ℝ 2 μ → Lp ℝ 2 μ) :=
  gradient_contraction.lipschitzWith_compLp gradient_zero

/-- Each supporting functional is continuous for the weak L² topology. -/
private def weakGradientFunctional (g : Lp ℝ 2 μ) : StrongDual ℝ (WeakSpace ℝ (Lp ℝ 2 μ)) :=
  { toLinearMap := (innerSL ℝ (gradientLp g) : Lp ℝ 2 μ →ₗ[ℝ] ℝ).comp
      ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm : WeakSpace ℝ (Lp ℝ 2 μ) →ₗ[ℝ] Lp ℝ 2 μ)
    cont := WeakBilin.eval_continuous (topDualPairing ℝ (Lp ℝ 2 μ)).flip
      (innerSL ℝ (gradientLp g)) }

/-- Weak sublevels are intersections of explicit continuous affine half-spaces. -/
theorem isClosed_weak_integral_sublevel (r : ℝ) :
    IsClosed {w : WeakSpace ℝ (Lp ℝ 2 μ) |
      integralEnergy ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm w) ≤ r} := by
  have he : {w : WeakSpace ℝ (Lp ℝ 2 μ) |
      integralEnergy ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm w) ≤ r} =
      ⋂ g : Lp ℝ 2 μ, {w | integralEnergy g + weakGradientFunctional g w -
        inner ℝ (gradientLp g) g ≤ r} := by
    ext w
    simp only [mem_setOf_eq, mem_iInter]
    constructor
    · intro h g
      have hs := integral_support ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm w) g
      rw [inner_sub_right] at hs
      change integralEnergy g + inner ℝ (gradientLp g)
        ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm w) - inner ℝ (gradientLp g) g ≤ r
      linarith only [hs, h]
    · intro h
      have hs := h ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm w)
      change integralEnergy ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm w) +
        inner ℝ (gradientLp ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm w))
          ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm w) -
        inner ℝ (gradientLp ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm w))
          ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm w) ≤ r at hs
      linarith only [hs]
  rw [he]
  apply isClosed_iInter
  intro g
  exact isClosed_le ((continuous_const.add (weakGradientFunctional g).continuous).sub
    continuous_const) continuous_const

/-- The flat integral energy cannot jump upwards at a weak limit. -/
theorem integral_energy_weak_lowerSemicontinuous :
    LowerSemicontinuous (fun w : WeakSpace ℝ (Lp ℝ 2 μ) =>
      integralEnergy ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm w)) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  exact isClosed_weak_integral_sublevel

#print axioms integral_tangent_error_bounds
#print axioms integral_energy_convex
#print axioms gradientLp_contraction
#print axioms integral_energy_weak_lowerSemicontinuous
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
