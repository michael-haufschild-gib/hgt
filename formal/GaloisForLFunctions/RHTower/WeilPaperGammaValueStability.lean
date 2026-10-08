import GaloisForLFunctions.RHTower.WeilPaperGammaVariational
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Stable variational values for completed Weil spectral families

The minimum perturbed gamma energy is 1-Lipschitz in the bounded spectral
penalty, monotone, equivariant under constant shifts, and concave. Each attained
minimizer supplies an exact supporting affine bound and a quantitative bound
for transferring an optimizer between two penalties.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP

variable {ι : Type*}

/-- An attained minimizer in the actual observed native completion. -/
def paperObservedGammaMinimizer (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (G : ℝ →ᵇ ℝ) : PaperObservedSpectralCompletion c F :=
  Classical.choose (exists_paperObservedPerturbedGamma_minimizer c F G)

/-- The finite attained value, with feasibility and integrability already paid. -/
def paperObservedGammaValue (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (G : ℝ →ᵇ ℝ) : ℝ :=
  paperPerturbedGammaExpectation G (paperObservedGammaMinimizer c F G).1

/-- The chosen value is below the objective at every feasible completed law. -/
theorem paperObservedGammaValue_le (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (G : ℝ →ᵇ ℝ) (μ : PaperObservedSpectralCompletion c F) :
    paperObservedGammaValue c F G ≤ paperPerturbedGammaExpectation G μ.1 :=
  Classical.choose_spec (exists_paperObservedPerturbedGamma_minimizer c F G) μ

/-- The variational value is the integral of the actual perturbed gamma symbol. -/
theorem paperObservedGammaValue_eq_integral
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ) :
    paperObservedGammaValue c F G =
      ∫ ξ, paperSpectralGammaWeight ξ + G ξ
        ∂((paperObservedGammaMinimizer c F G).1 : Measure ℝ) :=
  paperPerturbedGammaExpectation_eq_integral _
    ⟨_, paperObservedSpectralCompletion_subset_budget c F
      (paperObservedGammaMinimizer c F G).2⟩ G

/-- Objective differences are exactly bounded-observable expectations. -/
theorem paperPerturbedGammaExpectation_sub (μ : ProbabilityMeasure ℝ) (G H : ℝ →ᵇ ℝ) :
    paperPerturbedGammaExpectation G μ - paperPerturbedGammaExpectation H μ =
      ∫ ξ, (G - H) ξ ∂(μ : Measure ℝ) := by
  change _ = ∫ ξ, G ξ - H ξ ∂(μ : Measure ℝ)
  rw [integral_sub (G.integrable _) (H.integrable _)]
  unfold paperPerturbedGammaExpectation
  ring

/-- Every attained minimizer supplies a supporting affine bound for all other penalties. -/
theorem paperObservedGammaValue_supergradient
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ) :
    paperObservedGammaValue c F H ≤ paperObservedGammaValue c F G +
      ∫ ξ, (H - G) ξ ∂((paperObservedGammaMinimizer c F G).1 : Measure ℝ) := by
  have hm := paperObservedGammaValue_le c F H (paperObservedGammaMinimizer c F G)
  have hd := paperPerturbedGammaExpectation_sub (paperObservedGammaMinimizer c F G).1 H G
  change paperObservedGammaValue c F H ≤
    paperPerturbedGammaExpectation G (paperObservedGammaMinimizer c F G).1 + _
  linarith

private theorem integral_penalty_sub_le (μ : ProbabilityMeasure ℝ) (G H : ℝ →ᵇ ℝ) :
    (∫ ξ, (G - H) ξ ∂(μ : Measure ℝ)) ≤ ‖G - H‖ :=
  (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using (G - H).norm_integral_le_norm (μ : Measure ℝ))

/-- A bounded perturbation changes the optimal value by at most its uniform norm. -/
theorem paperObservedGammaValue_le_add_norm
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ) :
    paperObservedGammaValue c F G ≤ paperObservedGammaValue c F H + ‖G - H‖ := by
  have h := paperObservedGammaValue_supergradient c F H G
  have hi := integral_penalty_sub_le (paperObservedGammaMinimizer c F H).1 G H
  linarith

/-- The attained value has a two-sided uniform perturbation bound. -/
theorem abs_paperObservedGammaValue_sub_le
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ) :
    |paperObservedGammaValue c F G - paperObservedGammaValue c F H| ≤ ‖G - H‖ := by
  apply abs_le.mpr
  constructor
  · have h := paperObservedGammaValue_le_add_norm c F H G
    rw [norm_sub_rev] at h
    linarith
  · have h := paperObservedGammaValue_le_add_norm c F G H
    linarith

/-- The gamma variational value is 1-Lipschitz on the space of bounded continuous penalties. -/
theorem lipschitzWith_paperObservedGammaValue
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    LipschitzWith 1 (paperObservedGammaValue c F) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro G H
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    abs_paperObservedGammaValue_sub_le c F G H

theorem continuous_paperObservedGammaValue
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    Continuous (paperObservedGammaValue c F) :=
  (lipschitzWith_paperObservedGammaValue c F).continuous

/-- Raising a spectral penalty pointwise raises the optimal value. -/
theorem monotone_paperObservedGammaValue
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    Monotone (paperObservedGammaValue c F) := by
  intro G H hGH
  calc
    _ ≤ paperPerturbedGammaExpectation G (paperObservedGammaMinimizer c F H).1 :=
      paperObservedGammaValue_le c F G _
    _ ≤ paperPerturbedGammaExpectation H (paperObservedGammaMinimizer c F H).1 := by
      have hi := integral_mono
        (G.integrable ((paperObservedGammaMinimizer c F H).1 : Measure ℝ))
        (H.integrable ((paperObservedGammaMinimizer c F H).1 : Measure ℝ)) (fun ξ => hGH ξ)
      dsimp only [paperPerturbedGammaExpectation]
      linarith
    _ = _ := rfl

/-- Constant spectral penalties shift every probability-law objective by the same constant. -/
theorem paperPerturbedGammaExpectation_add_const
    (μ : ProbabilityMeasure ℝ) (G : ℝ →ᵇ ℝ) (a : ℝ) :
    paperPerturbedGammaExpectation (G + BoundedContinuousFunction.const ℝ a) μ =
      paperPerturbedGammaExpectation G μ + a := by
  unfold paperPerturbedGammaExpectation
  change (∫ ξ, paperSpectralGammaWeight ξ ∂(μ : Measure ℝ)) +
    (∫ ξ, G ξ + a ∂(μ : Measure ℝ)) = _
  rw [integral_add (G.integrable _) (integrable_const a), integral_const, probReal_univ, one_smul]
  ring

/-- The variational perturbation bound is attained for constant shifts. -/
theorem paperObservedGammaValue_add_const
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ) (a : ℝ) :
    paperObservedGammaValue c F (G + BoundedContinuousFunction.const ℝ a) =
      paperObservedGammaValue c F G + a := by
  apply le_antisymm
  · calc
      _ ≤ paperPerturbedGammaExpectation (G + BoundedContinuousFunction.const ℝ a)
          (paperObservedGammaMinimizer c F G).1 := paperObservedGammaValue_le c F _ _
      _ = _ := paperPerturbedGammaExpectation_add_const _ G a
  · have h := paperObservedGammaValue_le c F G
      (paperObservedGammaMinimizer c F (G + BoundedContinuousFunction.const ℝ a))
    have he : paperObservedGammaValue c F (G + BoundedContinuousFunction.const ℝ a) =
        paperPerturbedGammaExpectation G
          (paperObservedGammaMinimizer c F (G + BoundedContinuousFunction.const ℝ a)).1 + a :=
      paperPerturbedGammaExpectation_add_const _ G a
    linarith

/-- At a fixed law, the perturbed objective is affine in the bounded spectral penalty. -/
theorem paperPerturbedGammaExpectation_segment
    (μ : ProbabilityMeasure ℝ) (G H : ℝ →ᵇ ℝ) (t : Icc (0 : ℝ) 1) :
    paperPerturbedGammaExpectation (t.1 • G + (1 - t.1) • H) μ =
      t.1 * paperPerturbedGammaExpectation G μ +
        (1 - t.1) * paperPerturbedGammaExpectation H μ := by
  unfold paperPerturbedGammaExpectation
  change (∫ ξ, paperSpectralGammaWeight ξ ∂(μ : Measure ℝ)) +
    (∫ ξ, t.1 * G ξ + (1 - t.1) * H ξ ∂(μ : Measure ℝ)) = _
  rw [integral_add ((G.integrable _).const_mul _) ((H.integrable _).const_mul _),
    integral_const_mul, integral_const_mul]
  ring

/-- The minimum gamma value is concave in the spectral penalty. -/
theorem paperObservedGammaValue_concave
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ) (t : Icc (0 : ℝ) 1) :
    t.1 * paperObservedGammaValue c F G + (1 - t.1) * paperObservedGammaValue c F H ≤
      paperObservedGammaValue c F (t.1 • G + (1 - t.1) • H) := by
  let μ := paperObservedGammaMinimizer c F (t.1 • G + (1 - t.1) • H)
  calc
    _ ≤ t.1 * paperPerturbedGammaExpectation G μ.1 +
        (1 - t.1) * paperPerturbedGammaExpectation H μ.1 :=
      add_le_add (mul_le_mul_of_nonneg_left (paperObservedGammaValue_le c F G μ) t.2.1)
        (mul_le_mul_of_nonneg_left (paperObservedGammaValue_le c F H μ)
          (sub_nonneg.mpr t.2.2))
    _ = paperPerturbedGammaExpectation (t.1 • G + (1 - t.1) • H) μ.1 :=
      (paperPerturbedGammaExpectation_segment μ.1 G H t).symm
    _ = _ := rfl

/-- An optimizer for one penalty is a controlled approximate optimizer for every other penalty. -/
theorem paperObservedGammaMinimizer_transfer_bound
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ) :
    0 ≤ paperPerturbedGammaExpectation G (paperObservedGammaMinimizer c F H).1 -
        paperObservedGammaValue c F G ∧
      paperPerturbedGammaExpectation G (paperObservedGammaMinimizer c F H).1 -
        paperObservedGammaValue c F G ≤ 2 * ‖G - H‖ := by
  have hm := paperObservedGammaValue_le c F G (paperObservedGammaMinimizer c F H)
  have hd := paperPerturbedGammaExpectation_sub (paperObservedGammaMinimizer c F H).1 G H
  have hi := integral_penalty_sub_le (paperObservedGammaMinimizer c F H).1 G H
  have hv := paperObservedGammaValue_le_add_norm c F H G
  rw [norm_sub_rev] at hv
  have he : paperObservedGammaValue c F H =
      paperPerturbedGammaExpectation H (paperObservedGammaMinimizer c F H).1 := rfl
  constructor <;> linarith

end RHTower.WeilWorkPBAP
