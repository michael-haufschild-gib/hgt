import GaloisForLFunctions.HTGeometry.ProjectiveBoundary
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier

/-!
# Multiplication operators on `L²(ℝ)` by continuous functions on the projective line

A continuous complex function `F` on the one-point compactification `ℝ ∪ {∞}` is bounded, so
multiplication by its restriction to `ℝ` is a bounded operator on `L²(ℝ)` with operator norm at
most `‖F‖_∞`. The assignment `F ↦ M_F` is unital, additive and `ℂ`-homogeneous, hence a continuous
linear map of norm at most `1` from the projective boundary algebra into the bounded operators.

## Main results

- `projectiveBoundaryMul`: the multiplication operator `M_F` on `L²(ℝ)`.
- `coeFn_projectiveBoundaryMul`: `M_F f = F · f` almost everywhere.
- `projectiveBoundaryMul_one`, `projectiveBoundaryMul_add`, `projectiveBoundaryMul_smul`:
  `M_1 = id`, `M_{F+G} = M_F + M_G`, `M_{cF} = c M_F`.
- `norm_projectiveBoundaryMul_le`: `‖M_F‖ ≤ ‖F‖_∞`.
- `projectiveBoundaryMulCLM`: `F ↦ M_F` as a continuous linear map.

## Hypotheses

All results are unconditional.
-/

open Complex MeasureTheory Topology
open scoped OnePoint

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The Hilbert space `L²(ℝ)` of complex functions. -/
abbrev ProjectiveBoundaryL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- Multiplication on `L²(ℝ)` by a continuous function `F` on `ℝ ∪ {∞}` restricted to `ℝ`. -/
def projectiveBoundaryMul (F : ProjectiveBoundary) :
    ProjectiveBoundaryL2 →L[ℂ] ProjectiveBoundaryL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (F.continuous.measurable.comp measurable_onePoint_some)
    (norm_nonneg F)
    (fun x => (ContinuousMap.norm_le F (norm_nonneg F)).mp le_rfl (x : OnePoint ℝ))

/-- `M_F f` agrees almost everywhere with the pointwise product `F(x) f(x)`. -/
theorem coeFn_projectiveBoundaryMul (F : ProjectiveBoundary)
    (f : ProjectiveBoundaryL2) :
    ((projectiveBoundaryMul F f : ProjectiveBoundaryL2) : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => F (x : OnePoint ℝ) * (f : ℝ → ℂ) x := by
  unfold projectiveBoundaryMul
  exact lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    (F.continuous.measurable.comp measurable_onePoint_some)
    (norm_nonneg F)
    (fun x => (ContinuousMap.norm_le F (norm_nonneg F)).mp le_rfl (x : OnePoint ℝ)) f

/-- Multiplication by the constant `1` is the identity. -/
theorem projectiveBoundaryMul_one :
    projectiveBoundaryMul (1 : ProjectiveBoundary) =
      ContinuousLinearMap.id ℂ ProjectiveBoundaryL2 := by
  apply ContinuousLinearMap.ext
  intro f
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_projectiveBoundaryMul (1 : ProjectiveBoundary) f] with x hx
  rw [hx]
  simp

/-- `M_{F+G} = M_F + M_G`. -/
theorem projectiveBoundaryMul_add (F G : ProjectiveBoundary) :
    projectiveBoundaryMul (F + G) = projectiveBoundaryMul F + projectiveBoundaryMul G := by
  apply ContinuousLinearMap.ext
  intro f
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_projectiveBoundaryMul (F + G) f,
    coeFn_projectiveBoundaryMul F f, coeFn_projectiveBoundaryMul G f,
    MeasureTheory.Lp.coeFn_add (projectiveBoundaryMul F f)
      (projectiveBoundaryMul G f)] with x hFG hF hG hadd
  rw [hFG]
  change (F + G) (x : OnePoint ℝ) * (f : ℝ → ℂ) x =
    (((projectiveBoundaryMul F f + projectiveBoundaryMul G f : ProjectiveBoundaryL2) :
      ℝ → ℂ) x)
  rw [hadd, Pi.add_apply, hF, hG, ContinuousMap.add_apply]
  ring

/-- `M_{cF} = c M_F`. -/
theorem projectiveBoundaryMul_smul (c : ℂ) (F : ProjectiveBoundary) :
    projectiveBoundaryMul (c • F) = c • projectiveBoundaryMul F := by
  apply ContinuousLinearMap.ext
  intro f
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_projectiveBoundaryMul (c • F) f,
    coeFn_projectiveBoundaryMul F f,
    MeasureTheory.Lp.coeFn_smul c (projectiveBoundaryMul F f)] with x hcf hF hsmul
  rw [hcf]
  change (c • F) (x : OnePoint ℝ) * (f : ℝ → ℂ) x =
    (((c • projectiveBoundaryMul F f : ProjectiveBoundaryL2) : ℝ → ℂ) x)
  rw [hsmul, Pi.smul_apply, smul_eq_mul, ContinuousMap.smul_apply, hF]
  ring

/-- Operator norm bound `‖M_F‖ ≤ ‖F‖_∞`. -/
theorem norm_projectiveBoundaryMul_le (F : ProjectiveBoundary) :
    ‖projectiveBoundaryMul F‖ ≤ ‖F‖ := by
  unfold projectiveBoundaryMul
  exact norm_lpBoundedMulCLM_le (p := 2) (μ := (volume : Measure ℝ))
    (F.continuous.measurable.comp measurable_onePoint_some)
    (norm_nonneg F)
    (fun x => (ContinuousMap.norm_le F (norm_nonneg F)).mp le_rfl (x : OnePoint ℝ))

/-- `F ↦ M_F` as a continuous `ℂ`-linear map into bounded operators on `L²(ℝ)`, of norm at most `1`. -/
def projectiveBoundaryMulCLM :
    ProjectiveBoundary →L[ℂ]
      (ProjectiveBoundaryL2 →L[ℂ] ProjectiveBoundaryL2) :=
  LinearMap.mkContinuous
    { toFun := projectiveBoundaryMul
      map_add' := projectiveBoundaryMul_add
      map_smul' := projectiveBoundaryMul_smul }
    1 (fun F => by simpa using norm_projectiveBoundaryMul_le F)

@[simp]
theorem projectiveBoundaryMulCLM_apply (F : ProjectiveBoundary) :
    projectiveBoundaryMulCLM F = projectiveBoundaryMul F := rfl

end GaloisForLFunctions.HTGeometry
