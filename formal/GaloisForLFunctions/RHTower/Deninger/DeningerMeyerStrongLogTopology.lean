import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogTarget
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Natural weighted-derivative topology on Meyer's strong logarithmic target

The underlying strong target requires every derivative to be bounded after
every real exponential weight.  Its natural locally convex topology is the
initial topology of the uniform weighted-derivative gauges

`g ↦ (t ↦ exp(t)^k g⁽ⁿ⁾(t))`,  `n : ℕ`, `k : ℤ`.

Integral weights are cofinal among real weights at both logarithmic ends, so
this countable family is the usual strong Schwartz family rather than a
pointwise or discrete substitute.  This file constructs the gauges as honest
bounded continuous functions and proves that their initial topology is a
complex topological-vector-space topology.
-/

noncomputable section

open Asymptotics Complex Filter Function Set Topology Bornology
open scoped BoundedContinuousFunction ContDiff

namespace RHTower

/-- Weighted `n`th derivative of one strong logarithmic profile, represented
in the uniform normed space of bounded continuous functions. -/
def deningerMeyerStrongLogGauge (n : ℕ) (k : ℤ)
    (g : DeningerMeyerStrongLogTarget) : ℝ →ᵇ ℂ where
  toFun := fun t => ((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) *
    iteratedDeriv n (g : ℝ → ℂ) t
  continuous_toFun := by
    have hweight : Continuous (fun t : ℝ => Real.exp t ^ (k : ℝ)) :=
      Real.continuous_exp.rpow_const
        (fun t => Or.inl (Real.exp_ne_zero t))
    have hderiv : Continuous (iteratedDeriv n (g : ℝ → ℂ)) :=
      g.property.smooth.continuous_iteratedDeriv n (by
        show ((n : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr (ENat.coe_lt_top n).le)
    exact (Complex.continuous_ofReal.comp hweight).mul hderiv
  map_bounded' := Metric.isBounded_range_iff.mp
    (g.property.weighted_iteratedDeriv_isBounded n (k : ℝ))

@[simp]
theorem deningerMeyerStrongLogGauge_apply
    (n : ℕ) (k : ℤ) (g : DeningerMeyerStrongLogTarget) (t : ℝ) :
    deningerMeyerStrongLogGauge n k g t =
      ((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) *
        iteratedDeriv n (g : ℝ → ℂ) t :=
  rfl

/-- Each weighted-derivative gauge is complex-linear. -/
def deningerMeyerStrongLogGaugeLinear (n : ℕ) (k : ℤ) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] (ℝ →ᵇ ℂ) where
  toFun := deningerMeyerStrongLogGauge n k
  map_add' g h := by
    apply BoundedContinuousFunction.ext
    intro t
    change
      ((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) *
          iteratedDeriv n ((g + h : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t =
        ((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) *
            iteratedDeriv n (g : ℝ → ℂ) t +
          ((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) *
            iteratedDeriv n (h : ℝ → ℂ) t
    have hadd :
        ((g + h : DeningerMeyerStrongLogTarget) : ℝ → ℂ) =
          (g : ℝ → ℂ) + (h : ℝ → ℂ) :=
      rfl
    rw [hadd]
    rw [iteratedDeriv_add
      (g.property.smooth.contDiffAt.of_le (mod_cast le_top))
      (h.property.smooth.contDiffAt.of_le (mod_cast le_top))]
    ring
  map_smul' z g := by
    apply BoundedContinuousFunction.ext
    intro t
    change
      ((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) *
          iteratedDeriv n ((z • g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t =
        z * (((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) *
          iteratedDeriv n (g : ℝ → ℂ) t)
    have hsmul :
        ((z • g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) =
          z • (g : ℝ → ℂ) :=
      rfl
    rw [hsmul]
    rw [iteratedDeriv_const_smul_field]
    ring

@[simp]
theorem deningerMeyerStrongLogGaugeLinear_apply
    (n : ℕ) (k : ℤ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogGaugeLinear n k g =
      deningerMeyerStrongLogGauge n k g :=
  rfl

/-- Countable initial topology of all integral weighted-derivative uniform
gauges.  This is the natural strong logarithmic Schwartz topology. -/
@[reducible]
def deningerMeyerStrongLogTopology :
    TopologicalSpace DeningerMeyerStrongLogTarget :=
  ⨅ i : ℕ × ℤ, TopologicalSpace.induced
    (deningerMeyerStrongLogGaugeLinear i.1 i.2)
    inferInstance

/-- Addition is continuous for the strong logarithmic topology. -/
theorem deningerMeyerStrongLogTopology_continuousAdd :
    @ContinuousAdd DeningerMeyerStrongLogTarget
      deningerMeyerStrongLogTopology inferInstance := by
  unfold deningerMeyerStrongLogTopology
  exact continuousAdd_iInf fun (i : ℕ × ℤ) =>
    continuousAdd_induced (deningerMeyerStrongLogGaugeLinear i.1 i.2)

/-- Complex scalar multiplication is continuous for the strong logarithmic
topology. -/
theorem deningerMeyerStrongLogTopology_continuousSMul :
    @ContinuousSMul ℂ DeningerMeyerStrongLogTarget
      inferInstance inferInstance deningerMeyerStrongLogTopology := by
  unfold deningerMeyerStrongLogTopology
  exact continuousSMul_iInf fun (i : ℕ × ℤ) =>
    continuousSMul_induced (deningerMeyerStrongLogGaugeLinear i.1 i.2)

/-- Every defining weighted-derivative gauge is continuous. -/
theorem continuous_deningerMeyerStrongLogGaugeLinear (n : ℕ) (k : ℤ) :
    @Continuous DeningerMeyerStrongLogTarget (ℝ →ᵇ ℂ)
      deningerMeyerStrongLogTopology inferInstance
      (deningerMeyerStrongLogGaugeLinear n k) := by
  unfold deningerMeyerStrongLogTopology
  exact continuous_iInf_dom (i := (n, k)) continuous_induced_dom

/-- Zeroth unweighted gauge remembers the original function pointwise. -/
theorem deningerMeyerStrongLogGaugeLinear_zero_zero_injective :
    Function.Injective (deningerMeyerStrongLogGaugeLinear 0 0) := by
  intro g h hgh
  apply Subtype.ext
  funext t
  have ht : deningerMeyerStrongLogGauge 0 0 g t =
      deningerMeyerStrongLogGauge 0 0 h t :=
    congrArg (fun F : ℝ →ᵇ ℂ => F t) hgh
  simpa only [deningerMeyerStrongLogGauge_apply, Int.cast_zero,
    Real.rpow_zero, Complex.ofReal_one, one_mul, iteratedDeriv_zero] using ht

end RHTower
