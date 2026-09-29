import GaloisForLFunctions.HTGeometry.ExponentialWallStrictContraction
import GaloisForLFunctions.HTGeometry.SquareIntegrableKernelTransport

/-!
# The exponential wall operator in the quantile chart

The exponential quantile `Q₀(u) = -log(1 - u)` pushes the uniform law on `(0, 1)` to the unit
exponential law `μ`, and the distribution function `F(x) = 1 - e^{-x}` pushes `μ` back, with
`F ∘ Q₀ = id` on `(0, 1)` and `Q₀ ∘ F = id` on `(0, ∞)`.  Hence `U f = f ∘ Q₀` is a unitary
`L²(μ) → L²(0, 1)` with inverse `g ↦ g ∘ F`, and it conjugates the wall operator `A` to the
integral operator `A₀ = U A U⁻¹` on `L²(0, 1)` with kernel `κ(Q₀ u, Q₀ v)` — the comoving landing
kernel of the quantile-pulled wall.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance isProbabilityMeasure_expMeasure_one_quantile : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- **Inverse transform sampling** for the unit exponential law. -/
theorem measurePreserving_quantile_expMeasure_one :
    MeasurePreserving (quantile (expMeasure 1)) (volume.restrict (Ioo (0 : ℝ) 1)) (expMeasure 1) :=
  ⟨measurable_quantile _, map_quantile_eq _⟩

theorem cdf_quantile_expMeasure_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    cdf (expMeasure 1) (quantile (expMeasure 1) u) = u := by
  rw [quantile_expMeasure_one hu.1 hu.2, cdf_expMeasure_eq one_pos]
  have h1 : 0 < 1 - u := by linarith [hu.2]
  have hx0 : (0 : ℝ) ≤ -Real.log (1 - u) := by
    have := Real.log_nonpos h1.le (by linarith [hu.1])
    linarith
  rw [if_pos hx0, show -(1 * -Real.log (1 - u)) = Real.log (1 - u) by ring, Real.exp_log h1]
  ring

theorem quantile_cdf_expMeasure_one {x : ℝ} (hx : 0 < x) :
    quantile (expMeasure 1) (cdf (expMeasure 1) x) = x := by
  have hc : cdf (expMeasure 1) x = 1 - Real.exp (-x) := by
    rw [cdf_expMeasure_eq one_pos, if_pos hx.le, one_mul]
  have he : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he0 : 0 < Real.exp (-x) := Real.exp_pos _
  rw [hc, quantile_expMeasure_one (by linarith) (by linarith),
    show 1 - (1 - Real.exp (-x)) = Real.exp (-x) by ring, Real.log_exp, neg_neg]

/-- The distribution function pushes the unit exponential law to the uniform law on `(0, 1)`. -/
theorem measurePreserving_cdf_expMeasure_one :
    MeasurePreserving (fun x => cdf (expMeasure 1) x) (expMeasure 1)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hF : Measurable fun x => cdf (expMeasure 1) x := (cdf (expMeasure 1)).mono.measurable
  refine ⟨hF, ?_⟩
  calc Measure.map (fun x => cdf (expMeasure 1) x) (expMeasure 1)
      = Measure.map (fun x => cdf (expMeasure 1) x)
          (Measure.map (quantile (expMeasure 1)) (volume.restrict (Ioo (0 : ℝ) 1))) :=
        congrArg _ measurePreserving_quantile_expMeasure_one.map_eq.symm
    _ = Measure.map ((fun x => cdf (expMeasure 1) x) ∘ quantile (expMeasure 1))
          (volume.restrict (Ioo (0 : ℝ) 1)) := Measure.map_map hF (measurable_quantile _)
    _ = Measure.map id (volume.restrict (Ioo (0 : ℝ) 1)) := by
        refine Measure.map_congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact cdf_quantile_expMeasure_one hu
    _ = volume.restrict (Ioo (0 : ℝ) 1) := Measure.map_id

/-- The comoving wall kernel `κ(Q₀ u, Q₀ v)` on `L²(0, 1)`. -/
def quantileWallKernel :
    SqIntKernel (volume.restrict (Ioo (0 : ℝ) 1)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
  wallKernel.pullback measurePreserving_quantile_expMeasure_one

/-- The comoving wall landing `A₀`. -/
def quantileWallOperator :
    Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) →L[ℂ] Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
  quantileWallKernel.op

theorem quantileWallKernel_toFun {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    quantileWallKernel.toFun u v
      = ((wallCubicKernel (-Real.log (1 - u)) (-Real.log (1 - v)) : ℝ) : ℂ) := by
  rw [quantileWallKernel, SqIntKernel.pullback_toFun, quantile_expMeasure_one hu.1 hu.2,
    quantile_expMeasure_one hv.1 hv.2]
  rfl

/-- The comoving kernel is the quantile-pulled wall kernel of the prime Stokes landing. -/
theorem quantileWallKernel_toFun_eq {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    quantileWallKernel.toFun u v
      = ((RHTower.routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) (u, v) : ℝ) :
          ℂ) := by
  rw [RHTower.routePPrimitiveGammaJuliaStokesWallQuantileKernel, if_pos ⟨hu, hv⟩]
  rfl

/-- `U = (f ↦ f ∘ Q₀)` is unitary with inverse `g ↦ g ∘ F`. -/
theorem compL2_quantile_cdf_inverse :
    compL2 measurePreserving_cdf_expMeasure_one ∘L compL2 measurePreserving_quantile_expMeasure_one
        = ContinuousLinearMap.id ℂ (Lp ℂ 2 (expMeasure 1)) ∧
      compL2 measurePreserving_quantile_expMeasure_one ∘L
          compL2 measurePreserving_cdf_expMeasure_one
        = ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1))) := by
  constructor
  · refine compL2_comp_compL2 _ _ ?_
    filter_upwards [ae_pos_expMeasure_one] with x hx
    exact quantile_cdf_expMeasure_one hx
  · refine compL2_comp_compL2 _ _ ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact cdf_quantile_expMeasure_one hu

/-- **Quantile transport.**  `A₀ = U A U⁻¹`. -/
theorem quantileWallOperator_eq :
    quantileWallOperator = compL2 measurePreserving_quantile_expMeasure_one ∘L wallOperator ∘L
      compL2 measurePreserving_cdf_expMeasure_one := by
  refine wallKernel.pullback_op_eq _ _ ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact cdf_quantile_expMeasure_one hu

end GaloisForLFunctions.HTGeometry
