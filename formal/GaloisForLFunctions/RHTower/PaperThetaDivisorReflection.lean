import GaloisForLFunctions.RHTower.PaperThetaRelativeTail

/-! # Literal divisor reflection and normalized endpoint traces

Reflection is paid by the vanishing connection coefficient. It identifies the
two actual source ends and gives their common quotient trace without imposing
critical-line location.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry

theorem normalized_reflection (x : ℝ) : thetaSource.normalized (-x) = thetaSource.normalized x := by
  simp only [PositiveDensitySource.normalized, thetaSource_even]

theorem flatCharDensity_reflection (z : ℂ) (x : ℝ) :
    flatCharDensity (-z) (-x) = flatCharDensity z x := by
  rw [flatCharDensity, flatCharDensity, normalized_reflection, sourceChar, sourceChar]
  congr 2
  push_cast
  ring

theorem flatPrimitiveMode_divisor_reflection (z : {z : ℂ // XiC z = 0}) (x : ℝ) :
    flatPrimitiveMode z.val x = -flatPrimitiveMode (-z.val) (-x) := by
  have hC : flatConnection z.val = 0 := by
    rw [flatConnection_eq_all, z.property, zero_div]
  have hI : ∫ y in Iic x, flatCharDensity z.val y =
      ∫ y in Ioi (-x), flatCharDensity (-z.val) y := by
    rw [← integral_comp_neg_Iic x (flatCharDensity (-z.val))]
    apply integral_congr_ae
    filter_upwards [] with y
    exact (flatCharDensity_reflection z.val y).symm
  have he : Complex.exp (-(Complex.I * (-z.val)) * ((-x : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I * z.val) * (x : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [flatPrimitiveMode_eq_all, hC, zero_mul, zero_sub, hI, flatPrimitiveMode, he]

theorem flatMode_divisor_reflection (z : {z : ℂ // XiC z = 0}) (x : ℝ) :
    flatMode z.val x = flatMode (-z.val) (-x) := by
  rw [flatMode, flatMode, flatPrimitiveMode_divisor_reflection z, normalized_reflection]
  ring

theorem flatQuotient_divisor_reflection (z : {z : ℂ // XiC z = 0}) (x : ℝ) :
    flatQuotient z.val x = flatQuotient (-z.val) (-x) := by
  rw [flatQuotient, flatQuotient, flatMode_divisor_reflection z, normalized_reflection]

/-- Every Xi divisor point has normalized left trace -1, without a location assumption. -/
theorem tendsto_divisor_flatQuotient_atBot (z : {z : ℂ // XiC z = 0}) :
    Tendsto (flatQuotient z.val) atBot (𝓝 (-1)) := by
  have h := (tendsto_flatQuotient_atTop (-z.val)).comp tendsto_neg_atBot_atTop
  exact h.congr fun x => (flatQuotient_divisor_reflection z x).symm

theorem flatQuotient_zero (x : ℝ) : flatQuotient 0 x = -1 := by
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.normalized_pos x).ne'
  rw [flatQuotient, flatMode_zero_parameter, neg_div, div_self hρ]

theorem flatModePullback_eq_flatQuotient (z : ℂ) (t : ℝ) :
    flatModePullback z t = flatQuotient z (thetaSource.quantileFun t) := rfl

theorem flatModePullback_zero (t : ℝ) : flatModePullback 0 t = -1 := by
  rw [flatModePullback_eq_flatQuotient, flatQuotient_zero]

/-- The actual quantile mode has right interior trace -1 for every parameter. -/
theorem tendsto_pullback_at_one (z : ℂ) :
    Tendsto (flatModePullback z) (𝓝[<] (1 : ℝ)) (𝓝 (-1)) := by
  have h := (tendsto_flatQuotient_atTop z).comp (tendsto_quantileFun_nhdsLT_one thetaSource)
  exact h.congr fun t => (flatModePullback_eq_flatQuotient z t).symm

/-- The divisor mode has matching interior traces at both quantile ends. -/
theorem tendsto_divisor_pullback_at_zero (z : {z : ℂ // XiC z = 0}) :
    Tendsto (flatModePullback z.val) (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
  have h := (tendsto_divisor_flatQuotient_atBot z).comp (tendsto_quantileFun_nhdsGT_zero thetaSource)
  exact h.congr fun t => (flatModePullback_eq_flatQuotient z.val t).symm

end RHTower.PaperThetaEndpoint
