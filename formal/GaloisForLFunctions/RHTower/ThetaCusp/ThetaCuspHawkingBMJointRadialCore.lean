import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMModularEnergyDomain
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Smooth interior tortoise tests, their actual derivatives and the geometric angular weight. -/
open MeasureTheory Set Filter Topology
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMJointWave
noncomputable section

abbrev radialMeasure : Measure ℝ := volume.restrict (Iio 0)
abbrev RadialSpace := Lp ℂ 2 radialMeasure

structure RadialCore where
  field : ℝ → ℂ
  smooth : ContDiff ℝ ∞ field
  compact : HasCompactSupport field
  support : tsupport field ⊆ Iio 0

def radialValue (f : RadialCore) : RadialSpace :=
  (f.smooth.continuous.memLp_of_hasCompactSupport f.compact).toLp f.field

def radialDerivative (f : RadialCore) : RadialSpace :=
  ((f.smooth.continuous_deriv (by simp)).memLp_of_hasCompactSupport f.compact.deriv).toLp
    (deriv f.field)

/-- The coefficient multiplying the hyperbolic angular gradient in tortoise coordinates. -/
def angularWeight (t : ℝ) : ℂ := ((Real.cosh t)⁻¹ : ℝ)

private theorem angularWeight_continuous : Continuous angularWeight := by
  exact Complex.continuous_ofReal.comp (Real.continuous_cosh.inv₀ (fun t => ne_of_gt (Real.cosh_pos t)))

private theorem weighted_compact (f : RadialCore) :
    HasCompactSupport (fun t => angularWeight t * f.field t) :=
  f.compact.mul_left

def radialWeightedValue (f : RadialCore) : RadialSpace :=
  ((angularWeight_continuous.mul f.smooth.continuous).memLp_of_hasCompactSupport
    (weighted_compact f)).toLp (fun t => angularWeight t * f.field t)

/-- Smooth tests compactly supported in the physical tortoise interval separate its L² vectors. -/
theorem radialValue_total (u : RadialSpace)
    (hu : ∀ f : RadialCore, inner ℂ (radialValue f) u = 0) : u = 0 := by
  have ht : ∀ (g : ℝ → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Iio 0 →
      ∫ t, g t • u t ∂radialMeasure = 0 := by
    intro g hg hk hs
    let G : ℝ → ℂ := fun t => (g t : ℂ)
    have hG : ContDiff ℝ ∞ G := Complex.ofRealCLM.contDiff.comp hg
    have hsupport : Function.support G ⊆ Function.support g := by
      intro t ht
      simpa only [G, Function.mem_support, Complex.ofReal_ne_zero] using ht
    let f : RadialCore := ⟨G,hG,hk.mono hsupport,(closure_mono hsupport).trans hs⟩
    have he := hu f
    rw [L2.inner_def] at he
    convert he using 1
    apply integral_congr_ae
    filter_upwards [(f.smooth.continuous.memLp_of_hasCompactSupport (p := 2)
      (μ := radialMeasure) f.compact).coeFn_toLp] with t ht
    change (radialValue f) t = f.field t at ht
    rw [ht]
    simp [f,G,Complex.real_smul,mul_comm]
  have hz := isOpen_Iio.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((Lp.memLp u).locallyIntegrable (by norm_num) |>.locallyIntegrableOn (Iio 0)) ht
  apply Lp.ext
  filter_upwards [hz, ae_restrict_mem measurableSet_Iio, Lp.coeFn_zero ℂ 2 radialMeasure]
    with t ht hi h0
  rw [h0]
  exact ht hi

theorem radialWeightedValue_symmetric (f g : RadialCore) :
    inner ℂ (radialValue f) (radialWeightedValue g) =
      inner ℂ (radialWeightedValue f) (radialValue g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    (f.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := radialMeasure) f.compact).coeFn_toLp,
    (g.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := radialMeasure) g.compact).coeFn_toLp,
    ((angularWeight_continuous.mul f.smooth.continuous).memLp_of_hasCompactSupport
      (p := 2) (μ := radialMeasure) (weighted_compact f)).coeFn_toLp,
    ((angularWeight_continuous.mul g.smooth.continuous).memLp_of_hasCompactSupport
      (p := 2) (μ := radialMeasure) (weighted_compact g)).coeFn_toLp] with t hf hg hwf hwg
  change (radialValue f) t = f.field t at hf
  change (radialValue g) t = g.field t at hg
  change (radialWeightedValue f) t = angularWeight t * f.field t at hwf
  change (radialWeightedValue g) t = angularWeight t * g.field t at hwg
  rw [hf,hg,hwf,hwg]
  change (angularWeight t * g.field t) * conj (f.field t) =
    g.field t * conj (angularWeight t * f.field t)
  rw [map_mul]
  have hw : conj (angularWeight t) = angularWeight t := Complex.conj_ofReal _
  rw [hw]
  ring

end
end RHTower.D4BMJointWave
