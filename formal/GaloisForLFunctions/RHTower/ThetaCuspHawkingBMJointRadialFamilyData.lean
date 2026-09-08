import GaloisForLFunctions.HTGeometry.HilbertCompactJetApproximation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointAngularEnergyTests

/-! Smooth compact radial families in the actual completed modular energy domain. -/
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMJointWave
noncomputable section

abbrev AngularEnergy := D4BMModularCore.energyDomain
abbrev RadialAngularSpace := Lp AngularEnergy 2 radialMeasure

structure RadialEnergyFamily where
  field : ℝ → AngularEnergy
  smooth : ContDiff ℝ ∞ field
  compact : HasCompactSupport field
  support : tsupport field ⊆ Iio 0

theorem angularWeight_smooth : ContDiff ℝ ∞ angularWeight :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_cosh.inv (fun t => ne_of_gt (Real.cosh_pos t)))

theorem radialWeightedValue_ae (f : RadialCore) :
    (radialWeightedValue f : ℝ → ℂ) =ᵐ[radialMeasure]
      (fun t => angularWeight t*f.field t) :=
  ((angularWeight_smooth.continuous.mul f.smooth.continuous).memLp_of_hasCompactSupport
    (p := 2) (μ := radialMeasure) f.compact.mul_left).coeFn_toLp

def RadialEnergyFamily.value (h : RadialEnergyFamily) : RadialAngularSpace :=
  (h.smooth.continuous.memLp_of_hasCompactSupport h.compact).toLp h.field

def RadialEnergyFamily.radial (h : RadialEnergyFamily) : RadialAngularSpace :=
  ((h.smooth.continuous_deriv (by simp)).memLp_of_hasCompactSupport h.compact.deriv).toLp
    (deriv h.field)

def RadialEnergyFamily.weightedField (h : RadialEnergyFamily) (t : ℝ) : AngularEnergy :=
  angularWeight t • h.field t

theorem RadialEnergyFamily.weightedField_smooth (h : RadialEnergyFamily) :
    ContDiff ℝ ∞ h.weightedField := angularWeight_smooth.smul h.smooth

theorem RadialEnergyFamily.weightedField_compact (h : RadialEnergyFamily) :
    HasCompactSupport h.weightedField := by
  apply h.compact.mono
  intro t ht hz
  apply ht
  change angularWeight t • h.field t = 0
  rw [hz,smul_zero]

def RadialEnergyFamily.weighted (h : RadialEnergyFamily) : RadialAngularSpace :=
  (h.weightedField_smooth.continuous.memLp_of_hasCompactSupport h.weightedField_compact).toLp
    h.weightedField

theorem RadialEnergyFamily.value_ae (h : RadialEnergyFamily) :
    (h.value : ℝ → AngularEnergy) =ᵐ[radialMeasure] h.field :=
  (h.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := radialMeasure) h.compact).coeFn_toLp

theorem RadialEnergyFamily.radial_ae (h : RadialEnergyFamily) :
    (h.radial : ℝ → AngularEnergy) =ᵐ[radialMeasure] deriv h.field :=
  ((h.smooth.continuous_deriv (by simp)).memLp_of_hasCompactSupport
    (p := 2) (μ := radialMeasure) h.compact.deriv).coeFn_toLp

theorem RadialEnergyFamily.weighted_ae (h : RadialEnergyFamily) :
    (h.weighted : ℝ → AngularEnergy) =ᵐ[radialMeasure] h.weightedField :=
  (h.weightedField_smooth.continuous.memLp_of_hasCompactSupport
    (p := 2) (μ := radialMeasure) h.weightedField_compact).coeFn_toLp

/-- Every Hilbert coefficient is an actual smooth radial test, with unchanged physical support. -/
def RadialEnergyFamily.coefficient {ι : Type*} (h : RadialEnergyFamily)
    (b : HilbertBasis ι ℂ AngularEnergy) (i : ι) : RadialCore where
  field := hilbertRadialCoefficient b h.field i
  smooth := hilbertRadialCoefficient_smooth b h.field h.smooth i
  compact := hilbertRadialCoefficient_compact b h.field h.compact i
  support := (hilbertRadialCoefficient_support b h.field i).trans h.support

theorem RadialEnergyFamily.coefficient_value {ι : Type*} (h : RadialEnergyFamily)
    (b : HilbertBasis ι ℂ AngularEnergy) (i : ι) :
    (innerSL ℂ (b i)).compLp h.value = radialValue (h.coefficient b i) := by
  apply Lp.ext
  filter_upwards [(innerSL ℂ (b i)).coeFn_compLp h.value,h.value_ae,
    radialValue_ae (h.coefficient b i)] with t h0 h1 h2
  rw [h0,h1,h2]
  rfl

theorem RadialEnergyFamily.coefficient_radial {ι : Type*} (h : RadialEnergyFamily)
    (b : HilbertBasis ι ℂ AngularEnergy) (i : ι) :
    (innerSL ℂ (b i)).compLp h.radial = radialDerivative (h.coefficient b i) := by
  apply Lp.ext
  filter_upwards [(innerSL ℂ (b i)).coeFn_compLp h.radial,h.radial_ae,
    radialDerivative_ae (h.coefficient b i)] with t h0 h1 h2
  rw [h0,h1,h2]
  exact (hilbertRadialCoefficient_deriv b h.field (h.smooth.differentiable (by simp)) i t).symm

theorem RadialEnergyFamily.coefficient_weighted {ι : Type*} (h : RadialEnergyFamily)
    (b : HilbertBasis ι ℂ AngularEnergy) (i : ι) :
    (innerSL ℂ (b i)).compLp h.weighted = radialWeightedValue (h.coefficient b i) := by
  apply Lp.ext
  filter_upwards [(innerSL ℂ (b i)).coeFn_compLp h.weighted,h.weighted_ae,
    radialWeightedValue_ae (h.coefficient b i)] with t h0 h1 h2
  rw [h0,h1,h2]
  change inner ℂ (b i) (angularWeight t • h.field t) =
    angularWeight t*inner ℂ (b i) (h.field t)
  exact _root_.inner_smul_right (𝕜 := ℂ) (b i) (h.field t) (angularWeight t)

end
end RHTower.D4BMJointWave
