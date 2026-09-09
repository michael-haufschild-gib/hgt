import GaloisForLFunctions.HTGeometry.FokasLenellsRegularFullWeight
import GaloisForLFunctions.RHTower.FokasLenellsTimeDifferentiability

/-!
# Exact second time symbols and their sharp integrability gate

The paper's reciprocal time phases differentiate twice to the same
negative quarter of the actual second-inverse-weight jump in both
channels. The full-line weight classification therefore determines
exactly when the upper pointwise second derivative belongs to L2.
-/

open MeasureTheory Complex Matrix Filter Topology
open scoped ENNReal NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The exact second pointwise time derivative of either actual direct-scattering channel. -/
def directSecondTimeSymbol (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) : ℂ :=
  (-1/4 : ℂ)*regularSecondInverseJump q t x reverse z

/-- The second derivative is exactly the original actual symbol divided by the squared spectral coordinate. -/
theorem directSecondTimeSymbol_eq (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    directSecondTimeSymbol q t x reverse z = (-1/4 : ℂ)*directSymbol q t x reverse z/(z : ℂ)^2 := by
  cases reverse <;>
    simp only [directSecondTimeSymbol, regularSecondInverseJump, regularInverseFrequencyJump,
      directSymbol, Bool.false_eq_true, ↓reduceIte, div_div, pow_two, mul_div_assoc]

/-- Differentiating the first time symbol gives the actual second derivative at every spectral point, including zero. -/
theorem directTimeSymbol_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    HasDerivAt (fun s => directTimeSymbol q s x reverse z) (directSecondTimeSymbol q t x reverse z) t := by
  have hh := ((directSymbol_time_hasDerivAt q t x reverse z).div_const (z : ℂ)).const_mul
    (if reverse then -I/2 else I/2)
  change HasDerivAt (fun s => (if reverse then -I/2 else I/2)*(directSymbol q s x reverse z/(z : ℂ)))
    (directSecondTimeSymbol q t x reverse z) t
  refine hh.congr_deriv ?_
  change (if reverse then -I/2 else I/2)*
    ((if reverse then -I/2 else I/2)*regularInverseFrequencyJump q t x reverse z/(z : ℂ)) =
      (-1/4 : ℂ)*(regularInverseFrequencyJump q t x reverse z/(z : ℂ))
  cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring_nf <;> simp <;> ring

/-- The exact second-derivative norm is independent of time and position. -/
theorem directSecondTimeSymbol_norm (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖directSecondTimeSymbol q t x reverse z‖ =
      (1/4 : ℝ)*‖regularSecondInverseReflection (globalSmallScatteringPotential q) reverse z‖ := by
  simp only [directSecondTimeSymbol, norm_mul, regularSecondInverseJump_norm]
  norm_num

theorem directSecondTimeSymbol_measurable (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    Measurable (directSecondTimeSymbol q t x reverse) :=
  (regularSecondInverseJump_measurable q t x reverse).const_mul (-1/4 : ℂ)

/-- The fixed nonzero quarter factor does not change any Lp membership or restricted-measure criterion. -/
theorem directSecondTimeSymbol_memLp_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool)
    (p : ℝ≥0∞) (μ : Measure ℝ) :
    MemLp (directSecondTimeSymbol q t x reverse) p μ ↔ MemLp (regularSecondInverseJump q t x reverse) p μ := by
  constructor
  · intro h
    have he : (fun z : ℝ => (-4 : ℂ)*directSecondTimeSymbol q t x reverse z) =
        regularSecondInverseJump q t x reverse := by
      funext z
      rw [directSecondTimeSymbol]
      ring
    rw [← he]
    exact h.const_mul (-4 : ℂ)
  · intro h
    exact h.const_mul (-1/4 : ℂ)

/-- The lower actual second time derivative is square integrable for every constructed small Schwartz profile. -/
theorem directSecondTimeSymbol_lower_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    MemLp (directSecondTimeSymbol q t x false) 2 volume :=
  (directSecondTimeSymbol_memLp_iff q t x false 2 volume).2 (regularSecondInverseJump_lower_memLp q t x)

/-- The upper actual second time derivative is square integrable exactly on the nonlinear compatibility locus. -/
theorem directSecondTimeSymbol_upper_memLp_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    MemLp (directSecondTimeSymbol q t x true) 2 volume ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  rw [directSecondTimeSymbol_memLp_iff, regularSecondInverseJump_upper_memLp_iff]

/-- Small Gaussian spatial profiles have a pointwise second time derivative that is not in L2 at any time or position. -/
theorem directSecondTimeSymbol_upper_Gaussian_not_memLp (a t x : ℝ) :
    ¬ MemLp (directSecondTimeSymbol (compatibilityGaussian a) t x true) 2 volume := by
  rw [directSecondTimeSymbol_upper_memLp_iff]
  exact compatibilityMoment_globalSmallGaussian_ne_zero a

/-- The compatible prescribed-fifth-trace family does satisfy the second-time L2 condition everywhere. -/
theorem directSecondTimeSymbol_upper_quinticGaussianProfile_memLp (a : ℝ) (c : ℂ) (t x : ℝ) :
    MemLp (directSecondTimeSymbol (quinticGaussianProfile a c) t x true) 2 volume :=
  (directSecondTimeSymbol_upper_memLp_iff _ t x).2 (compatibilityMoment_globalSmall_quinticGaussianProfile a c)

/-- The pointwise second derivative is jointly continuous in the physical parameters. -/
theorem continuous_directSecondTimeSymbol_parameters (q : SchwartzMap ℝ ℂ) (reverse : Bool) (z : ℝ) :
    Continuous (fun p : ℝ × ℝ => directSecondTimeSymbol q p.1 p.2 reverse z) := by
  simp only [directSecondTimeSymbol_eq]
  exact (continuous_const.mul (continuous_directSymbol_parameters q reverse z)).div_const ((z : ℂ)^2)

end
end RHTower.FokasLenells
