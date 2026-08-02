import GaloisForLFunctions.RHTower.BurnolCoPoissonIndicatorSeed
import GaloisForLFunctions.RHTower.ArchimedeanMellinFourier

/-!
# The correction constant of a co-Poisson sum

The constant subtracted in the co-Poisson sum is the half-line mass of the reciprocal seed,
`integral_0^infinity g(1/y) dy / y`.  Inverting the ray turns it into the logarithmic mass
`integral_0^infinity g(y) dy / y` of the seed itself, so the constant is symmetric under passing to
the reciprocal seed, and the correction constant of the reciprocal seed is the plain half-line mass
`integral_0^infinity g`.

These are the two constants that cancel in the co-Poisson intertwining: the logarithmic mass cancels
the correction of the seed and the plain mass cancels the correction of the reciprocal seed.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The correction constant of the co-Poisson sum of `g`: the half-line mass of the reciprocal
seed. -/
def coPoissonCorrectionConstant (g : ℝ → ℂ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), ((y : ℝ) : ℂ)⁻¹ * g y⁻¹

theorem burnolCoPoissonRightSum_eq_sub_correction (g : ℝ → ℂ) (t : ℝ) :
    burnolCoPoissonRightSum g t =
      (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ))) -
        coPoissonCorrectionConstant g :=
  rfl

/-- **The correction constant is the logarithmic mass of the seed.**  Inverting the positive ray
exchanges the seed with its reciprocal seed and leaves the logarithmic measure invariant. -/
theorem coPoissonCorrectionConstant_eq_logMass (g : ℝ → ℂ) :
    coPoissonCorrectionConstant g = ∫ y in Ioi (0 : ℝ), ((y : ℝ) : ℂ)⁻¹ * g y := by
  rw [coPoissonCorrectionConstant, integral_Ioi_comp_inv (fun u : ℝ => ((u : ℝ) : ℂ)⁻¹ * g u)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hvpos : (0 : ℝ) < v := mem_Ioi.mp hv
  have hvne : ((v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hvpos)
  rw [Complex.ofReal_inv, inv_inv, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
  rw [← mul_assoc, sq]
  congr 1
  field_simp

/-- **The correction constant of the reciprocal seed is the plain half-line mass of the seed.** -/
theorem coPoissonCorrectionConstant_reciprocalSeed (g : ℝ → ℂ) :
    coPoissonCorrectionConstant (coPoissonReciprocalSeed g) = ∫ y in Ioi (0 : ℝ), g y := by
  rw [coPoissonCorrectionConstant]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hypos : (0 : ℝ) < y := mem_Ioi.mp hy
  have hyne : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hypos)
  rw [coPoissonReciprocalSeed, inv_inv, Complex.ofReal_inv, inv_inv, ← mul_assoc,
    inv_mul_cancel₀ hyne, one_mul]

end RHTower
