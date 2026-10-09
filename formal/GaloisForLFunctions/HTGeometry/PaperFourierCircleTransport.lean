import GaloisForLFunctions.HTGeometry.PaperFourierLLogLAdmission
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Exact circle-period transport for the Fourier endpoint

Rescaling a positive circle period preserves normalized Haar measure and every Fourier
coefficient. Thus the paper's fixed `2π` normalization accepts the actual L² boundary spaces
at period one or any positive source length, with their logarithmic integrability paid.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory Filter Topology FourierLLogL
open scoped ENNReal

variable (T S : ℝ) [hT : Fact (0 < T)] [hS : Fact (0 < S)]

/-- The actual rescaling of the additive circles. -/
def paperCircleRescale : AddCircle T ≃ₜ AddCircle S :=
  AddCircle.homeomorphAddCircle T S hT.out.ne' hS.out.ne'

/-- Period rescaling preserves the normalized Haar probabilities exactly. -/
theorem paperCircleRescale_measurePreserving :
    MeasurePreserving (paperCircleRescale T S)
      (AddCircle.haarAddCircle (T := T)) (AddCircle.haarAddCircle (T := S)) := by
  exact AddMonoidHom.measurePreserving
    (f := (AddCircle.equivAddCircle T S hT.out.ne' hS.out.ne').toAddMonoidHom)
    (paperCircleRescale T S).continuous
    (AddCircle.equivAddCircle T S hT.out.ne' hS.out.ne').surjective (by simp)

/-- Fourier characters retain their integer label under the period change. -/
theorem fourier_paperCircleRescale (k : ℤ) (x : AddCircle T) :
    fourier k (paperCircleRescale T S x) = fourier k x := by
  induction x using QuotientAddGroup.induction_on
  rename_i x
  change fourier k ((x * (T⁻¹ * S) : ℝ) : AddCircle S) = fourier k (x : AddCircle T)
  rw [fourier_coe_apply, fourier_coe_apply]
  congr 1
  push_cast
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.out.ne'
  have hSc : (S : ℂ) ≠ 0 := by exact_mod_cast hS.out.ne'
  field_simp

/-- Fourier coefficients are exactly invariant, including their normalization. -/
theorem fourierCoeff_paperCircleRescale (f : AddCircle S → ℂ) (k : ℤ) :
    fourierCoeff (fun x => f (paperCircleRescale T S x)) k = fourierCoeff f k := by
  have h := (paperCircleRescale_measurePreserving T S).integral_comp
    (paperCircleRescale T S).measurableEmbedding (fun y => fourier (-k) y • f y)
  simpa only [fourierCoeff, fourier_paperCircleRescale] using h

/-- The full finite Fourier sum commutes with period rescaling, at every point and cutoff. -/
theorem fourierPartialSum_paperCircleRescale (f : AddCircle S → ℂ) (N : ℕ)
    (x : AddCircle T) :
    (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      fourierCoeff (fun y => f (paperCircleRescale T S y)) k * fourier k x) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        fourierCoeff f k * fourier k (paperCircleRescale T S x) := by
  simp only [fourierCoeff_paperCircleRescale, fourier_paperCircleRescale]

/-- Logarithmic mass is unchanged by the same rescaling. -/
theorem orliczIntegral_paperCircleRescale (f : AddCircle S → ℂ) :
    (∫ x, ‖f (paperCircleRescale T S x)‖ *
      Real.log (2 + ‖f (paperCircleRescale T S x)‖) ∂AddCircle.haarAddCircle) =
      ∫ y, ‖f y‖ * Real.log (2 + ‖f y‖) ∂AddCircle.haarAddCircle :=
  (paperCircleRescale_measurePreserving T S).integral_comp
    (paperCircleRescale T S).measurableEmbedding
    (fun y : AddCircle S => ‖f y‖ * Real.log (2 + ‖f y‖))

/-- Pull back the actual L² boundary class, not a separately supplied representative. -/
def paperCirclePullbackLp (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := S))) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := T)) :=
  Lp.compMeasurePreserving (paperCircleRescale T S)
    (paperCircleRescale_measurePreserving T S) f

theorem paperCirclePullbackLp_ae (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := S))) :
    paperCirclePullbackLp T S f =ᵐ[AddCircle.haarAddCircle (T := T)]
      fun x => f (paperCircleRescale T S x) :=
  Lp.coeFn_compMeasurePreserving f (paperCircleRescale_measurePreserving T S)

theorem norm_paperCirclePullbackLp (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := S))) :
    ‖paperCirclePullbackLp T S f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (paperCircleRescale_measurePreserving T S)

variable {S}

/-- Native L² inputs at every positive period enter the paper's `2π` domain unconditionally. -/
theorem paperCircle_rescaled_memLLogL (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) :
    MemLLogL (fun x : Torus => f (paperCircleRescale (2 * Real.pi) T x)) :=
  (paperMemLLogL_Lp (paperCirclePullbackLp (2 * Real.pi) T f)).congr_ae
    (paperCirclePullbackLp_ae (2 * Real.pi) T f)

/-- The logarithmic height-layer budget is paid for native boundary inputs at any period. -/
theorem paperCircle_rescaled_heightLayerCost_summable
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) :
    Summable (fun j =>
      heightLayerMass (fun x => f (paperCircleRescale (2 * Real.pi) T x)) j *
        ((2 : ℝ) ^ (j + 2) + max 0 (-Real.log
          (heightLayerMass (fun x => f (paperCircleRescale (2 * Real.pi) T x)) j)))) :=
  (paperCircle_rescaled_memLLogL T f).summable_heightLayerCost

end

end GaloisForLFunctions.HTGeometry
