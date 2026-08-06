import GaloisForLFunctions.HTGeometry.GaussianRadialLaw
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Gaussian polar disintegration

A standard Gaussian vector in `m` dimensions has radius distributed with the
chi density

`ρ_m(r) = 2^{1 - m/2} / Γ(m/2) · r^{m-1} · exp(-r²/2)`,

and every function of the radius integrates against the Gaussian exactly as it
integrates against `ρ_m` on the positive half-line.  The normalising constant is
identified from the volume of the Euclidean unit ball and the functional equation
of `Γ`.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal NNReal Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The radial density of a standard Gaussian vector in `m` dimensions. -/
def gaussianRadialDensity (m : ℕ) (r : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 - (m : ℝ) / 2) / Real.Gamma ((m : ℝ) / 2) * r ^ (m - 1)
    * Real.exp (-r ^ 2 / 2)

/-- **Polar normalisation constant.**  The Euclidean unit-ball volume times the
Gaussian normalisation is the chi normalisation. -/
theorem gaussian_polar_constant (m : ℕ) (hm : 0 < m) :
    (m : ℝ) * (volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal
        * (Real.sqrt (2 * Real.pi))⁻¹ ^ m
      = (2 : ℝ) ^ (1 - (m : ℝ) / 2) / Real.Gamma ((m : ℝ) / 2) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hmpos : (0 : ℝ) < (m : ℝ) / 2 := by positivity
  have hGpos : 0 < Real.Gamma ((m : ℝ) / 2) := Real.Gamma_pos_of_pos hmpos
  have hGpos' : 0 < Real.Gamma ((m : ℝ) / 2 + 1) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  have hvol : (volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal
      = Real.sqrt Real.pi ^ m / Real.Gamma ((m : ℝ) / 2 + 1) := by
    rw [EuclideanSpace.volume_ball, hcard]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hpi : Real.sqrt Real.pi ^ m = Real.pi ^ ((m : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (Real.pi ^ (1 / 2 : ℝ)) m,
      ← Real.rpow_mul (le_of_lt Real.pi_pos)]
    ring_nf
  have htwopi : Real.sqrt (2 * Real.pi) ^ m
      = (2 : ℝ) ^ ((m : ℝ) / 2) * Real.pi ^ ((m : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((2 * Real.pi) ^ (1 / 2 : ℝ)) m,
      ← Real.rpow_mul (by positivity),
      Real.mul_rpow (by norm_num) (le_of_lt Real.pi_pos)]
    ring_nf
  have hGrec : Real.Gamma ((m : ℝ) / 2 + 1) = ((m : ℝ) / 2) * Real.Gamma ((m : ℝ) / 2) :=
    Real.Gamma_add_one (ne_of_gt hmpos)
  have hpipow : (0 : ℝ) < Real.pi ^ ((m : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have htwopow : (0 : ℝ) < (2 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_pos_of_pos two_pos _
  have hsplit : (2 : ℝ) ^ (1 - (m : ℝ) / 2)
      = 2 * ((2 : ℝ) ^ ((m : ℝ) / 2))⁻¹ := by
    rw [Real.rpow_sub two_pos, Real.rpow_one]
    ring
  rw [hvol, hpi, inv_pow, htwopi, hGrec, hsplit]
  field_simp

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Gaussian polar disintegration.**  Every function of the radius integrates
against the standard Gaussian exactly as it integrates against the chi density on
the positive half-line. -/
theorem integral_stdGaussian_fun_norm {m : ℕ} (hm : 0 < m) (f : ℝ → F) :
    ∫ x, f ‖x‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))
      = ∫ y in Ioi (0 : ℝ), gaussianRadialDensity m y • f y := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin m)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hm)
  have hmeas : Measurable
      (fun x : EuclideanSpace ℝ (Fin m) =>
        ENNReal.ofReal (euclideanGaussianDensityReal x)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    unfold euclideanGaussianDensityReal
    fun_prop
  rw [stdGaussian_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) _]
  have hpt : ∀ x : EuclideanSpace ℝ (Fin m),
      (ENNReal.ofReal (euclideanGaussianDensityReal x)).toReal • f ‖x‖
        = ((Real.sqrt (2 * Real.pi))⁻¹ ^ m * Real.exp (-‖x‖ ^ 2 / 2)) • f ‖x‖ := by
    intro x
    rw [ENNReal.toReal_ofReal (euclideanGaussianDensityReal_nonneg x)]
    simp only [euclideanGaussianDensityReal, Fintype.card_fin]
  rw [funext hpt]
  rw [integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin m)))
    (fun y => ((Real.sqrt (2 * Real.pi))⁻¹ ^ m * Real.exp (-y ^ 2 / 2)) • f y)]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by simp
  rw [hdim, ← Nat.cast_smul_eq_nsmul ℝ, ← integral_smul, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  simp only [smul_smul, measureReal_def]
  congr 1
  rw [gaussianRadialDensity, ← gaussian_polar_constant m hm]
  ring

end

end GaloisForLFunctions.HTGeometry
