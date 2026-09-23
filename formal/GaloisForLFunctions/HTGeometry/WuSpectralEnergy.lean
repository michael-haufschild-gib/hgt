import GaloisForLFunctions.HTGeometry.WuExponentialEnergy
import GaloisForLFunctions.HTGeometry.FokasLenellsSpectralVolterra

/-!
# Exponential energy bounds for the Fokas–Lenells spectral equation

The global Picard solution already has exponential growth rate `spectralMass`.
Removing exactly this known growth makes Wu's Lemma 2.3 applicable, without
smallness of the potential or restrictions on the spectral parameter.
The same construction controls the actual spectral derivative.
-/
namespace GaloisForLFunctions.HTGeometry.Wu
open FokasLenells MeasureTheory
noncomputable section

/-- The globally bounded spectral solution after removing its proved growth envelope. -/
def spectralOrbit (f g h : SchwartzMap ℝ ℂ) (z : ℂ) (v : SpectralVector) :
    BoundedContinuousFunction ℝ SpectralVector :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s => Real.exp (-(spectralMass f g h z * |s|)) • spectralSolution f g h z v s)
    ((by fun_prop : Continuous (fun s : ℝ => Real.exp (-(spectralMass f g h z * |s|)))).smul
      (continuous_spectralSolution f g h z v)) ‖v‖
    (fun s => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(spectralMass f g h z * |s|)) * ‖spectralSolution f g h z v s‖ ≤
          Real.exp (-(spectralMass f g h z * |s|)) *
            (‖v‖ * Real.exp (spectralMass f g h z * |s|)) :=
          mul_le_mul_of_nonneg_left (spectralSolution_bound f g h z v s) (Real.exp_pos _).le
        _ = ‖v‖ := by rw [mul_left_comm, ← Real.exp_add]; simp)

theorem norm_spectralOrbit_le (f g h : SchwartzMap ℝ ℂ) (z : ℂ) (v : SpectralVector) :
    ‖spectralOrbit f g h z v‖ ≤ ‖v‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg _) _

/-- Damping separates the known spectral growth from the energy integration gain. -/
theorem spectral_energy_le (f g h : SchwartzMap ℝ ℂ) (z : ℂ) (v : SpectralVector) (d t : ℝ) :
    energy d t (fun s => Real.exp (-(spectralMass f g h z * |s|)) •
      spectralSolution f g h z v s) ≤ ‖v‖ ^ (2 : ℕ) / (2 * Real.exp d) := by
  exact (energy_le d t (spectralOrbit f g h z v)).trans
    (div_le_div_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_spectralOrbit_le f g h z v))
      (by positivity))

/-- The derivative of the actual spectral solution, in the same exponential frame. -/
def spectralDerivativeOrbit (f g h : SchwartzMap ℝ ℂ) (z : ℂ) (v : SpectralVector) :
    BoundedContinuousFunction ℝ SpectralVector :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s => spectralKernel f g h z s s (spectralOrbit f g h z v s))
    (((continuous_spectralKernel f g h z).comp (continuous_id.prodMk continuous_id)).clm_apply
      (spectralOrbit f g h z v).continuous) (spectralMass f g h z * ‖v‖)
    (fun s => by
      calc ‖spectralKernel f g h z s s (spectralOrbit f g h z v s)‖ ≤
          ‖spectralKernel f g h z s s‖ * ‖spectralOrbit f g h z v s‖ :=
          (spectralKernel f g h z s s).le_opNorm _
        _ ≤ spectralMass f g h z * ‖v‖ :=
          mul_le_mul (spectralKernel_bound f g h z s s)
            (((spectralOrbit f g h z v).norm_coe_le_norm s).trans (norm_spectralOrbit_le f g h z v))
            (norm_nonneg _) (spectralMass_nonneg f g h z))

/-- An unconditional integrated derivative bound for every spectral parameter and Schwartz triple. -/
theorem spectral_derivative_energy_le (f g h : SchwartzMap ℝ ℂ) (z : ℂ)
    (v : SpectralVector) (d t : ℝ) :
    energy d t (fun s => Real.exp (-(spectralMass f g h z * |s|)) •
      deriv (spectralSolution f g h z v) s) ≤
      (spectralMass f g h z * ‖v‖) ^ (2 : ℕ) / (2 * Real.exp d) := by
  have heq : (fun s => Real.exp (-(spectralMass f g h z * |s|)) •
      deriv (spectralSolution f g h z v) s) = spectralDerivativeOrbit f g h z v := by
    funext s
    rw [(spectralSolution_hasDerivAt f g h z v s).deriv]
    change _ = spectralKernel f g h z s s
      (Real.exp (-(spectralMass f g h z * |s|)) • spectralSolution f g h z v s)
    rw [map_smul]
  rw [heq]
  have hb : ‖spectralDerivativeOrbit f g h z v‖ ≤ spectralMass f g h z * ‖v‖ :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
      (mul_nonneg (spectralMass_nonneg f g h z) (norm_nonneg _)) _
  exact (energy_le d t (spectralDerivativeOrbit f g h z v)).trans
    (div_le_div_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg (spectralMass_nonneg _ _ _ _) (norm_nonneg _))).mpr hb)
      (by positivity))

/-- The actual initial-data Lax solution inherits the same gain, with its reflected derivative. -/
theorem initial_spectral_energy_le (q : SchwartzMap ℝ ℂ) (z : ℂ)
    (v : SpectralVector) (d t : ℝ) :
    energy d t (fun s =>
      Real.exp (-(spectralMass (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
        (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) z * |s|)) •
        initialSpectralSolution q z v s) ≤ ‖v‖ ^ (2 : ℕ) / (2 * Real.exp d) :=
  spectral_energy_le _ _ _ z v d t

end
end GaloisForLFunctions.HTGeometry.Wu
