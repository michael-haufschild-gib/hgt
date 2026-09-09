import GaloisForLFunctions.HTGeometry.GaussBonnetGibbsAGauge
import GaloisForLFunctions.HTGeometry.GaussBonnetSmarrAnomaly

/-!
# Exact scaling laws with a logarithmic entropy reference

Apply dimensional rescaling to the mass, temperatures, conjugates, entropy,
and Gibbs functions from arXiv:2609.00025. Positive radii and scale factors
are represented by exponentials. A fixed reference length produces an
explicit logarithmic term; scaling the reference with the geometry restores
homogeneity. All identities concern the actual thermodynamic functions.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

theorem egbMass_dimensional_scaling (P Q a x s : ℝ) :
    egbMass (P / exp s ^ 2) (Q * exp s) (a * exp s) (exp x * exp s) =
      exp s * egbMass P Q a (exp x) := by
  unfold egbMass
  field_simp

theorem egbTemperatureA_dimensional_scaling (P Q a x s : ℝ) :
    egbTemperatureA (P / exp s ^ 2) (Q * exp s) (a * exp s) (exp x * exp s) =
      egbTemperatureA P Q a (exp x) / exp s := by
  have h₁ : exp x ^ 2 + 2 * a ^ 2 ≠ 0 := by positivity
  have h₂ : (exp x * exp s) ^ 2 + 2 * (a * exp s) ^ 2 ≠ 0 := by positivity
  unfold egbTemperatureA
  field_simp

theorem egbTemperatureB_dimensional_scaling (P Q a x s : ℝ) :
    egbTemperatureB (P / exp s ^ 2) (Q * exp s) (a * exp s) (exp x * exp s) =
      egbTemperatureB P Q a (exp x) / exp s := by
  unfold egbTemperatureB
  field_simp

theorem egbPressureA_dimensional_scaling (T Q a x s : ℝ) :
    egbPressureA (T / exp s) (Q * exp s) (a * exp s) (exp x * exp s) =
      egbPressureA T Q a (exp x) / exp s ^ 2 := by
  unfold egbPressureA
  field_simp

theorem egbPressureB_dimensional_scaling (T Q a x s : ℝ) :
    egbPressureB (T / exp s) (Q * exp s) (a * exp s) (exp x * exp s) =
      egbPressureB T Q a (exp x) / exp s ^ 2 := by
  unfold egbPressureB
  field_simp

theorem egbEntropyB_dimensional_scaling (x s : ℝ) :
    egbEntropyB (exp x * exp s) = exp s ^ 2 * egbEntropyB (exp x) := by
  unfold egbEntropyB
  ring

/-- Holding the reference length fixed produces the precise logarithmic anomaly. -/
theorem egbEntropyA_fixed_reference_scaling (a l x s : ℝ) :
    egbEntropyA (a * exp s) l (exp x * exp s) =
      exp s ^ 2 * egbEntropyA a l (exp x) + 4 * Real.pi * a ^ 2 * exp s ^ 2 * s := by
  simp only [egbEntropyA, log_div (mul_ne_zero (exp_ne_zero x) (exp_ne_zero s)) (exp_ne_zero l),
    log_mul (exp_ne_zero x) (exp_ne_zero s), log_div (exp_ne_zero x) (exp_ne_zero l), log_exp]
  ring

/-- Scaling the reference length along with the radius restores entropy homogeneity. -/
theorem egbEntropyA_moving_reference_scaling (a l x s : ℝ) :
    egbEntropyA (a * exp s) (l + s) (exp x * exp s) = exp s ^ 2 * egbEntropyA a l (exp x) := by
  simp only [egbEntropyA, log_div (mul_ne_zero (exp_ne_zero x) (exp_ne_zero s)) (exp_ne_zero (l + s)),
    log_mul (exp_ne_zero x) (exp_ne_zero s), log_div (exp_ne_zero x) (exp_ne_zero l), log_exp]
  ring

theorem egbThermodynamicVolume_dimensional_scaling (r s : ℝ) :
    egbThermodynamicVolume (r * exp s) = exp s ^ 3 * egbThermodynamicVolume r := by
  unfold egbThermodynamicVolume
  ring

theorem egbElectricPotential_dimensional_scaling (Q x s : ℝ) :
    egbElectricPotential (Q * exp s) (exp x * exp s) = egbElectricPotential Q (exp x) := by
  unfold egbElectricPotential
  field_simp

/-- The same fixed-reference logarithm changes the coupling conjugate's scaling law. -/
theorem egbCouplingConjugateA_fixed_reference_scaling (P Q a l x s : ℝ) :
    egbCouplingConjugateA (P / exp s ^ 2) (Q * exp s) (a * exp s) l (exp x * exp s) =
      (egbCouplingConjugateA P Q a l (exp x) - 4 * Real.pi * egbTemperatureA P Q a (exp x) * s) / exp s := by
  unfold egbCouplingConjugateA
  rw [egbTemperatureA_dimensional_scaling]
  simp only [log_div (mul_ne_zero (exp_ne_zero x) (exp_ne_zero s)) (exp_ne_zero l),
    log_mul (exp_ne_zero x) (exp_ne_zero s), log_div (exp_ne_zero x) (exp_ne_zero l), log_exp]
  ring

theorem egbCouplingConjugateA_moving_reference_scaling (P Q a l x s : ℝ) :
    egbCouplingConjugateA (P / exp s ^ 2) (Q * exp s) (a * exp s) (l + s) (exp x * exp s) =
      egbCouplingConjugateA P Q a l (exp x) / exp s := by
  unfold egbCouplingConjugateA
  rw [egbTemperatureA_dimensional_scaling]
  simp only [log_div (mul_ne_zero (exp_ne_zero x) (exp_ne_zero s)) (exp_ne_zero (l + s)),
    log_mul (exp_ne_zero x) (exp_ne_zero s), log_div (exp_ne_zero x) (exp_ne_zero l), log_exp]
  ring

theorem egbReferenceConjugateA_dimensional_scaling (P Q a x s : ℝ) :
    egbReferenceConjugateA (P / exp s ^ 2) (Q * exp s) (a * exp s) (exp x * exp s) =
      exp s * egbReferenceConjugateA P Q a (exp x) := by
  unfold egbReferenceConjugateA
  rw [egbTemperatureA_dimensional_scaling]
  field_simp

theorem egbOffShellGibbsA_fixed_reference_scaling (P T Q a l x s : ℝ) :
    egbOffShellGibbsA (P / exp s ^ 2) (T / exp s) (Q * exp s) (a * exp s) l (exp x * exp s) =
      exp s * (egbOffShellGibbsA P T Q a l (exp x) - 4 * Real.pi * a ^ 2 * T * s) := by
  unfold egbOffShellGibbsA
  rw [egbMass_dimensional_scaling, egbEntropyA_fixed_reference_scaling]
  field_simp
  ring

theorem egbOffShellGibbsA_moving_reference_scaling (P T Q a l x s : ℝ) :
    egbOffShellGibbsA (P / exp s ^ 2) (T / exp s) (Q * exp s) (a * exp s) (l + s) (exp x * exp s) =
      exp s * egbOffShellGibbsA P T Q a l (exp x) := by
  unfold egbOffShellGibbsA
  rw [egbMass_dimensional_scaling, egbEntropyA_moving_reference_scaling]
  field_simp

theorem egbOffShellGibbsB_dimensional_scaling (P T Q a x s : ℝ) :
    egbOffShellGibbs (P / exp s ^ 2) (T / exp s) (Q * exp s) (a * exp s) (exp x * exp s) =
      exp s * egbOffShellGibbs P T Q a (exp x) := by
  unfold egbOffShellGibbs
  rw [egbMass_dimensional_scaling, egbEntropyB_dimensional_scaling]
  field_simp

end GaloisForLFunctions.HTGeometry
