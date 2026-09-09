import GaloisForLFunctions.HTGeometry.GaussBonnetExtendedFirstLaw

/-!
# Logarithmic-entropy Gibbs energy and reference invariance

Formalize the model-A free energy of arXiv:2609.00025 as an actual function,
including its partial derivatives. Changing the reference length adds one
radius-independent constant at fixed external temperature. Therefore every
pairwise phase comparison and every global minimizer is unchanged.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

/-- Free energy at independently prescribed external temperature. -/
def egbOffShellGibbsA (P T Q a l r : ℝ) : ℝ :=
  egbMass P Q a r - T * egbEntropyA a l r

theorem egbOffShellGibbsA_temperature_derivative (P T Q a l x : ℝ) :
    HasDerivAt (fun t => egbOffShellGibbsA P t Q a l (exp x))
      (-egbEntropyA a l (exp x)) T := by
  have h := ((hasDerivAt_id T).mul_const (egbEntropyA a l (exp x))).const_sub (egbMass P Q a (exp x))
  apply h.congr_deriv
  ring

theorem egbOffShellGibbsA_pressure_derivative (P T Q a l x : ℝ) :
    HasDerivAt (fun p => egbOffShellGibbsA p T Q a l (exp x)) (egbThermodynamicVolume (exp x)) P :=
  (egbMass_pressure_derivative P Q a (exp x)).sub_const _

theorem egbOffShellGibbsA_charge_derivative (P T Q a l x : ℝ) :
    HasDerivAt (fun q => egbOffShellGibbsA P T q a l (exp x)) (egbElectricPotential Q (exp x)) Q :=
  (egbMass_charge_derivative P Q a x).sub_const _

theorem egbOffShellGibbsA_coupling_derivative (P T Q a l x : ℝ) :
    HasDerivAt (fun b => egbOffShellGibbsA P T Q b l (exp x))
      (a / exp x - 8 * Real.pi * a * T * log (exp x / exp l)) a := by
  have h := (egbMass_coupling_derivative P Q a x).sub ((egbEntropyA_coupling_derivative a l x).const_mul T)
  apply h.congr_deriv
  ring

theorem egbOffShellGibbsA_reference_derivative (P T Q a l x : ℝ) :
    HasDerivAt (fun c => egbOffShellGibbsA P T Q a c (exp x)) (4 * Real.pi * a ^ 2 * T) l := by
  have h := ((egbEntropyA_reference_derivative a l x).const_mul T).const_sub (egbMass P Q a (exp x))
  apply h.congr_deriv
  ring

/-- Equilibria are exactly the stationary points of the genuine radial free energy. -/
theorem egbOffShellGibbsA_radius_derivative (P T Q a l x : ℝ) :
    HasDerivAt (egbOffShellGibbsA P T Q a l)
      ((egbTemperatureA P Q a (exp x) - T) * (2 * Real.pi * exp x + 4 * Real.pi * a ^ 2 / exp x)) (exp x) := by
  have h := (egbMass_derivative P Q a x).sub ((egbEntropyA_derivative a l x).const_mul T)
  apply h.congr_deriv
  have hf := (egb_firstLaw_both_prescriptions P Q a l x).1
  rw [(egbMass_derivative P Q a x).deriv, (egbEntropyA_derivative a l x).deriv] at hf
  rw [hf]
  ring

theorem egbEntropyA_radial_slope_pos (a l x : ℝ) :
    0 < deriv (egbEntropyA a l) (exp x) := by
  rw [(egbEntropyA_derivative a l x).deriv]
  positivity

theorem egbOffShellGibbsA_stationary_iff (P T Q a l x : ℝ) :
    deriv (egbOffShellGibbsA P T Q a l) (exp x) = 0 ↔ egbTemperatureA P Q a (exp x) = T := by
  have hs : 2 * Real.pi * exp x + 4 * Real.pi * a ^ 2 / exp x ≠ 0 := by positivity
  rw [(egbOffShellGibbsA_radius_derivative P T Q a l x).deriv, mul_eq_zero]
  simp [hs, sub_eq_zero]

theorem egbOffShellGibbsA_increasing_iff (P T Q a l x : ℝ) :
    0 < deriv (egbOffShellGibbsA P T Q a l) (exp x) ↔ T < egbTemperatureA P Q a (exp x) := by
  have hs : 0 < 2 * Real.pi * exp x + 4 * Real.pi * a ^ 2 / exp x := by positivity
  rw [(egbOffShellGibbsA_radius_derivative P T Q a l x).deriv, mul_pos_iff_of_pos_right hs, sub_pos]

theorem egbOffShellGibbsA_reference_shift (P T Q a l c x : ℝ) :
    egbOffShellGibbsA P T Q a (l + c) (exp x) =
      egbOffShellGibbsA P T Q a l (exp x) + 4 * Real.pi * a ^ 2 * T * c := by
  unfold egbOffShellGibbsA
  rw [egbEntropyA_scale_shift]
  ring

/-- Phase free-energy differences are exactly independent of entropy normalization. -/
theorem egbOffShellGibbsA_difference_reference_invariant (P T Q a l c x y : ℝ) :
    egbOffShellGibbsA P T Q a (l + c) (exp x) - egbOffShellGibbsA P T Q a (l + c) (exp y) =
      egbOffShellGibbsA P T Q a l (exp x) - egbOffShellGibbsA P T Q a l (exp y) := by
  rw [egbOffShellGibbsA_reference_shift, egbOffShellGibbsA_reference_shift]
  ring

theorem egbOffShellGibbsA_order_reference_invariant (P T Q a l c x y : ℝ) :
    egbOffShellGibbsA P T Q a (l + c) (exp x) ≤ egbOffShellGibbsA P T Q a (l + c) (exp y) ↔
      egbOffShellGibbsA P T Q a l (exp x) ≤ egbOffShellGibbsA P T Q a l (exp y) := by
  rw [egbOffShellGibbsA_reference_shift, egbOffShellGibbsA_reference_shift, add_le_add_iff_right]

/-- Every global minimizer among positive radii survives every reference change. -/
theorem egbOffShellGibbsA_minimizers_reference_invariant (P T Q a l c x : ℝ) :
    (∀ y : ℝ, egbOffShellGibbsA P T Q a (l + c) (exp x) ≤ egbOffShellGibbsA P T Q a (l + c) (exp y)) ↔
      (∀ y : ℝ, egbOffShellGibbsA P T Q a l (exp x) ≤ egbOffShellGibbsA P T Q a l (exp y)) := by
  simp_rw [egbOffShellGibbsA_order_reference_invariant]

theorem egbOffShellGibbsA_force_reference_invariant (P T Q a l c x : ℝ) :
    deriv (egbOffShellGibbsA P T Q a (l + c)) (exp x) = deriv (egbOffShellGibbsA P T Q a l) (exp x) := by
  rw [(egbOffShellGibbsA_radius_derivative P T Q a (l + c) x).deriv,
    (egbOffShellGibbsA_radius_derivative P T Q a l x).deriv]

end GaloisForLFunctions.HTGeometry
