import GaloisForLFunctions.HTGeometry.GaussBonnetClapeyron

/-!
# Full differentiated first laws for both Gauss--Bonnet prescriptions

Apply equation (5) of arXiv:2609.00025 to the existing mass and entropy
functions. Recover the electric and coupling conjugates from actual partial
derivatives. The coupling is α=a², so its work term is 2a Ψ da. If the
arbitrary logarithmic reference coordinate l is changed, its auxiliary
conjugate exactly compensates the entropy normalization change.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def egbElectricPotential (Q r : ℝ) : ℝ := Q / r

def egbCouplingConjugateA (P Q a l r : ℝ) : ℝ :=
  1 / (2 * r) - 4 * Real.pi * egbTemperatureA P Q a r * log (r / exp l)

def egbCouplingConjugateB (r : ℝ) : ℝ := 1 / (2 * r)

/-- Auxiliary work coefficient for changing the entropy's log reference length. -/
def egbReferenceConjugateA (P Q a r : ℝ) : ℝ := 4 * Real.pi * a ^ (2 : ℕ) * egbTemperatureA P Q a r

theorem egbMass_charge_derivative (P Q a x : ℝ) :
    HasDerivAt (fun q => egbMass P q a (exp x)) (egbElectricPotential Q (exp x)) Q := by
  have h := (((((hasDerivAt_id Q).pow 2).add_const (a ^ (2 : ℕ))).div_const (2 * exp x)).const_add (exp x / 2)).add_const
    (4 * Real.pi * P * exp x ^ (3 : ℕ) / 3)
  apply h.congr_deriv
  unfold egbElectricPotential
  norm_num only [Nat.cast_ofNat, pow_one, id_eq]
  field_simp

theorem egbMass_coupling_derivative (P Q a x : ℝ) :
    HasDerivAt (fun b => egbMass P Q b (exp x)) (a / exp x) a := by
  have h := (((((hasDerivAt_id a).pow 2).const_add (Q ^ (2 : ℕ))).div_const (2 * exp x)).const_add (exp x / 2)).add_const
    (4 * Real.pi * P * exp x ^ (3 : ℕ) / 3)
  apply h.congr_deriv
  norm_num only [Nat.cast_ofNat, pow_one, id_eq]
  field_simp

theorem egbEntropyA_coupling_derivative (a l x : ℝ) :
    HasDerivAt (fun b => egbEntropyA b l (exp x))
      (8 * Real.pi * a * log (exp x / exp l)) a := by
  have h := ((((hasDerivAt_id a).pow 2).const_mul (4 * Real.pi)).mul_const (log (exp x / exp l))).const_add
    (Real.pi * exp x ^ (2 : ℕ))
  apply h.congr_deriv
  norm_num only [Nat.cast_ofNat, pow_one, id_eq]
  ring

/-- The scale derivative is computed from the logarithm, rather than postulated as a gauge rule. -/
theorem egbEntropyA_reference_derivative (a l x : ℝ) :
    HasDerivAt (fun c => egbEntropyA a c (exp x)) (-4 * Real.pi * a ^ (2 : ℕ)) l := by
  have he : (fun c => egbEntropyA a c (exp x)) =
      (fun c => Real.pi * exp x ^ (2 : ℕ) + 4 * Real.pi * a ^ (2 : ℕ) * (x - c)) := by
    funext c
    simp only [egbEntropyA, log_div (exp_ne_zero _) (exp_ne_zero _), log_exp]
  rw [he]
  have h := (((hasDerivAt_id l).const_sub x).const_mul (4 * Real.pi * a ^ (2 : ℕ))).const_add (Real.pi * exp x ^ (2 : ℕ))
  apply h.congr_deriv
  ring

/-- The coupling conjugate is obtained by subtracting the entropy contribution from the actual mass derivative. -/
theorem egbCouplingConjugateA_partial_first_law (P Q a l x : ℝ) :
    deriv (fun b => egbMass P Q b (exp x)) a =
      egbTemperatureA P Q a (exp x) * deriv (fun b => egbEntropyA b l (exp x)) a +
        2 * a * egbCouplingConjugateA P Q a l (exp x) := by
  rw [(egbMass_coupling_derivative P Q a x).deriv, (egbEntropyA_coupling_derivative a l x).deriv]
  unfold egbCouplingConjugateA
  ring

theorem egbCouplingConjugateB_partial_first_law (P Q a x : ℝ) :
    deriv (fun b => egbMass P Q b (exp x)) a = 2 * a * egbCouplingConjugateB (exp x) := by
  rw [(egbMass_coupling_derivative P Q a x).deriv]
  unfold egbCouplingConjugateB
  ring

theorem egbReferenceConjugateA_compensation (P Q a l x : ℝ) :
    egbTemperatureA P Q a (exp x) * deriv (fun c => egbEntropyA a c (exp x)) l +
      egbReferenceConjugateA P Q a (exp x) = 0 := by
  rw [(egbEntropyA_reference_derivative a l x).deriv]
  unfold egbReferenceConjugateA
  ring

/-- The full model-A one-form identity for arbitrary radial, pressure, charge, coupling, and reference variations. -/
theorem egbExtendedFirstLawA (P Q a l x vr vP vQ va vl : ℝ) :
    deriv (egbMass P Q a) (exp x) * vr + deriv (fun p => egbMass p Q a (exp x)) P * vP +
      deriv (fun q => egbMass P q a (exp x)) Q * vQ + deriv (fun b => egbMass P Q b (exp x)) a * va =
    egbTemperatureA P Q a (exp x) *
      (deriv (egbEntropyA a l) (exp x) * vr + deriv (fun b => egbEntropyA b l (exp x)) a * va +
        deriv (fun c => egbEntropyA a c (exp x)) l * vl) +
      egbThermodynamicVolume (exp x) * vP + egbElectricPotential Q (exp x) * vQ +
      2 * a * egbCouplingConjugateA P Q a l (exp x) * va + egbReferenceConjugateA P Q a (exp x) * vl := by
  rw [(egb_firstLaw_both_prescriptions P Q a l x).1, (egbMass_pressure_derivative P Q a (exp x)).deriv,
    (egbMass_charge_derivative P Q a x).deriv, egbCouplingConjugateA_partial_first_law P Q a l x,
    (egbEntropyA_reference_derivative a l x).deriv]
  unfold egbReferenceConjugateA
  ring

/-- The same differentiated mass law with area entropy and the modified temperature. -/
theorem egbExtendedFirstLawB (P Q a x vr vP vQ va : ℝ) :
    deriv (egbMass P Q a) (exp x) * vr + deriv (fun p => egbMass p Q a (exp x)) P * vP +
      deriv (fun q => egbMass P q a (exp x)) Q * vQ + deriv (fun b => egbMass P Q b (exp x)) a * va =
    egbTemperatureB P Q a (exp x) * deriv egbEntropyB (exp x) * vr +
      egbThermodynamicVolume (exp x) * vP + egbElectricPotential Q (exp x) * vQ +
      2 * a * egbCouplingConjugateB (exp x) * va := by
  rw [(egb_firstLaw_both_prescriptions P Q a 0 x).2, (egbMass_pressure_derivative P Q a (exp x)).deriv,
    (egbMass_charge_derivative P Q a x).deriv, egbCouplingConjugateB_partial_first_law P Q a x]

/-- Changing the entropy reference changes the coupling conjugate by the compensating amount. -/
theorem egbCouplingConjugateA_scale_shift (P Q a l c x : ℝ) :
    egbCouplingConjugateA P Q a (l + c) (exp x) =
      egbCouplingConjugateA P Q a l (exp x) + 4 * Real.pi * egbTemperatureA P Q a (exp x) * c := by
  simp only [egbCouplingConjugateA, log_div (exp_ne_zero _) (exp_ne_zero _), log_exp]
  ring

end GaloisForLFunctions.HTGeometry
