import GaloisForLFunctions.HTGeometry.FokasLenellsRawCoefficientEndpoints

/-!
# Whole-line identities that evaluate the cubic scattering coefficient

The existing Hermite coordinate commutator and the Schwartz trace identity
turn the spatially weighted derivative into the initial mass. Ordinary
integration by parts supplies both reflected product identities. These are
closed identities for arbitrary Schwartz initial data, with no PDE premise.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

theorem rawMixedTotal_eq (q : SchwartzMap ℝ ℂ) :
    rawMixedTotal q = ∫ x : ℝ, q x*reflectedDerivative q x := by
  simp only [rawMixedTotal,rawMixedProfile_apply]

theorem integrable_coordinate_derivative (q : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => (x : ℂ)*deriv q x) := by
  have hh : Integrable (fun x : ℝ => mulXCLM (derivSCLM q) x) := (mulXCLM (derivSCLM q)).integrable
  simpa only [mulXCLM_apply,derivSCLM_apply] using hh

/-- The Hermite coordinate commutator evaluates the weighted derivative exactly. -/
theorem integral_coordinate_derivative (q : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, (x : ℂ)*deriv q x) = -∫ x : ℝ, q x := by
  have he : (fun x : ℝ => deriv (mulXCLM q) x) = fun x => q x+(x : ℂ)*deriv q x := by
    funext x
    have hh := congrArg (fun f : SchwartzMap ℝ ℂ => f x) (derivSCLM_mulXCLM q)
    simpa only [derivSCLM_apply,_root_.add_apply,mulXCLM_apply] using hh
  have hz := RHTower.integral_deriv_schwartz_eq_zero (mulXCLM q)
  rw [he,integral_add q.integrable (integrable_coordinate_derivative q)] at hz
  linear_combination hz

theorem integrable_derivative_reflected_product (q : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => deriv q x*q (-x)) := by
  have hh : Integrable (fun x : ℝ => mulS (SchwartzMap.derivCLM ℂ ℂ q) (RHTower.negSchwartz' q) x) :=
    (mulS (SchwartzMap.derivCLM ℂ ℂ q) (RHTower.negSchwartz' q)).integrable
  simpa only [mulS_apply,SchwartzMap.derivCLM_apply,RHTower.negSchwartz'_apply] using hh

theorem integral_derivative_reflected_product (q : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, deriv q x*q (-x)) = -rawMixedTotal q := by
  have hi1 := integrable_derivative_reflected_product q
  have hi2 : Integrable (fun x : ℝ => q x*reflectedDerivative q x) := by
    have hh : Integrable (fun x : ℝ => rawMixedProfile q x) := (rawMixedProfile q).integrable
    simpa only [rawMixedProfile_apply] using hh
  have hi : Integrable (fun x : ℝ => q x*q (-x)) := by
    have hh : Integrable (fun x : ℝ => mulS q (RHTower.negSchwartz' q) x) :=
      (mulS q (RHTower.negSchwartz' q)).integrable
    simpa only [mulS_apply,RHTower.negSchwartz'_apply] using hh
  have hd : ∀ x : ℝ, HasDerivAt (fun y => q y*q (-y))
      (deriv q x*q (-x)+q x*reflectedDerivative q x) x :=
    fun x => (q.hasDerivAt x).mul (rawReflectedProfile_hasDerivAt q x)
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd (hi1.add hi2) hi
  rw [integral_add hi1 hi2] at hz
  rw [rawMixedTotal_eq]
  linear_combination hz

theorem integrable_square_reflected_derivative (q : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => q x^2*reflectedDerivative q x) := by
  have hh : Integrable (fun x : ℝ => mulS (mulS q q) (reflectedDerivative q) x) :=
    (mulS (mulS q q) (reflectedDerivative q)).integrable
  simpa only [mulS_apply,pow_two] using hh

/-- The local reflected cubic is twice the compatibility coupling, with the exact sign. -/
theorem integral_square_reflected_derivative (q : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, q x^2*reflectedDerivative q x) = -2*∫ x : ℝ, q x*q (-x)*deriv q x := by
  have hi1 : Integrable (fun x : ℝ => (2 : ℂ)*(q x*q (-x)*deriv q x)) :=
    (compatibilityCubic_integrable q).const_mul 2
  have hi2 := integrable_square_reflected_derivative q
  have hi : Integrable (fun x : ℝ => q x*q x*q (-x)) := by
    have hh : Integrable (fun x : ℝ => mulS (mulS q q) (RHTower.negSchwartz' q) x) :=
      (mulS (mulS q q) (RHTower.negSchwartz' q)).integrable
    simpa only [mulS_apply,RHTower.negSchwartz'_apply] using hh
  have hd : ∀ x : ℝ, HasDerivAt (fun y => q y*q y*q (-y))
      ((2 : ℂ)*(q x*q (-x)*deriv q x)+q x^2*reflectedDerivative q x) x := by
    intro x
    have hq := q.hasDerivAt x
    convert! (hq.mul hq).mul (rawReflectedProfile_hasDerivAt q x) using 1
    change (2 : ℂ)*(q x*q (-x)*deriv q x)+q x^2*reflectedDerivative q x =
      (deriv q x*q x+q x*deriv q x)*q (-x)+(q x*q x)*reflectedDerivative q x
    ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd (hi1.add hi2) hi
  rw [integral_add hi1 hi2,integral_const_mul] at hz
  linear_combination hz

end
end GaloisForLFunctions.HTGeometry.FokasLenells
