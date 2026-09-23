import GaloisForLFunctions.HTGeometry.FokasLenellsRawOddPrimitives

/-!
# Schwartz trace identities for the genuine fifth coefficient

The nonlinear fifth density is an exact derivative. A second use of the
corpus's Hermite coordinate commutator reduces the remaining quadratic
spatial weight to the first moment of the initial profile.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

theorem integrable_first_moment_density (q : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => (x : ℂ)*q x) := by
  have hh : Integrable (fun x : ℝ => mulXCLM q x) := (mulXCLM q).integrable
  simpa only [mulXCLM_apply] using hh

theorem integrable_quartic_derivative (q : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => q x^(4 : ℕ)*deriv q x) := by
  have hh := (mulS (mulS (mulS q q) (mulS q q)) (SchwartzMap.derivCLM ℂ ℂ q)).integrable (μ := volume)
  convert! hh using 1
  funext x
  simp only [mulS_apply,SchwartzMap.derivCLM_apply]
  ring

/-- The nonlinear density in the symmetrized fifth coefficient has zero total integral. -/
theorem integral_quartic_derivative (q : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, q x^(4 : ℕ)*deriv q x) = 0 := by
  let g := mulS (mulS (mulS q q) (mulS q q)) q
  have he : (g : ℝ → ℂ) = fun x : ℝ => q x^(5 : ℕ) := by
    funext x
    simp only [g,mulS_apply]
    ring
  have hd (x : ℝ) : deriv g x = (5 : ℂ)*(q x^(4 : ℕ)*deriv q x) := by
    rw [he]
    convert! ((q.hasDerivAt x).pow 5).deriv using 1
    ring
  have hz := RHTower.integral_deriv_schwartz_eq_zero g
  simp only [hd,integral_const_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem integrable_coordinate_sq_derivative (q : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => (x : ℂ)^(2 : ℕ)*deriv q x) := by
  have hh := (mulXCLM (mulXCLM (derivSCLM q))).integrable (μ := volume)
  convert! hh using 1
  funext x
  simp only [mulXCLM_apply,derivSCLM_apply]
  ring

/-- The second coordinate commutator evaluates the remaining fifth-order spatial density. -/
theorem integral_coordinate_sq_derivative (q : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, (x : ℂ)^(2 : ℕ)*deriv q x) = -2*∫ x : ℝ, (x : ℂ)*q x := by
  have he : (fun x : ℝ => (x : ℂ)*deriv (mulXCLM q) x) =
      fun x : ℝ => (x : ℂ)*q x+(x : ℂ)^(2 : ℕ)*deriv q x := by
    funext x
    have hh := congrArg (fun f : SchwartzMap ℝ ℂ => f x) (derivSCLM_mulXCLM q)
    simp only [derivSCLM_apply,_root_.add_apply,mulXCLM_apply] at hh
    rw [hh]
    ring
  have hi : Integrable (fun x : ℝ => (x : ℂ)*q x) := integrable_first_moment_density q
  have hz := integral_coordinate_derivative (mulXCLM q)
  rw [he,integral_add hi (integrable_coordinate_sq_derivative q)] at hz
  simp only [mulXCLM_apply] at hz
  linear_combination hz

/-- Odd projection preserves precisely the spatial first moment relevant to fifth-order reflection. -/
theorem integral_coordinate_oddInitialPart (q : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, (x : ℂ)*oddInitialPart q x) = ∫ x : ℝ, (x : ℂ)*q x := by
  have hi : Integrable (fun x : ℝ => (x : ℂ)*q x) := integrable_first_moment_density q
  have hr : Integrable (fun x : ℝ => (x : ℂ)*q (-x)) := by
    simpa only [RHTower.negSchwartz'_apply] using
      integrable_first_moment_density (RHTower.negSchwartz' q)
  have href : (∫ x : ℝ, (x : ℂ)*q (-x)) = -(∫ x : ℝ, (x : ℂ)*q x) := by
    have hh := integral_neg_eq_self (fun x : ℝ => (x : ℂ)*q x) volume
    simp only [Complex.ofReal_neg,neg_mul,integral_neg] at hh
    linear_combination -hh
  have he : (fun x : ℝ => (x : ℂ)*oddInitialPart q x) =
      fun x : ℝ => ((x : ℂ)*q x-(x : ℂ)*q (-x))/2 := by
    funext x
    rw [oddInitialPart_apply]
    ring
  rw [he,integral_div,integral_sub hi hr,href]
  ring

/-- Odd projection of the corpus's derivative operator has an exactly prescribed first moment. -/
theorem integral_coordinate_oddDerivative (q : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, (x : ℂ)*oddInitialPart (SchwartzMap.derivCLM ℂ ℂ q) x) = -∫ x : ℝ, q x := by
  rw [integral_coordinate_oddInitialPart]
  simpa only [SchwartzMap.derivCLM_apply] using integral_coordinate_derivative q

end
end GaloisForLFunctions.HTGeometry.FokasLenells
