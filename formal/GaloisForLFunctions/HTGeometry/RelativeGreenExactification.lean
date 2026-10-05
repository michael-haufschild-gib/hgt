import GaloisForLFunctions.HTGeometry.RelativeScaleDefectKernel
import GaloisForLFunctions.RHTower.PerronLaplaceKernel

/-!
# Relative Green exactification of the ordered defect

The signed ordered defect `F_{a,b}(t) = ab ω_t(a,b)` is exactly divisible by the relative grade
`a - b`: `(a + b) F_{a,b} = (a - b) H_{a,b}` `(RGE.6a)` with
`H_{a,b}(t) = 1 - e^{-(a+b)t} + (a+b)/(a-b) (e^{-at} - e^{-bt})` for `a ≠ b` and its continuous
diagonal value `H_{a,a}(t) = 1 - e^{-2at} - 2at e^{-at}`.  Its Laplace transform is
`ab(a+b)/(z(z+a)(z+b)(z+a+b))` for `Re z > 0` `(RGE.6)`.  On the diagonal the ordered defect
vanishes, and off it `H = Δ₊ Δ₋⁻¹ F` with `Δ₊ = a + b`, `Δ₋ = a - b` `(RGE.16)`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

/-! ### The Green-exactified response -/

/-- The Green-exactified response `H_{a,b}(t)` `(RGE.5)`, with its continuous diagonal value. -/
def greenExact (a b t : ℝ) : ℝ :=
  if a = b then 1 - Real.exp (-(2 * a) * t) - 2 * a * t * Real.exp (-a * t)
  else 1 - Real.exp (-(a + b) * t) + (a + b) / (a - b) * (Real.exp (-a * t) - Real.exp (-b * t))

theorem greenExact_of_ne {a b : ℝ} (hab : a ≠ b) (t : ℝ) :
    greenExact a b t = 1 - Real.exp (-(a + b) * t) +
      (a + b) / (a - b) * (Real.exp (-a * t) - Real.exp (-b * t)) := by
  rw [greenExact, if_neg hab]

theorem greenExact_self (a t : ℝ) :
    greenExact a a t = 1 - Real.exp (-(2 * a) * t) - 2 * a * t * Real.exp (-a * t) := by
  rw [greenExact, if_pos rfl]

/-- `H_{a,b} = ((a+b)/(a-b)) F_{a,b}` off the diagonal `(RGE.5)`. -/
theorem greenExact_eq_div_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (t : ℝ) :
    greenExact a b t = (a + b) / (a - b) * (a * b * defectKernel t a b) := by
  have hs : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hp : a + b ≠ 0 := by positivity
  rw [greenExact_of_ne hab, defectKernel_closed ha hb]
  field_simp
  ring

/-- **`(RGE.6a)`: orientation–positivity conservation** `(a + b) F_{a,b} = (a - b) H_{a,b}`. -/
theorem conservation {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    (a + b) * (a * b * defectKernel t a b) = (a - b) * greenExact a b t := by
  by_cases hab : a = b
  · subst hab
    rw [defectKernel_self, sub_self]
    ring
  · have hs : a - b ≠ 0 := sub_ne_zero.mpr hab
    rw [greenExact_eq_div_mul ha hb hab]
    field_simp

theorem continuous_greenExact (a b : ℝ) : Continuous (greenExact a b) := by
  by_cases hab : a = b
  · subst hab
    rw [show greenExact a a = fun t =>
      1 - Real.exp (-(2 * a) * t) - 2 * a * t * Real.exp (-a * t) from funext (greenExact_self a)]
    fun_prop
  · rw [show greenExact a b = fun t => 1 - Real.exp (-(a + b) * t) +
      (a + b) / (a - b) * (Real.exp (-a * t) - Real.exp (-b * t)) from
        funext (greenExact_of_ne hab)]
    fun_prop

/-- **`(RGE.16)`**: off the diagonal, `H = Δ₊ Δ₋⁻¹ F` with `Δ₊ = a + b`, `Δ₋ = a - b`. -/
theorem greenExact_eq_sum_mul_inv_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (t : ℝ) :
    greenExact a b t = (a + b) * ((a - b)⁻¹ * (a * b * defectKernel t a b)) := by
  rw [greenExact_eq_div_mul ha hb hab, div_eq_mul_inv, mul_assoc]

/-- The antisymmetric ordered defect vanishes on the diagonal sector `a = b`. -/
theorem defect_diag (a t : ℝ) : a * a * defectKernel t a a = 0 := by
  rw [defectKernel_self, mul_zero]

/-- The Moore–Penrose identities of the scalar Green inverse `d ↦ d⁻¹` (with `0⁻¹ = 0`):
`d d⁺ d = d` and `d⁺ d d⁺ = d⁺`. -/
theorem greenInverse_penrose (d : ℝ) : d * d⁻¹ * d = d ∧ d⁻¹ * d * d⁻¹ = d⁻¹ := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · exact ⟨by field_simp, by field_simp⟩

/-! ### The Laplace transform `(RGE.6)` -/

private theorem laplace_cexp {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-c * t)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Complex.exp (-c * t) = 1 / c := by
  refine ⟨integrableOn_exp_mul_complex_Ioi (by simpa using hc) 0, ?_⟩
  rw [integral_exp_mul_complex_Ioi (by simpa using hc) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  field_simp

/-- **`(RGE.6)`**: `∫₀^∞ e^{-zt} H_{a,b}(t) dt = ab(a+b)/(z(z+a)(z+b)(z+a+b))` for `Re z > 0`. -/
theorem laplace_greenExact {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-z * t) * (greenExact a b t : ℂ) =
      (a * b * (a + b) : ℂ) / (z * (z + a) * (z + b) * (z + a + b)) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hsa : 0 < (z + (a : ℝ)).re := by simp; linarith
  have hsb : 0 < (z + (b : ℝ)).re := by simp; linarith
  have h2 : z + (a : ℝ) ≠ 0 := fun h => by rw [h] at hsa; simp at hsa
  have h3 : z + (b : ℝ) ≠ 0 := fun h => by rw [h] at hsb; simp at hsb
  have hab' : 0 < (z + (a : ℝ) + b).re := by simp; linarith
  have h4 : z + (a : ℝ) + b ≠ 0 := fun h => by rw [h] at hab'; simp at hab'
  by_cases hab : a = b
  · subst hab
    have hs2 : 0 < (z + ((2 * a : ℝ) : ℂ)).re := by simp; linarith
    have hpt : ∀ t : ℝ, Complex.exp (-z * t) * (greenExact a a t : ℂ) =
        Complex.exp (-z * t) - Complex.exp (-(z + ((2 * a : ℝ) : ℂ)) * t) -
          (2 * a : ℂ) * ((t : ℂ) * Complex.exp (-((z + (a : ℝ)) * t))) := fun t => by
      rw [greenExact_self]
      push_cast
      rw [show -(z + 2 * (a : ℂ)) * t = -z * t + (-(2 * a) * t) by ring,
        show -((z + (a : ℂ)) * t) = -z * t + (-a * t) by ring, Complex.exp_add, Complex.exp_add]
      ring
    simp_rw [hpt]
    obtain ⟨i1, e1⟩ := laplace_cexp hz
    obtain ⟨i2, e2⟩ := laplace_cexp hs2
    have i3 := (RHTower.integrableOn_mul_exp_neg_mul hsa).const_mul (2 * a : ℂ)
    rw [integral_sub (f := fun t : ℝ => Complex.exp (-z * t) -
          Complex.exp (-(z + ((2 * a : ℝ) : ℂ)) * t))
        (g := fun t : ℝ => (2 * a : ℂ) * ((t : ℂ) * Complex.exp (-((z + (a : ℝ)) * t))))
        (i1.sub i2) i3,
      integral_sub (f := fun t : ℝ => Complex.exp (-z * t))
        (g := fun t : ℝ => Complex.exp (-(z + ((2 * a : ℝ) : ℂ)) * t)) i1 i2,
      integral_const_mul, e1, e2, RHTower.integral_mul_exp_neg_mul_Ioi hsa]
    have h5 : z + ((2 * a : ℝ) : ℂ) ≠ 0 := fun h => by rw [h] at hs2; simp at hs2
    push_cast at h2 h4 h5 ⊢
    have h6 : z + a + a ≠ 0 := by rw [add_assoc, ← two_mul]; exact h5
    field_simp
    ring
  · have hs : (a : ℂ) - b ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hab
    have hpt : ∀ t : ℝ, Complex.exp (-z * t) * (greenExact a b t : ℂ) =
        (((a + b) / (a - b) : ℝ) : ℂ) *
          (Complex.exp (-z * t) * ((a * b * defectKernel t a b : ℝ) : ℂ)) := fun t => by
      rw [greenExact_eq_div_mul ha hb hab]
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_const_mul, laplace_defect ha hb hz]
    push_cast at h2 h3 h4 ⊢
    field_simp

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
