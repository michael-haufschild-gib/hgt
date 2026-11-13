import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import GaloisForLFunctions.HTGeometry.FourierIntegralDilation

/-!
# Unitary real dilations and weighted energies

The square-root normalization preserves square mass. Physical weights
transform by division of their argument, while Fourier weights transform
by multiplication. The same changes of variables preserve integrability.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped FourierTransform
namespace GaloisForLFunctions.HTGeometry

/-- Unitary normalization of a real dilation. -/
def unitaryRealDilation (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun u => Real.sqrt a * f (a * u)

theorem unitaryRealDilation_inv_cancel {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    unitaryRealDilation a (unitaryRealDilation a⁻¹ f) = f := by
  funext u
  simp only [unitaryRealDilation]
  rw [← mul_assoc a⁻¹ a u, inv_mul_cancel₀ ha.ne', one_mul,
    ← mul_assoc, ← Real.sqrt_mul ha.le, mul_inv_cancel₀ ha.ne', Real.sqrt_one, one_mul]

theorem integral_sq_unitaryRealDilation {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    (∫ u, unitaryRealDilation a f u ^ 2) = ∫ u, f u ^ 2 := by
  simp only [unitaryRealDilation, mul_pow, Real.sq_sqrt ha.le]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun u : ℝ => f u ^ 2) a]
  simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr ha)]
  rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

theorem integral_weighted_sq_unitaryRealDilation {a : ℝ} (ha : 0 < a)
    (f w : ℝ → ℝ) :
    (∫ u, w u * unitaryRealDilation a f u ^ 2) =
      ∫ u, w (u / a) * f u ^ 2 := by
  have heq : (fun u => w u * unitaryRealDilation a f u ^ 2) =
      fun u => a * ((fun v => w (v / a) * f v ^ 2) (a * u)) := by
    funext u
    simp only [unitaryRealDilation, mul_pow, Real.sq_sqrt ha.le]
    rw [mul_div_cancel_left₀ u ha.ne']
    ring
  rw [heq, integral_const_mul,
    Measure.integral_comp_mul_left (fun u : ℝ => w (u / a) * f u ^ 2) a]
  simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr ha)]
  rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

theorem integrable_unitaryRealDilation {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ} (hf : Integrable f) : Integrable (unitaryRealDilation a f) :=
  (hf.comp_mul_left' ha.ne').const_mul _

theorem integrable_sq_unitaryRealDilation {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ} (hf : Integrable (fun u => f u ^ 2)) :
    Integrable (fun u => unitaryRealDilation a f u ^ 2) := by
  simpa only [unitaryRealDilation, mul_pow, Real.sq_sqrt ha.le] using
    (hf.comp_mul_left' ha.ne').const_mul a

theorem integrable_weighted_sq_unitaryRealDilation {a : ℝ} (ha : 0 < a)
    (f w : ℝ → ℝ) (hf : Integrable (fun u => w (u / a) * f u ^ 2)) :
    Integrable (fun u => w u * unitaryRealDilation a f u ^ 2) := by
  apply ((hf.comp_mul_left' ha.ne').const_mul a).congr
  exact Eventually.of_forall fun u => by
    change a * (w ((a * u) / a) * f (a * u) ^ 2) = _
    rw [mul_div_cancel_left₀ u ha.ne']
    simp only [unitaryRealDilation, mul_pow, Real.sq_sqrt ha.le]
    ring

theorem integral_firstMoment_unitaryRealDilation {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    (∫ u, (-u) * unitaryRealDilation a f u ^ 2) = (∫ u, (-u) * f u ^ 2) / a := by
  rw [integral_weighted_sq_unitaryRealDilation ha]
  have heq : (fun u => -(u / a) * f u ^ 2) = fun u => ((-u) * f u ^ 2) / a := by
    funext u
    ring
  rw [heq, integral_div]

theorem fourier_unitaryRealDilation {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) (ξ : ℝ) :
    𝓕 (fun u => (unitaryRealDilation a f u : ℂ)) ξ =
      (Real.sqrt a⁻¹ : ℂ) * 𝓕 (fun u => (f u : ℂ)) (a⁻¹ * ξ) := by
  have heq : (fun u => (unitaryRealDilation a f u : ℂ)) =
      fun u => (Real.sqrt a : ℂ) * (f (a * u) : ℂ) := by
    funext u
    exact Complex.ofReal_mul _ _
  rw [heq]
  exact _root_.RHTower.fourier_normalized_dilation (fun u => (f u : ℂ)) a ha ξ

theorem norm_sq_fourier_unitaryRealDilation {a : ℝ} (ha : 0 < a)
    (f : ℝ → ℝ) (ξ : ℝ) :
    ‖𝓕 (fun u => (unitaryRealDilation a f u : ℂ)) ξ‖ ^ 2 =
      a⁻¹ * ‖𝓕 (fun u => (f u : ℂ)) (a⁻¹ * ξ)‖ ^ 2 := by
  rw [fourier_unitaryRealDilation ha, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (inv_pos.mpr ha).le]

/-- A normalized spatial dilation transports the spectral weight by the inverse change of variables. -/
theorem integral_weighted_fourier_sq_unitaryRealDilation {a : ℝ} (ha : 0 < a)
    (f w : ℝ → ℝ) :
    (∫ ξ, w ξ * ‖𝓕 (fun u => (unitaryRealDilation a f u : ℂ)) ξ‖ ^ 2) =
      ∫ ξ, w (a * ξ) * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2 := by
  have heq : (fun ξ => w ξ * ‖𝓕 (fun u => (unitaryRealDilation a f u : ℂ)) ξ‖ ^ 2) =
      fun ξ => a⁻¹ * ((fun η => w (a * η) * ‖𝓕 (fun u => (f u : ℂ)) η‖ ^ 2) (a⁻¹ * ξ)) := by
    funext ξ
    dsimp only
    rw [norm_sq_fourier_unitaryRealDilation ha, ← mul_assoc a a⁻¹ ξ,
      mul_inv_cancel₀ ha.ne', one_mul]
    ring
  rw [heq, integral_const_mul, Measure.integral_comp_mul_left
    (fun ξ : ℝ => w (a * ξ) * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2) a⁻¹]
  simp only [inv_inv, abs_of_pos ha, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]

theorem integrable_weighted_fourier_sq_unitaryRealDilation {a : ℝ} (ha : 0 < a)
    (f w : ℝ → ℝ)
    (hf : Integrable (fun ξ => w (a * ξ) * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2)) :
    Integrable (fun ξ => w ξ * ‖𝓕 (fun u => (unitaryRealDilation a f u : ℂ)) ξ‖ ^ 2) := by
  apply ((hf.comp_mul_left' (inv_ne_zero ha.ne')).const_mul a⁻¹).congr
  exact Eventually.of_forall fun ξ => by
    change a⁻¹ * (w (a * (a⁻¹ * ξ)) * ‖𝓕 (fun u => (f u : ℂ)) (a⁻¹ * ξ)‖ ^ 2) =
      w ξ * ‖𝓕 (fun u => (unitaryRealDilation a f u : ℂ)) ξ‖ ^ 2
    rw [← mul_assoc a a⁻¹ ξ, mul_inv_cancel₀ ha.ne', one_mul,
      norm_sq_fourier_unitaryRealDilation ha]
    ring

theorem integrable_weighted_fourier_sq_of_unitaryRealDilation {a : ℝ} (ha : 0 < a)
    (f w : ℝ → ℝ)
    (hf : Integrable (fun ξ => w ξ * ‖𝓕 (fun u => (unitaryRealDilation a f u : ℂ)) ξ‖ ^ 2)) :
    Integrable (fun ξ => w (a * ξ) * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2) := by
  apply ((hf.comp_mul_left' ha.ne').const_mul a).congr
  exact Eventually.of_forall fun ξ => by
    change a * (w (a * ξ) * ‖𝓕 (fun u => (unitaryRealDilation a f u : ℂ)) (a * ξ)‖ ^ 2) =
      w (a * ξ) * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2
    rw [norm_sq_fourier_unitaryRealDilation ha, ← mul_assoc a⁻¹ a ξ,
      inv_mul_cancel₀ ha.ne', one_mul]
    calc
      _ = (a * a⁻¹) * (w (a * ξ) * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2) := by ring
      _ = _ := by rw [mul_inv_cancel₀ ha.ne', one_mul]

#print axioms unitaryRealDilation_inv_cancel
#print axioms integral_firstMoment_unitaryRealDilation
#print axioms integrable_weighted_sq_unitaryRealDilation
#print axioms integrable_weighted_fourier_sq_unitaryRealDilation
#print axioms integrable_weighted_fourier_sq_of_unitaryRealDilation
#print axioms integral_sq_unitaryRealDilation
#print axioms norm_sq_fourier_unitaryRealDilation
#print axioms integral_weighted_fourier_sq_unitaryRealDilation
end GaloisForLFunctions.HTGeometry
