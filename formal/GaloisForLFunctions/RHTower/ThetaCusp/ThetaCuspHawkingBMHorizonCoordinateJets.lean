import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceLiftJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceCompactPower
import GaloisForLFunctions.HTGeometry.ElementaryHorizonJets

/-!
# Elementary radial factors in the horizon coordinate

On the exterior `t < 0` the radial unit is `√(1-z)` with `z = horizonCoordinate t`, and
`e^{ut} = z^{u/2} (1+√(1-z))^{-u}`.  Hence the source amplitude and the radial lift are `z^{u/2}`
times explicit profiles in `z`, and those profiles have uniform second-order jets on every closed
frequency ball.  Nothing here evaluates a Green response.
-/

namespace RHTower.D4BMJointSource
open Complex Set Metric D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

theorem radialUnit_eq_sqrt (t : ℝ) (ht : t < 0) :
    radialUnit t = Real.sqrt (1 - horizonCoordinate t) := by
  rw [horizonCoordinate, sub_sub_cancel, Real.sqrt_sq (radialUnit_bounds t ht).1.le]

theorem one_add_radialUnit (t : ℝ) : 1 + radialUnit t = Real.exp (-t) / Real.cosh t := by
  have hc := (Real.cosh_pos t).ne'
  rw [radialUnit, ← Real.cosh_sub_sinh]
  field_simp
  ring

theorem horizonCoordinate_eq_inv_cosh_sq (t : ℝ) :
    horizonCoordinate t = (1 / Real.cosh t) ^ 2 := by
  have hc := Real.cosh_pos t
  rw [horizonCoordinate, radialUnit]
  field_simp
  linear_combination Real.cosh_sq_sub_sinh_sq t

theorem sqrt_horizonCoordinate (t : ℝ) :
    Real.sqrt (horizonCoordinate t) = 1 / Real.cosh t := by
  have hc := Real.cosh_pos t
  rw [horizonCoordinate_eq_inv_cosh_sq, Real.sqrt_sq (by positivity)]

theorem exp_eq_sqrt_div (t : ℝ) :
    Real.exp t = Real.sqrt (horizonCoordinate t) / (1 + radialUnit t) := by
  rw [sqrt_horizonCoordinate t, one_add_radialUnit]
  have hc := (Real.cosh_pos t).ne'
  have he := (Real.exp_pos (-t)).ne'
  field_simp
  rw [← Real.exp_add]
  simp

/-- `e^{ut} = z^{u/2} (1+√(1-z))^{-u}` on the exterior. -/
theorem exp_mul_tortoise (u : ℂ) (t : ℝ) (ht : t < 0) :
    Complex.exp (u * (t:ℂ)) =
      (horizonCoordinate t : ℂ) ^ (u / 2) * ((1 + radialUnit t : ℝ) : ℂ) ^ (-u) := by
  have hz := horizonCoordinate_interior t ht
  have hu1 : 0 < 1 + radialUnit t := by linarith [(radialUnit_bounds t ht).1]
  have hs : 0 < Real.sqrt (horizonCoordinate t) := Real.sqrt_pos.mpr hz.1
  have ht' : (t:ℂ) = ((Real.log (Real.sqrt (horizonCoordinate t) / (1 + radialUnit t)) : ℝ) : ℂ) := by
    rw [← exp_eq_sqrt_div t, Real.log_exp]
  rw [ht', Real.log_div hs.ne' hu1.ne', Real.log_sqrt hz.1.le, cpow_ofReal_pos_eq hz.1,
    cpow_ofReal_pos_eq hu1, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The source amplitude as a `z^{u/2}`-dressed profile. -/
def amplitudeProfile (s a : ℂ) (T : ℂ → ℂ) (u : ℂ) (z : ℝ) : ℂ :=
  ((1 + Real.sqrt (1 - z) : ℝ) : ℂ) ^ (2 * s - u) * (a ^ 2 * T u)

/-- The radial lift as a `z^{u/2}`-dressed profile. -/
def liftProfile (s a : ℂ) (T : ℂ → ℂ) (u : ℂ) (z : ℝ) : ℂ :=
  (-s * (s - 1) / 4) * (amplitudeProfile s a T u z * (Real.sqrt (1 - z) : ℂ) ^ 3)

theorem sourceAmplitude_eq_profile (s a : ℂ) (T : ℂ → ℂ) (u : ℂ) (t : ℝ) (ht : t < 0) :
    sourceAmplitude s u a (T u) t =
      (horizonCoordinate t : ℂ) ^ (u / 2) * amplitudeProfile s a T u (horizonCoordinate t) := by
  have hu1 : 0 < 1 + radialUnit t := by linarith [(radialUnit_bounds t ht).1]
  have hne : ((1 + radialUnit t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu1.ne'
  rw [sourceAmplitude, exp_mul_tortoise u t ht, amplitudeProfile, ← radialUnit_eq_sqrt t ht,
    power, show 2 * s - u = 2 * s + (-u) by ring, Complex.cpow_add _ _ hne]
  ring

theorem radialLift_eq_profile (s a : ℂ) (T : ℂ → ℂ) (u : ℂ) (t : ℝ) (ht : t < 0) :
    radialLift s u a (T u) t =
      (horizonCoordinate t : ℂ) ^ (u / 2) * liftProfile s a T u (horizonCoordinate t) := by
  rw [radialLift, sourceAmplitude_eq_profile s a T u t ht, liftProfile, ← radialUnit_eq_sqrt t ht]
  ring

/-- The exponent `2s - u` is bounded on a closed frequency ball. -/
theorem norm_two_mul_sub_le (s w : ℂ) (R : ℝ) {u : ℂ} (hu : u ∈ closedBall w R) :
    ‖2 * s - u‖ ≤ ‖2 * s - w‖ + R := by
  have h := mem_closedBall.mp hu
  rw [dist_eq_norm] at h
  calc ‖2 * s - u‖ = ‖(2 * s - w) - (u - w)‖ := by ring_nf
    _ ≤ ‖2 * s - w‖ + ‖u - w‖ := norm_sub_le _ _
    _ ≤ ‖2 * s - w‖ + R := by linarith

/-- Uniform jet of the amplitude profile on a closed frequency ball. -/
theorem amplitudeProfile_jet (s a w : ℂ) (R : ℝ) (hR : 0 ≤ R) (T : ℂ → ℂ) {K : ℝ}
    (hK : ∀ u ∈ closedBall w R, ‖T u‖ ≤ K) :
    ∃ C : ℝ, HasUniformJet2 (closedBall w R) (min (1 / 2) (1 / (‖2 * s - w‖ + R + 1)))
      (amplitudeProfile s a T)
      (fun u => (2:ℂ) ^ (2 * s - u) * (a ^ 2 * T u))
      (fun u => -(2 * s - u) * (2:ℂ) ^ (2 * s - u) / 4 * (a ^ 2 * T u)) C := by
  have hB : 0 ≤ ‖2 * s - w‖ + R := by positivity
  have hj := hasUniformJet2_cpow_one_add_sqrt (closedBall w R) (α := fun u => 2 * s - u) hB
    (fun u hu => norm_two_mul_sub_le s w R hu)
  have hk : ∀ u ∈ closedBall w R, ‖a ^ 2 * T u‖ ≤ ‖a‖ ^ 2 * K := fun u hu => by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hK u hu) (by positivity)
  refine ⟨_, ((hj.const_mul hk).congr (fun u _ z _ => ?_)).congr_coeff (fun u _ => ?_)
    (fun u _ => ?_)⟩
  · simp only [amplitudeProfile]; ring
  · ring
  · ring

/-- Uniform jet of the lift profile on a closed frequency ball. -/
theorem liftProfile_jet (s a w : ℂ) (R : ℝ) (hR : 0 ≤ R) (T : ℂ → ℂ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ u ∈ closedBall w R, ‖T u‖ ≤ K) :
    ∃ (b C : ℝ), 0 < b ∧ b ≤ 1 / 2 ∧
      HasUniformJet2 (closedBall w R) b (liftProfile s a T)
        (fun u => (-s * (s - 1) / 4) * ((2:ℂ) ^ (2 * s - u) * (a ^ 2 * T u)))
        (fun u => (-s * (s - 1) / 4) *
          ((2:ℂ) ^ (2 * s - u) * (a ^ 2 * T u) * (-3 / 2) +
            -(2 * s - u) * (2:ℂ) ^ (2 * s - u) / 4 * (a ^ 2 * T u))) C := by
  obtain ⟨C₁, h₁⟩ := amplitudeProfile_jet s a w R hR T hK
  set b := min (1 / 2) (1 / (‖2 * s - w‖ + R + 1)) with hb
  have hb0 : 0 < b := lt_min (by norm_num) (by positivity)
  have hb1 : b ≤ 1 / 2 := min_le_left _ _
  have hsq := (hasUniformJet2_sqrt_one_sub (closedBall w R)).mono_radius hb1
  obtain ⟨C₃, h₃⟩ := hsq.pow_three (by linarith) (by norm_num) (by norm_num : (0:ℝ) ≤ 1)
    (fun _ _ => by simp) (fun _ _ => by norm_num)
  -- coefficient bounds for the amplitude jet
  have hB : 0 ≤ ‖2 * s - w‖ + R := by positivity
  have hc₀ : ∀ u ∈ closedBall w R, ‖(2:ℂ) ^ (2 * s - u) * (a ^ 2 * T u)‖ ≤
      (2:ℝ) ^ (‖2 * s - w‖ + R) * (‖a‖ ^ 2 * K) := fun u hu => by
    rw [norm_mul, norm_mul, norm_pow]
    apply mul_le_mul _ (mul_le_mul_of_nonneg_left (hK u hu) (by positivity)) (by positivity)
      (by positivity)
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      ((Complex.re_le_norm _).trans (norm_two_mul_sub_le s w R hu))
  have hc₁ : ∀ u ∈ closedBall w R, ‖-(2 * s - u) * (2:ℂ) ^ (2 * s - u) / 4 * (a ^ 2 * T u)‖ ≤
      (‖2 * s - w‖ + R) * ((2:ℝ) ^ (‖2 * s - w‖ + R) * (‖a‖ ^ 2 * K)) := fun u hu => by
    have := hc₀ u hu
    rw [show -(2 * s - u) * (2:ℂ) ^ (2 * s - u) / 4 * (a ^ 2 * T u) =
      (-(2 * s - u) / 4) * ((2:ℂ) ^ (2 * s - u) * (a ^ 2 * T u)) by ring, norm_mul]
    apply mul_le_mul _ this (norm_nonneg _) hB
    rw [norm_div, norm_neg]
    calc ‖2 * s - u‖ / ‖(4:ℂ)‖ ≤ ‖2 * s - u‖ := by
          rw [show ‖(4:ℂ)‖ = 4 by simp]
          exact div_le_self (norm_nonneg _) (by norm_num)
      _ ≤ ‖2 * s - w‖ + R := norm_two_mul_sub_le s w R hu
  set M := max ((2:ℝ) ^ (‖2 * s - w‖ + R) * (‖a‖ ^ 2 * K))
    ((‖2 * s - w‖ + R) * ((2:ℝ) ^ (‖2 * s - w‖ + R) * (‖a‖ ^ 2 * K))) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left (by positivity)
  have hM' : 0 ≤ max M 3 := le_max_of_le_right (by norm_num)
  have hC₁ : 0 ≤ C₁ := by
    have := h₁ w (mem_closedBall_self hR) b ⟨hb0, le_rfl⟩
    have hb2 : 0 < b ^ 2 := by positivity
    nlinarith [norm_nonneg (amplitudeProfile s a T w b - (2:ℂ) ^ (2 * s - w) * (a ^ 2 * T w) -
      -(2 * s - w) * (2:ℂ) ^ (2 * s - w) / 4 * (a ^ 2 * T w) * (b:ℂ))]
  have hC₃ : 0 ≤ C₃ := by
    have := h₃ w (mem_closedBall_self hR) b ⟨hb0, le_rfl⟩
    have hb2 : 0 < b ^ 2 := by positivity
    nlinarith [norm_nonneg ((Real.sqrt (1 - b) : ℂ) ^ 3 - (1:ℂ) ^ 3 - 3 * (1:ℂ) ^ 2 * (-1 / 2) * (b:ℂ))]
  have hprod := h₁.mul (by linarith) h₃ hC₁ hC₃ hM'
    (fun u hu => (hc₀ u hu).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun u hu => (hc₁ u hu).trans ((le_max_right _ _).trans (le_max_left _ _)))
    (fun _ _ => by simp)
    (fun _ _ => by norm_num)
  refine ⟨b, _, hb0, hb1, ((hprod.const_mul (k := fun _ => -s * (s - 1) / 4)
    (K := ‖-s * (s - 1) / 4‖) (fun _ _ => le_rfl)).congr (fun u _ z _ => ?_)).congr_coeff
    (fun u _ => ?_) (fun u _ => ?_)⟩
  · simp only [liftProfile]
  · ring
  · ring

end
end RHTower.D4BMJointSource
