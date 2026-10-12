import GaloisForLFunctions.RHTower.PaperThetaRelativeTail

/-! # Opposite-parameter cancellation in the actual theta primitive

Combining the two primitives before estimating their norms gains one power
of the source decay rate. All complex parameters are admitted.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry

private theorem shifted_char (z : ℂ) (x y : ℝ) :
    (thetaSource.normalized y : ℂ) * Complex.exp (Complex.I*z*((y-x : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I*z)*(x : ℂ)) * flatCharDensity z y := by
  dsimp [flatCharDensity, sourceChar]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The shifted phase has the positive sign fixed by the literal source character. -/
theorem flatPrimitiveMode_shifted (z : ℂ) (x : ℝ) :
    flatPrimitiveMode z x =
      ∫ y in Ioi x, (thetaSource.normalized y : ℂ) *
        Complex.exp (Complex.I*z*((y-x : ℝ) : ℂ)) := by
  simp_rw [shifted_char]
  rw [integral_const_mul]
  rfl

private theorem integrable_shifted_char (z : ℂ) (x : ℝ) :
    Integrable (fun y => (thetaSource.normalized y : ℂ) *
      Complex.exp (Complex.I*z*((y-x : ℝ) : ℂ))) := by
  simp_rw [shifted_char]
  exact (integrable_flatCharDensity_all z).const_mul _

private theorem norm_exp_pair_le (w : ℂ) :
    ‖Complex.exp w - Complex.exp (-w)‖ ≤ 2*‖w‖*Real.exp ‖w‖ := by
  have h (v : ℂ) : ‖Complex.exp v - 1‖ ≤ ‖v‖*Real.exp ‖v‖ := by
    simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp v 1
  calc
    _ = ‖(Complex.exp w-1)-(Complex.exp (-w)-1)‖ := by congr 1; ring
    _ ≤ ‖Complex.exp w-1‖ + ‖Complex.exp (-w)-1‖ := norm_sub_le _ _
    _ ≤ ‖w‖*Real.exp ‖w‖ + ‖-w‖*Real.exp ‖-w‖ := add_le_add (h w) (h (-w))
    _ = _ := by rw [norm_neg]; ring

private theorem first_moment_bound {r x y : ℝ} (hr : 0 < r) :
    (y-x)*Real.exp (-r*(y-x)) ≤ (2/r)*Real.exp (-(r/2)*(y-x)) := by
  have h : y-x ≤ (2/r)*Real.exp ((r/2)*(y-x)) := by
    have he := Real.add_one_le_exp ((r/2)*(y-x))
    calc
      _ ≤ (2*Real.exp ((r/2)*(y-x)))/r := (le_div_iff₀ hr).mpr (by nlinarith)
      _ = _ := by ring
  calc
    _ ≤ ((2/r)*Real.exp ((r/2)*(y-x)))*Real.exp (-r*(y-x)) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

private theorem integrable_first_moment {r : ℝ} (hr : 0 < r) (x : ℝ) :
    IntegrableOn (fun y => (y-x)*Real.exp (-r*(y-x))) (Ioi x) := by
  refine ((integrableOn_exp_neg_shift (show 0 < r/2 by positivity)).const_mul (2/r)).mono'
    (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hxy : 0 ≤ y-x := sub_nonneg.mpr (show x < y from hy).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (y-x)*Real.exp (-r*(y-x)))]
  exact first_moment_bound hr

private theorem integral_first_moment_le {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ∫ y in Ioi x, (y-x)*Real.exp (-r*(y-x)) ≤ 4/r^2 := by
  calc
    _ ≤ ∫ y in Ioi x, (2/r)*Real.exp (-(r/2)*(y-x)) :=
      setIntegral_mono_on (integrable_first_moment hr x)
        ((integrableOn_exp_neg_shift (show 0 < r/2 by positivity)).const_mul (2/r))
        measurableSet_Ioi (fun _ _ => first_moment_bound hr)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_exp_neg_shift (show 0 < r/2 by positivity)]
      field_simp
      ring

private theorem primitive_pair_le_envelope (z : ℂ) {x : ℝ} (hx : 1 ≤ x)
    (hr : 0 < Real.pi*Real.exp (2*x)-‖z‖) :
    ‖flatPrimitiveMode z x - flatPrimitiveMode (-z) x‖ ≤
      (thetaEnvelopeUpper / thetaSource.mass * thetaEnvelope x) *
        (8*‖z‖/(Real.pi*Real.exp (2*x)-‖z‖)^2) := by
  let K := thetaEnvelopeUpper / thetaSource.mass * thetaEnvelope x
  let r := Real.pi*Real.exp (2*x)-‖z‖
  have hK : 0 ≤ K := (mul_pos (div_pos thetaEnvelopeUpper_pos thetaSource.mass_pos)
    (thetaEnvelope_pos x)).le
  have hb : ∀ y ∈ Ioi x,
      ‖(thetaSource.normalized y : ℂ) * Complex.exp (Complex.I*z*((y-x : ℝ) : ℂ)) -
        (thetaSource.normalized y : ℂ) * Complex.exp (Complex.I*(-z)*((y-x : ℝ) : ℂ))‖ ≤
          (K*(2*‖z‖))*((y-x)*Real.exp (-r*(y-x))) := by
    intro y hy
    have hρ : thetaSource.normalized y ≤ K * Real.exp (-(Real.pi*Real.exp (2*x))*(y-x)) := by
      have hs := thetaCuspFullSource_le_shift hx hy.le
      change thetaSource.k y / thetaSource.mass ≤ _
      rw [div_le_iff₀ thetaSource.mass_pos]
      calc
        _ ≤ (thetaEnvelopeUpper*thetaEnvelope x)*Real.exp (-(Real.pi*Real.exp (2*x))*(y-x)) := hs
        _ = _ := by dsimp [K]; field_simp [thetaSource.mass_ne_zero]
    have hn : ‖Complex.I*z*((y-x : ℝ) : ℂ)‖ = ‖z‖*(y-x) := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (sub_pos.mpr (show x < y from hy))]
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (thetaSource.normalized_pos y)]
    have he := norm_exp_pair_le (Complex.I*z*((y-x : ℝ) : ℂ))
    rw [hn] at he
    rw [show Complex.I*(-z)*((y-x : ℝ) : ℂ) = -(Complex.I*z*((y-x : ℝ) : ℂ)) by ring]
    calc
      _ ≤ (K*Real.exp (-(Real.pi*Real.exp (2*x))*(y-x))) *
          (2*(‖z‖*(y-x))*Real.exp (‖z‖*(y-x))) :=
        mul_le_mul hρ he (norm_nonneg _) (by positivity)
      _ = _ := by
        calc
          _ = K*(2*‖z‖)*(y-x)*
              (Real.exp (-(Real.pi*Real.exp (2*x))*(y-x))*Real.exp (‖z‖*(y-x))) := by ring
          _ = _ := by
            rw [← Real.exp_add, show -(Real.pi*Real.exp (2*x))*(y-x)+‖z‖*(y-x) =
              -r*(y-x) by dsimp [r]; ring]
            ring
  rw [flatPrimitiveMode_shifted, flatPrimitiveMode_shifted, ← integral_sub
    (integrable_shifted_char z x).integrableOn (integrable_shifted_char (-z) x).integrableOn]
  calc
    _ ≤ ∫ y in Ioi x, ‖(thetaSource.normalized y : ℂ) * Complex.exp (Complex.I*z*((y-x : ℝ) : ℂ)) -
        (thetaSource.normalized y : ℂ) * Complex.exp (Complex.I*(-z)*((y-x : ℝ) : ℂ))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioi x, (K*(2*‖z‖))*((y-x)*Real.exp (-r*(y-x))) :=
      setIntegral_mono_on ((integrable_shifted_char z x).sub
        (integrable_shifted_char (-z) x)).norm.integrableOn
        ((integrable_first_moment hr x).const_mul (K*(2*‖z‖))) measurableSet_Ioi hb
    _ ≤ (K*(2*‖z‖))*(4/r^2) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_first_moment_le hr x) (by positivity)
    _ = _ := by ring

private theorem primitive_pair_quotient_le (z : ℂ) {x : ℝ} (hx : 1 ≤ x)
    (hr : 0 < Real.pi*Real.exp (2*x)-‖z‖) :
    ‖flatPrimitiveMode z x - flatPrimitiveMode (-z) x‖ / thetaSource.normalized x ≤
      (8*(thetaEnvelopeUpper/thetaEnvelopeLower)*‖z‖) /
        (Real.pi*Real.exp (2*x)-‖z‖)^2 := by
  have hl : thetaEnvelopeLower / thetaSource.mass * thetaEnvelope x ≤ thetaSource.normalized x := by
    have h := thetaCuspFullSource_ge_envelope (show 0 < x by linarith)
    change _ ≤ thetaSource.k x / thetaSource.mass
    rw [le_div_iff₀ thetaSource.mass_pos]
    calc
      _ = thetaEnvelopeLower * thetaEnvelope x := by field_simp [thetaSource.mass_ne_zero]
      _ ≤ _ := h
  have hL := thetaEnvelopeLower_pos
  have hU := thetaEnvelopeUpper_pos
  have hM := thetaSource.mass_pos
  have hE := thetaEnvelope_pos x
  calc
    _ ≤ ((thetaEnvelopeUpper / thetaSource.mass * thetaEnvelope x) *
        (8*‖z‖/(Real.pi*Real.exp (2*x)-‖z‖)^2)) /
          (thetaEnvelopeLower / thetaSource.mass * thetaEnvelope x) :=
      div_le_div₀ (by positivity) (primitive_pair_le_envelope z hx hr) (by positivity) hl
    _ = _ := by field_simp

/-- Opposite primitives gain a full extra power of the theta tail rate. -/
theorem primitive_pair_quotient_decay (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      ‖flatPrimitiveMode z x - flatPrimitiveMode (-z) x‖ / thetaSource.normalized x ≤
        C*Real.exp (-4*x) := by
  let C := 32*(thetaEnvelopeUpper/thetaEnvelopeLower)*‖z‖/Real.pi^2
  have hL := thetaEnvelopeLower_pos
  have hU := thetaEnvelopeUpper_pos
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hlim : Tendsto (fun x : ℝ => Real.pi*Real.exp (2*x)) atTop atTop := by
    simpa using tendsto_theta_relative_rate 0
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlim.eventually_ge_atTop (2*‖z‖)] with x hx hz
  have hp : 0 < Real.pi*Real.exp (2*x) := mul_pos Real.pi_pos (Real.exp_pos _)
  have hr : 0 < Real.pi*Real.exp (2*x)-‖z‖ := by linarith
  have hhalf : Real.pi*Real.exp (2*x)/2 ≤ Real.pi*Real.exp (2*x)-‖z‖ := by linarith
  have he : Real.exp (2*x)^2 = Real.exp (4*x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  calc
    _ ≤ (8*(thetaEnvelopeUpper/thetaEnvelopeLower)*‖z‖) /
        (Real.pi*Real.exp (2*x)-‖z‖)^2 := primitive_pair_quotient_le z hx hr
    _ ≤ (8*(thetaEnvelopeUpper/thetaEnvelopeLower)*‖z‖) /
        (Real.pi*Real.exp (2*x)/2)^2 := by gcongr
    _ = C*Real.exp (-4*x) := by
      dsimp [C]
      rw [div_pow, mul_pow, he, show -4*x = -(4*x) by ring, Real.exp_neg]
      ring

/-- Exact cancellation identity before taking norms; no divisor condition is needed. -/
theorem flatQuotient_pair_eq (z : ℂ) (x : ℝ) :
    flatQuotient z x + flatQuotient (-z) x + 2 =
      -(Complex.I*z)*(flatPrimitiveMode z x-flatPrimitiveMode (-z) x) /
        (thetaSource.normalized x : ℂ) := by
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.normalized_pos x).ne'
  dsimp [flatQuotient, flatMode]
  field_simp
  ring

/-- The paired source-relative endpoint error has integrable second-order decay. -/
theorem flatQuotient_pair_decay (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      ‖flatQuotient z x + flatQuotient (-z) x + 2‖ ≤ C*Real.exp (-4*x) := by
  obtain ⟨C, hC, hb⟩ := primitive_pair_quotient_decay z
  refine ⟨‖z‖*C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  filter_upwards [hb] with x hx
  rw [flatQuotient_pair_eq, norm_div, norm_mul, norm_neg, norm_mul, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (thetaSource.normalized_pos x)]
  calc
    _ = ‖z‖*(‖flatPrimitiveMode z x-flatPrimitiveMode (-z) x‖/thetaSource.normalized x) := by ring
    _ ≤ ‖z‖*(C*Real.exp (-4*x)) := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _ = _ := by ring

end RHTower.PaperThetaEndpoint
