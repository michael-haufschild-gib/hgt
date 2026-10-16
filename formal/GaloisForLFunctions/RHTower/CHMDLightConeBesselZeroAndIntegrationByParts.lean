import GaloisForLFunctions.RHTower.CHMDQuarticMomentAndSecondOrderPacketPositivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# CHMD: Forward Light-Cone Linearity, the Order-Zero Bessel Derivative Law, and Integration by Parts of the Prime Wave

Stage 20 (`CHMDLightConePrimeKernelDecomposition`) decomposed each component of the CHMD causal wave
`φ_Λ(y) = chmdWave y` as a forward light-cone transmutation `L = lightConeTransmute`:
$$L[A](y) = A(y) - \frac{y^2}{2}\int_{-1}^1 B\bigl(2 y^2 (1 - t^2)\bigr) A(y t)\,dt,$$
where `B(w) = lightConeBessel w = Σ_k (-w/4)^k / (k! (k+1)!)` (`J₁(x) = (x/2) B(x²)`), and Stage 23
(`CHMDQuarticMomentAndSecondOrderPacketPositivity`) established the inverse Volterra reconstruction
`L⁻¹[chmdPrimeWave] = masslessPrimeWave > 0`.

On the forward light cone `w = 2 y² (1 - t²) ≥ 0`, the raw series bound `|B(w)| ≤ e^{w/4}` grows like
`e^{y²/2}`, obscuring the cancellation of the oscillatory Bessel kernel. This module resolves that
obstruction unconditionally by introducing the order-zero light-cone Bessel kernel
`lightConeBesselZero w = Σ_k (-w/4)^k / (k!)² = J₀(√w)` and integrating `lightConeTransmute` by parts:

1. **Forward Light-Cone Linearity and Three-Part Transmutation of `chmdWave`**:
   We prove that `lightConeTransmute` and `inverseLightConeTransmute` preserve continuity and are
   linear on continuous waves, deduce continuity of `masslessArchWave` and `masslessPrimeWave`, and
   establish the forward three-part linearity identity (`chmdWave_eq_lightConeTransmute`):
   $$\operatorname{chmdWave}(y) = L\Bigl[\frac{2}{\cos^2(1/4)}\cosh(\cdot/2)
     + \frac{1}{2\pi}\operatorname{masslessArchWave} - \operatorname{masslessPrimeWave}\Bigr](y),$$
   together with the pole–prime difference identity
   $$\operatorname{chmdPoleWave}(y) - \operatorname{chmdPrimeWave}(y) =
     L\Bigl[\frac{2}{\cos^2(1/4)}\cosh(\cdot/2) - \operatorname{masslessPrimeWave}\Bigr](y).$$

2. **The Order-Zero Light-Cone Bessel Kernel `lightConeBesselZero`, Exact Derivative Law, and `|J₀| ≤ 1`**:
   We define the entire function
   $$\operatorname{lightConeBesselZero}(w) := \sum_{k=0}^\infty \frac{(-w/4)^k}{(k!)^2}$$
   and its real restriction `lightConeBesselZeroReal`, prove `besselJ 0 x = lightConeBesselZeroReal (x²)`
   (so `lightConeBesselZeroReal w = J₀(√w)` for `w ≥ 0`), and establish the termwise derivative laws:
   $$\frac{d}{dw}\operatorname{lightConeBesselZero}(w) = -\frac{1}{4}\operatorname{lightConeBessel}(w)
     \qquad (\text{`hasDerivAt_lightConeBesselZero`}),$$
   $$\frac{d}{dt}\Bigl[\operatorname{lightConeBesselZeroReal}\bigl(c y^2 (1 - t^2)\bigr)\Bigr] =
     \frac{c y^2 t}{2}\operatorname{lightConeBesselReal}\bigl(c y^2 (1 - t^2)\bigr)
     \qquad (\text{`hasDerivAt_lightConeBesselZeroReal_light_cone`}).$$
   Combining `J₀'(x) = -J₁(x)` (`hasDerivAt_besselJ_zero`) with Bessel's odd-order integral for `J₁`
   yields Bessel's integral for `J₀`:
   $$J_0(x) = \frac{2}{\pi}\int_0^{\pi/2} \cos(x \sin\theta)\,d\theta
     \qquad (\text{`besselJ_zero_eq_integral`}),$$
   and hence the uniform bound `|J₀(x)| ≤ 1` (`abs_besselJ_zero_le_one`) and
   `|lightConeBesselZeroReal (c y² (1 - t²))| ≤ 1` inside the light cone `|t| ≤ 1` (`c ≥ 0`).

3. **Integration by Parts of `lightConeTransmute` and Cumulative Prime-Wave Identities**:
   With the cumulative d'Alembert prime wave
   $$\operatorname{cumulativeMasslessPrimeWave}(x) := \int_0^x P_0(s)\,ds,$$
   we integrate `lightConeTransmute` by parts on `[0, 1]` to express both the `J₀` light-cone integral
   and `chmdPrimeWave(y)` in terms of `∫_0^{y t} P₀(s) ds` and the bounded kernel `J₀`:
   $$y \int_0^1 J_0\Bigl(\sqrt{2 y^2 (1 - t^2)}\Bigr) P_0(y t)\,dt =
     \int_0^y P_0(s)\,ds - y^2 \int_0^1 t\,B\bigl(2 y^2 (1 - t^2)\bigr)
       \Bigl(\int_0^{y t} P_0(s)\,ds\Bigr)\,dt,$$
   $$\operatorname{chmdPrimeWave}(y) = P_0(y) - \int_0^1 P_0(y u)\,du
     + \int_0^1 \operatorname{lightConeBesselZeroReal}\bigl(2 y^2 (1 - t^2)\bigr) P_0(y t)\,dt
     - y^2 \int_0^1 B\bigl(2 y^2 (1 - t^2)\bigr)\Bigl(P_0(y t) - t \int_0^t P_0(y u)\,du\Bigr)\,dt.$$
   Because `|J₀| ≤ 1` and `P₀ > 0`, the `t`-weighted dispersive Bessel tail against the cumulative
   prime wave is unconditionally nonnegative and bounded above by `2 ∫_0^y P₀(s) ds` for all `y ≥ 0`
   (`cumulative_bessel_tail_nonneg_and_le_two_mul`), completely eliminating the `e^{y²/2}` Gaussian
   factor on the cumulative prime channel.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators Real Nat ComplexConjugate

noncomputable section

namespace RHTower.CHMDLightConeBesselZero

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry RHTower.EvenSector
open RHTower.CHMDStage11 RHTower.CHMDStage22 RHTower.CHMDLightCone RHTower.CHMDQuarticMoment

/-! ## Section 1: Forward Light-Cone Linearity and Three-Part Transmutation of `chmdWave` -/

/-- Forward light-cone transmutation preserves continuity. -/
theorem continuous_lightConeTransmute {A : ℝ → ℝ} (hA : Continuous A) :
    Continuous (lightConeTransmute A) := by
  unfold lightConeTransmute
  refine hA.sub ((by fun_prop : Continuous fun y : ℝ => y ^ 2 / 2).mul ?_)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun y t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * A (y * t))
    ((continuous_lightConeBesselReal.comp (by fun_prop)).mul (hA.comp (by fun_prop))) (-1) 1

/-- Inverse light-cone transmutation preserves continuity. -/
theorem continuous_inverseLightConeTransmute {A : ℝ → ℝ} (hA : Continuous A) :
    Continuous (inverseLightConeTransmute A) := by
  unfold inverseLightConeTransmute
  refine hA.add ((by fun_prop : Continuous fun y : ℝ => y ^ 2 / 2).mul ?_)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun y t => lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) * A (y * t))
    ((continuous_lightConeBesselReal.comp (by fun_prop)).mul (hA.comp (by fun_prop))) (-1) 1

/-- The massless archimedean wave `masslessArchWave` is continuous on `ℝ`. -/
theorem continuous_masslessArchWave : Continuous masslessArchWave := by
  have h : masslessArchWave = inverseLightConeTransmute chmdArchWave :=
    funext fun y => (inverseLightConeTransmute_chmdArchWave y).symm
  rw [h]
  exact continuous_inverseLightConeTransmute continuous_chmdArchWave

/-- The massless d'Alembert prime wave `masslessPrimeWave` (`P₀`) is continuous on `ℝ`. -/
theorem continuous_masslessPrimeWave : Continuous masslessPrimeWave := by
  have h : masslessPrimeWave = inverseLightConeTransmute chmdPrimeWave :=
    funext fun y => (inverseLightConeTransmute_chmdPrimeWave y).symm
  rw [h]
  exact continuous_inverseLightConeTransmute continuous_chmdPrimeWave

/-- Scalar linearity of `lightConeTransmute`. -/
theorem lightConeTransmute_const_mul (c : ℝ) (A : ℝ → ℝ) (y : ℝ) :
    lightConeTransmute (fun v => c * A v) y = c * lightConeTransmute A y := by
  unfold lightConeTransmute
  have hcongr : (∫ t in (-1 : ℝ)..1,
      lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * (c * A (y * t))) =
      c * ∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * A (y * t) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hcongr]
  ring

/-- Additive linearity of `lightConeTransmute` on continuous waves. -/
theorem lightConeTransmute_add {A B : ℝ → ℝ} (hA : Continuous A) (hB : Continuous B) (y : ℝ) :
    lightConeTransmute (fun v => A v + B v) y =
      lightConeTransmute A y + lightConeTransmute B y := by
  unfold lightConeTransmute
  set Bt : ℝ → ℝ := fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2))
  have hBc : Continuous Bt := continuous_lightConeBesselReal.comp (by fun_prop)
  have hiA : IntervalIntegrable (fun t => Bt t * A (y * t)) volume (-1) 1 :=
    (hBc.mul (hA.comp (by fun_prop))).intervalIntegrable _ _
  have hiB : IntervalIntegrable (fun t => Bt t * B (y * t)) volume (-1) 1 :=
    (hBc.mul (hB.comp (by fun_prop))).intervalIntegrable _ _
  have hsplit : (∫ t in (-1 : ℝ)..1, Bt t * (A (y * t) + B (y * t))) =
      (∫ t in (-1 : ℝ)..1, Bt t * A (y * t)) +
        (∫ t in (-1 : ℝ)..1, Bt t * B (y * t)) := by
    rw [← intervalIntegral.integral_add hiA hiB]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hsplit]
  ring

/-- Subtractive linearity of `lightConeTransmute` on continuous waves. -/
theorem lightConeTransmute_sub {A B : ℝ → ℝ} (hA : Continuous A) (hB : Continuous B) (y : ℝ) :
    lightConeTransmute (fun v => A v - B v) y =
      lightConeTransmute A y - lightConeTransmute B y := by
  unfold lightConeTransmute
  set Bt : ℝ → ℝ := fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2))
  have hBc : Continuous Bt := continuous_lightConeBesselReal.comp (by fun_prop)
  have hiA : IntervalIntegrable (fun t => Bt t * A (y * t)) volume (-1) 1 :=
    (hBc.mul (hA.comp (by fun_prop))).intervalIntegrable _ _
  have hiB : IntervalIntegrable (fun t => Bt t * B (y * t)) volume (-1) 1 :=
    (hBc.mul (hB.comp (by fun_prop))).intervalIntegrable _ _
  have hsplit : (∫ t in (-1 : ℝ)..1, Bt t * (A (y * t) - B (y * t))) =
      (∫ t in (-1 : ℝ)..1, Bt t * A (y * t)) -
        (∫ t in (-1 : ℝ)..1, Bt t * B (y * t)) := by
    rw [← intervalIntegral.integral_sub hiA hiB]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hsplit]
  ring

/-- The total massless d'Alembert source wave
`(2/cos²(1/4)) cosh(v/2) + (1/2π) masslessArchWave v - masslessPrimeWave v`. -/
def masslessSourceWave (v : ℝ) : ℝ :=
  2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (v / 2) +
    1 / (2 * π) * masslessArchWave v - masslessPrimeWave v

theorem continuous_masslessSourceWave : Continuous masslessSourceWave := by
  unfold masslessSourceWave
  exact ((by fun_prop : Continuous fun v : ℝ =>
    2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (v / 2)).add
    (continuous_const.mul continuous_masslessArchWave)).sub continuous_masslessPrimeWave

/-- **Forward Light-Cone Linearity Identity for the Causal Wave**:
`chmdWave y = L[(2/cos²(1/4)) cosh(·/2) + (1/2π) masslessArchWave - masslessPrimeWave](y)`. -/
theorem chmdWave_eq_lightConeTransmute (y : ℝ) :
    chmdWave y = lightConeTransmute
      (fun v => 2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (v / 2) +
        1 / (2 * π) * masslessArchWave v - masslessPrimeWave v) y := by
  have hpole : Continuous (fun v : ℝ => 2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (v / 2)) := by
    fun_prop
  have harch : Continuous (fun v : ℝ => 1 / (2 * π) * masslessArchWave v) :=
    continuous_const.mul continuous_masslessArchWave
  rw [lightConeTransmute_sub (hpole.add harch) continuous_masslessPrimeWave,
    lightConeTransmute_add hpole harch,
    lightConeTransmute_const_mul (1 / (2 * π)) masslessArchWave,
    ← chmdPoleWave_eq_lightConeTransmute,
    ← chmdArchWave_eq_lightConeTransmute,
    ← chmdPrimeWave_eq_lightConeTransmute,
    chmdWave_eq_pole_add_arch_sub_prime]

/-- `chmdWave` is the forward light-cone transmutation of `masslessSourceWave`. -/
theorem chmdWave_eq_lightConeTransmute_masslessSourceWave (y : ℝ) :
    chmdWave y = lightConeTransmute masslessSourceWave y :=
  chmdWave_eq_lightConeTransmute y

/-- **Pole–Prime Light-Cone Difference Identity**:
`chmdPoleWave y - chmdPrimeWave y = L[(2/cos²(1/4)) cosh(·/2) - masslessPrimeWave](y)`. -/
theorem chmdPoleWave_sub_chmdPrimeWave_eq_lightConeTransmute (y : ℝ) :
    chmdPoleWave y - chmdPrimeWave y = lightConeTransmute
      (fun v => 2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (v / 2) - masslessPrimeWave v) y := by
  have hpole : Continuous (fun v : ℝ => 2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (v / 2)) := by
    fun_prop
  rw [lightConeTransmute_sub hpole continuous_masslessPrimeWave,
    ← chmdPoleWave_eq_lightConeTransmute, ← chmdPrimeWave_eq_lightConeTransmute]

/-! ## Section 2: The Order-Zero Bessel Kernel `lightConeBesselZero` and Exact Derivative Laws -/

/-- The `k`-th term `(-w/4)^k / (k! * k!)` of the order-zero light-cone Bessel series. -/
def lightConeBesselZeroTerm (w : ℂ) (k : ℕ) : ℂ :=
  (-w / 4) ^ k / ((k ! : ℂ) * (k ! : ℂ))

/-- The order-zero light-cone Bessel kernel `B₀(w) = Σ_k (-w/4)^k / (k!)²`,
satisfying `B₀(x²) = J₀(x)` and `B₀'(w) = -(1/4) B(w)`. -/
def lightConeBesselZero (w : ℂ) : ℂ := ∑' k : ℕ, lightConeBesselZeroTerm w k

/-- The real order-zero light-cone Bessel kernel `B₀(x) = Re(lightConeBesselZero x)`. -/
def lightConeBesselZeroReal (x : ℝ) : ℝ := (lightConeBesselZero x).re

theorem norm_lightConeBesselZeroTerm_le (w : ℂ) (k : ℕ) :
    ‖lightConeBesselZeroTerm w k‖ ≤ (‖w‖ / 4) ^ k / k ! := by
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hk1 : (1 : ℝ) ≤ k ! := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos k)
  unfold lightConeBesselZeroTerm
  rw [norm_div, norm_pow, norm_div, norm_neg, norm_mul, Complex.norm_natCast, Complex.norm_natCast,
    show ‖(4 : ℂ)‖ = 4 by norm_num]
  exact div_le_div_of_nonneg_left (by positivity) hk (le_mul_of_one_le_right hk.le hk1)

theorem summable_norm_lightConeBesselZeroTerm (w : ℂ) :
    Summable fun k => ‖lightConeBesselZeroTerm w k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_lightConeBesselZeroTerm_le w)
    (Real.summable_pow_div_factorial _)

theorem hasSum_lightConeBesselZero (w : ℂ) :
    HasSum (lightConeBesselZeroTerm w) (lightConeBesselZero w) :=
  (summable_norm_lightConeBesselZeroTerm w).of_norm.hasSum

theorem norm_lightConeBesselZero_le (w : ℂ) :
    ‖lightConeBesselZero w‖ ≤ Real.exp (‖w‖ / 4) :=
  tsum_of_norm_bounded (hasSum_real_exp_series (‖w‖ / 4)) (norm_lightConeBesselZeroTerm_le w)

theorem lightConeBesselZero_zero : lightConeBesselZero 0 = 1 := by
  rw [lightConeBesselZero, tsum_eq_single 0 fun k hk => by
    simp [lightConeBesselZeroTerm, zero_pow hk]]
  simp [lightConeBesselZeroTerm]

theorem lightConeBesselZero_eq_one_add_tsum_succ (w : ℂ) :
    lightConeBesselZero w = 1 + ∑' k : ℕ, lightConeBesselZeroTerm w (k + 1) := by
  rw [lightConeBesselZero, (summable_norm_lightConeBesselZeroTerm w).of_norm.tsum_eq_zero_add]
  congr 1
  simp [lightConeBesselZeroTerm]

theorem lightConeBesselZero_ofReal_im (x : ℝ) : (lightConeBesselZero x).im = 0 := by
  rw [lightConeBesselZero, Complex.im_tsum (summable_norm_lightConeBesselZeroTerm _).of_norm]
  refine (tsum_congr fun k => ?_).trans tsum_zero
  unfold lightConeBesselZeroTerm
  rw [show (-(x : ℂ) / 4) ^ k / ((k ! : ℂ) * (k ! : ℂ)) =
      (((-x / 4) ^ k / ((k ! : ℝ) * (k ! : ℝ)) : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_im]

theorem ofReal_lightConeBesselZeroReal (x : ℝ) :
    (lightConeBesselZeroReal x : ℂ) = lightConeBesselZero x :=
  Complex.ext (by simp [lightConeBesselZeroReal]) (by simp [lightConeBesselZero_ofReal_im])

theorem lightConeBesselZeroReal_zero : lightConeBesselZeroReal 0 = 1 := by
  simp [lightConeBesselZeroReal, lightConeBesselZero_zero]

theorem abs_lightConeBesselZeroReal_le (x : ℝ) :
    |lightConeBesselZeroReal x| ≤ Real.exp (|x| / 4) := by
  have h := norm_lightConeBesselZero_le (x : ℂ)
  rw [← ofReal_lightConeBesselZeroReal, Complex.norm_real, Complex.norm_real] at h
  exact h

/-- **`J₀(x) = B₀(x²)`** on the complex plane for real `x`. -/
theorem besselJ_zero_eq (x : ℝ) :
    (besselJ 0 x : ℂ) = lightConeBesselZero ((x : ℂ) ^ 2) := by
  rw [besselJ_eq_mul_tsum, pow_zero, one_mul, Complex.ofReal_tsum, lightConeBesselZero]
  refine tsum_congr fun j => ?_
  unfold lightConeBesselZeroTerm
  rw [Nat.add_zero]
  push_cast
  rw [show -(x : ℂ) ^ 2 / 4 = (-1) * ((x : ℂ) / 2) ^ 2 by ring, mul_pow, ← pow_mul]

/-- **`J₀(x) = lightConeBesselZeroReal (x²)`** on the real line. -/
theorem besselJ_zero_eq_lightConeBesselZeroReal (x : ℝ) :
    besselJ 0 x = lightConeBesselZeroReal (x ^ 2) := by
  have h := congr_arg Complex.re (besselJ_zero_eq x)
  simpa [lightConeBesselZeroReal, ← Complex.ofReal_pow] using h

/-- For `w ≥ 0`, `lightConeBesselZeroReal w = J₀(√w)`. -/
theorem lightConeBesselZeroReal_eq_besselJ_zero_sqrt {w : ℝ} (hw : 0 ≤ w) :
    lightConeBesselZeroReal w = besselJ 0 (Real.sqrt w) := by
  rw [besselJ_zero_eq_lightConeBesselZeroReal, Real.sq_sqrt hw]

/-- For `w ≥ 0`, `lightConeBesselZero w = J₀(√w)`. -/
theorem lightConeBesselZero_ofReal_eq_besselJ_zero_sqrt {w : ℝ} (hw : 0 ≤ w) :
    lightConeBesselZero w = besselJ 0 (Real.sqrt w) := by
  rw [← ofReal_lightConeBesselZeroReal, lightConeBesselZeroReal_eq_besselJ_zero_sqrt hw]

/-- Term-by-term derivative of `lightConeBesselZeroTerm z (k + 1)`:
`(d/dz)[(-z/4)^{k+1} / ((k+1)!)²] = -(1/4) (-z/4)^k / (k! (k+1)!)`. -/
theorem hasDerivAt_lightConeBesselZeroTerm_succ (w : ℂ) (k : ℕ) :
    HasDerivAt (fun z => lightConeBesselZeroTerm z (k + 1))
      (-1 / 4 * lightConeBesselTerm w k) w := by
  unfold lightConeBesselZeroTerm
  have hd : HasDerivAt (fun z : ℂ => (-z / 4) ^ (k + 1) / (((k + 1)! : ℂ) * ((k + 1)! : ℂ)))
      (((k + 1 : ℕ) * (-w / 4) ^ (k + 1 - 1) * (-1 / 4)) /
        (((k + 1)! : ℂ) * ((k + 1)! : ℂ))) w := by
    refine (((((hasDerivAt_id w).neg).div_const (4 : ℂ)).pow (k + 1)).div_const
      (((k + 1)! : ℂ) * ((k + 1)! : ℂ))).congr_deriv ?_
    ring
  refine hd.congr_deriv ?_
  unfold lightConeBesselTerm
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast
  field_simp
  ring

/-- **Exact complex derivative law**: `(d/dw) lightConeBesselZero(w) = -(1/4) lightConeBessel(w)`. -/
theorem hasDerivAt_lightConeBesselZero (w₀ : ℂ) :
    HasDerivAt lightConeBesselZero (-1 / 4 * lightConeBessel w₀) w₀ := by
  set R : ℝ := ‖w₀‖ + 1
  have hR : 0 < R := by positivity
  have ht_open : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have ht_conn : IsPreconnected (Metric.ball (0 : ℂ) R) :=
    (convex_ball (0 : ℂ) R).isPreconnected
  have hu : Summable (fun k : ℕ => (1 / 4 : ℝ) * ((R / 4) ^ k / (k ! : ℝ))) :=
    (Real.summable_pow_div_factorial (R / 4)).mul_left (1 / 4)
  have hg0 : Summable (fun k : ℕ => lightConeBesselZeroTerm 0 (k + 1)) :=
    ((summable_norm_lightConeBesselZeroTerm 0).of_norm).comp_injective (add_left_injective 1)
  have hd := hasDerivAt_tsum_of_isPreconnected hu ht_open ht_conn
    (fun k z _ => hasDerivAt_lightConeBesselZeroTerm_succ z k)
    (fun k z hz => by
      rw [norm_mul, show ‖(-1 / 4 : ℂ)‖ = 1 / 4 by norm_num]
      refine mul_le_mul_of_nonneg_left ((norm_lightConeBesselTerm_le z k).trans ?_) (by positivity)
      have hzw : ‖z‖ ≤ R := by simpa using (Metric.mem_ball.mp hz).le
      gcongr)
    (by simp [R]; positivity : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R)
    hg0
    (by simp [R] : w₀ ∈ Metric.ball (0 : ℂ) R)
  have hd1 := hd.const_add (1 : ℂ)
  have hfun : (fun z : ℂ => (1 : ℂ) + ∑' k : ℕ, lightConeBesselZeroTerm z (k + 1)) =
      lightConeBesselZero :=
    funext fun z => (lightConeBesselZero_eq_one_add_tsum_succ z).symm
  rw [hfun, tsum_mul_left] at hd1
  exact hd1

theorem differentiable_lightConeBesselZero : Differentiable ℂ lightConeBesselZero :=
  fun w => (hasDerivAt_lightConeBesselZero w).differentiableAt

/-- **Exact real derivative law**:
`(d/dx) lightConeBesselZeroReal(x) = -(1/4) lightConeBesselReal(x)`. -/
theorem hasDerivAt_lightConeBesselZeroReal (x : ℝ) :
    HasDerivAt lightConeBesselZeroReal (-1 / 4 * lightConeBesselReal x) x := by
  have hc : HasDerivAt (fun y : ℝ => lightConeBesselZero (y : ℂ))
      (-1 / 4 * lightConeBessel (x : ℂ)) x := by
    simpa using HasDerivAt.scomp x (hasDerivAt_lightConeBesselZero (x : ℂ))
      Complex.ofRealCLM.hasDerivAt
  have hre := Complex.reCLM.hasDerivAt.comp x hc
  refine hre.congr_deriv ?_
  rw [← ofReal_lightConeBesselReal]
  simp [Complex.reCLM_apply]

theorem continuous_lightConeBesselZeroReal : Continuous lightConeBesselZeroReal :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_lightConeBesselZeroReal x).continuousAt

/-- **Exact Bessel Derivative Law on the Light Cone (`HasDerivAt`, real form)**:
`(d/dt)[lightConeBesselZeroReal(c y² (1 - t²))] = (c y² t / 2) lightConeBesselReal(c y² (1 - t²))`. -/
theorem hasDerivAt_lightConeBesselZeroReal_light_cone (c y t : ℝ) :
    HasDerivAt (fun s : ℝ => lightConeBesselZeroReal (c * y ^ 2 * (1 - s ^ 2)))
      (c * y ^ 2 * t / 2 * lightConeBesselReal (c * y ^ 2 * (1 - t ^ 2))) t := by
  have hinner : HasDerivAt (fun s : ℝ => c * y ^ 2 * (1 - s ^ 2)) (-2 * c * y ^ 2 * t) t := by
    have h1 : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (0 - (2 : ℕ) * t ^ (2 - 1)) t :=
      (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_pow 2 t)
    refine (h1.const_mul (c * y ^ 2)).congr_deriv ?_
    ring
  refine ((hasDerivAt_lightConeBesselZeroReal
    (c * y ^ 2 * (1 - t ^ 2))).comp t hinner).congr_deriv ?_
  ring

/-- **Exact Bessel Derivative Law on the Light Cone (`deriv`, real form)**:
`deriv (fun t => lightConeBesselZeroReal (c y² (1 - t²))) t = (c y² t / 2) lightConeBesselReal (c y² (1 - t²))`. -/
theorem deriv_lightConeBesselZeroReal_light_cone (c y t : ℝ) :
    deriv (fun s : ℝ => lightConeBesselZeroReal (c * y ^ 2 * (1 - s ^ 2))) t =
      c * y ^ 2 * t / 2 * lightConeBesselReal (c * y ^ 2 * (1 - t ^ 2)) :=
  (hasDerivAt_lightConeBesselZeroReal_light_cone c y t).deriv

/-- **Exact Bessel Derivative Law on the Light Cone (`HasDerivAt`, complex `lightConeBesselZero` form)**:
`(d/dt)[lightConeBesselZero(c y² (1 - t²))] = (c y² t / 2) lightConeBesselReal(c y² (1 - t²))`. -/
theorem hasDerivAt_lightConeBesselZero_light_cone (c y t : ℝ) :
    HasDerivAt (fun s : ℝ => lightConeBesselZero ((c * y ^ 2 * (1 - s ^ 2) : ℝ) : ℂ))
      (((c * y ^ 2 * t / 2 * lightConeBesselReal (c * y ^ 2 * (1 - t ^ 2)) : ℝ) : ℂ)) t := by
  have hfun : (fun s : ℝ => lightConeBesselZero ((c * y ^ 2 * (1 - s ^ 2) : ℝ) : ℂ)) =
      fun s : ℝ => ((lightConeBesselZeroReal (c * y ^ 2 * (1 - s ^ 2)) : ℝ) : ℂ) :=
    funext fun s => (ofReal_lightConeBesselZeroReal _).symm
  rw [hfun]
  exact Complex.ofRealCLM.hasDerivAt.comp t (hasDerivAt_lightConeBesselZeroReal_light_cone c y t)

/-- **Exact Bessel Derivative Law on the Light Cone (`deriv`, complex `lightConeBesselZero` form)**. -/
theorem deriv_lightConeBesselZero_light_cone (c y t : ℝ) :
    deriv (fun s : ℝ => lightConeBesselZero ((c * y ^ 2 * (1 - s ^ 2) : ℝ) : ℂ)) t =
      ((c * y ^ 2 * t / 2 * lightConeBesselReal (c * y ^ 2 * (1 - t ^ 2)) : ℝ) : ℂ) :=
  (hasDerivAt_lightConeBesselZero_light_cone c y t).deriv

/-- Specialization of the Bessel derivative law to the CHMD Klein–Gordon mass `c = 2`:
`(d/dt)[lightConeBesselZeroReal(2 y² (1 - t²))] = y² t lightConeBesselReal(2 y² (1 - t²))`. -/
theorem hasDerivAt_lightConeBesselZeroReal_two (y t : ℝ) :
    HasDerivAt (fun s : ℝ => lightConeBesselZeroReal (2 * y ^ 2 * (1 - s ^ 2)))
      (y ^ 2 * t * lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2))) t := by
  refine (hasDerivAt_lightConeBesselZeroReal_light_cone 2 y t).congr_deriv ?_
  ring

/-- `J₀'(x) = -J₁(x)` for all `x : ℝ`. -/
theorem hasDerivAt_besselJ_zero (x : ℝ) :
    HasDerivAt (besselJ 0) (-besselJ 1 x) x := by
  have hfun : besselJ 0 = fun u : ℝ => lightConeBesselZeroReal (u ^ 2) :=
    funext besselJ_zero_eq_lightConeBesselZeroReal
  have h1 : besselJ 1 x = x / 2 * lightConeBesselReal (x ^ 2) := by
    have hc := congr_arg Complex.re (besselJ_one_eq x)
    simpa [← ofReal_lightConeBesselReal, ← Complex.ofReal_pow] using hc
  rw [hfun, h1]
  have hd := (hasDerivAt_lightConeBesselZeroReal (x ^ 2)).comp x (hasDerivAt_pow 2 x)
  refine hd.congr_deriv ?_
  ring

theorem besselJ_zero_zero : besselJ 0 0 = 1 := by
  rw [besselJ_zero_eq_lightConeBesselZeroReal, sq, mul_zero, lightConeBesselZeroReal_zero]

/-- **Bessel's Integral for `J₀`**:
`J₀(x) = (2/π) ∫_0^{π/2} cos(x sin θ) dθ`. -/
theorem besselJ_zero_eq_integral (x : ℝ) :
    besselJ 0 x = 2 / Real.pi * ∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos (x * Real.sin θ) := by
  have hJ1_cont : Continuous (besselJ 1) := by
    have hfun : besselJ 1 = fun u : ℝ => u / 2 * lightConeBesselReal (u ^ 2) := by
      funext u
      have hc := congr_arg Complex.re (besselJ_one_eq u)
      simpa [← ofReal_lightConeBesselReal, ← Complex.ofReal_pow] using hc
    rw [hfun]
    exact (by fun_prop : Continuous fun u : ℝ => u / 2).mul
      (continuous_lightConeBesselReal.comp (by fun_prop))
  have hftc_J : ∫ u in (0 : ℝ)..x, (-besselJ 1 u) = besselJ 0 x - 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_besselJ_zero u)
      (hJ1_cont.neg.intervalIntegrable _ _), besselJ_zero_zero]
  have hJ1_int : ∀ u : ℝ, -besselJ 1 u =
      2 / Real.pi * ∫ θ in (0 : ℝ)..Real.pi / 2, (-Real.sin θ * Real.sin (u * Real.sin θ)) := by
    intro u
    have h := besselJ_odd_eq_integral 0 u
    simp only [mul_zero, zero_add, Nat.cast_one, one_mul] at h
    rw [h, ← neg_mul_eq_mul_neg, ← intervalIntegral.integral_neg]
    ring_nf
  have hF_cont : Continuous (fun p : ℝ × ℝ => -Real.sin p.2 * Real.sin (p.1 * Real.sin p.2)) := by
    fun_prop
  have hswap : (∫ u in (0 : ℝ)..x, ∫ θ in (0 : ℝ)..Real.pi / 2,
      (-Real.sin θ * Real.sin (u * Real.sin θ))) =
      ∫ θ in (0 : ℝ)..Real.pi / 2, ∫ u in (0 : ℝ)..x,
        (-Real.sin θ * Real.sin (u * Real.sin θ)) := by
    apply intervalIntegral_intervalIntegral_swap
    exact hF_cont.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) |>.mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hinner : ∀ θ : ℝ, (∫ u in (0 : ℝ)..x, (-Real.sin θ * Real.sin (u * Real.sin θ))) =
      Real.cos (x * Real.sin θ) - 1 := by
    intro θ
    have hd : ∀ u : ℝ, HasDerivAt (fun v : ℝ => Real.cos (v * Real.sin θ))
        (-Real.sin θ * Real.sin (u * Real.sin θ)) u := by
      intro u
      refine (((hasDerivAt_id u).mul_const (Real.sin θ)).cos).congr_deriv ?_
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
      ((by fun_prop : Continuous fun u : ℝ =>
        -Real.sin θ * Real.sin (u * Real.sin θ)).intervalIntegrable _ _)]
    simp
  have hcalc : ∫ u in (0 : ℝ)..x, (-besselJ 1 u) =
      2 / Real.pi * (∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos (x * Real.sin θ)) - 1 := by
    simp_rw [hJ1_int]
    rw [intervalIntegral.integral_const_mul, hswap]
    simp_rw [hinner]
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun θ : ℝ => Real.cos (x * Real.sin θ)).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  linarith

/-- **Uniform bound `|J₀(x)| ≤ 1`** for all `x : ℝ`. -/
theorem abs_besselJ_zero_le_one (x : ℝ) : |besselJ 0 x| ≤ 1 := by
  rw [besselJ_zero_eq_integral, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := Real.pi / 2) (C := 1)
    (f := fun θ : ℝ => Real.cos (x * Real.sin θ))
    (fun θ _ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 2),
    one_mul] at hint
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc 2 / Real.pi * |∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos (x * Real.sin θ)|
      ≤ 2 / Real.pi * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = 1 := by field_simp

/-- **Uniform bound `|lightConeBesselZeroReal w| ≤ 1`** on the forward light cone `w ≥ 0`. -/
theorem abs_lightConeBesselZeroReal_le_one {w : ℝ} (hw : 0 ≤ w) :
    |lightConeBesselZeroReal w| ≤ 1 := by
  rw [lightConeBesselZeroReal_eq_besselJ_zero_sqrt hw]
  exact abs_besselJ_zero_le_one (Real.sqrt w)

/-- **Uniform bound `|lightConeBesselZeroReal(c y² (1 - t²))| ≤ 1`** inside the light cone
`|t| ≤ 1` for `c ≥ 0`. -/
theorem abs_lightConeBesselZeroReal_light_cone_le_one {c : ℝ} (hc : 0 ≤ c) (y : ℝ) {t : ℝ}
    (ht : |t| ≤ 1) :
    |lightConeBesselZeroReal (c * y ^ 2 * (1 - t ^ 2))| ≤ 1 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  exact abs_lightConeBesselZeroReal_le_one (by nlinarith [sq_nonneg y])

/-! ## Section 3: Integration by Parts of `lightConeTransmute` and Cumulative Prime-Wave Identities -/

/-- For an even continuous wave `A`, `lightConeTransmute` folds onto `[0, 1]`:
`L[A](y) = A(y) - y² ∫_0^1 lightConeBesselReal(2 y² (1 - t²)) A(y t) dt`. -/
theorem lightConeTransmute_eq_of_even {A : ℝ → ℝ} (hA_cont : Continuous A)
    (hA_even : ∀ v : ℝ, A (-v) = A v) (y : ℝ) :
    lightConeTransmute A y =
      A y - y ^ 2 * ∫ t in (0 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * A (y * t) := by
  unfold lightConeTransmute
  set f : ℝ → ℝ := fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * A (y * t)
  have hf_cont : Continuous f :=
    (continuous_lightConeBesselReal.comp (by fun_prop)).mul (hA_cont.comp (by fun_prop))
  have hsplit : ∫ t in (-1 : ℝ)..1, f t = (∫ t in (-1 : ℝ)..0, f t) + ∫ t in (0 : ℝ)..1, f t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (-1) 0) (hf_cont.intervalIntegrable 0 1)).symm
  have hneg : ∫ t in (-1 : ℝ)..0, f t = ∫ t in (0 : ℝ)..1, f t := by
    have hc := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 0) f
    simp only [neg_neg, neg_zero] at hc
    rw [hc]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [f, neg_sq, mul_neg, hA_even]
  rw [hsplit, hneg]
  ring

/-- The massless d'Alembert prime wave `masslessPrimeWave` (`P₀`) is even. -/
theorem masslessPrimeWave_neg (v : ℝ) : masslessPrimeWave (-v) = masslessPrimeWave v := by
  unfold masslessPrimeWave
  refine tsum_congr fun n => ?_
  rw [← sub_eq_add_neg, sub_neg_eq_add, add_comm (dAlembertReal (Real.log n - v))]

/-- Half-interval light-cone decomposition of `chmdPrimeWave`:
`chmdPrimeWave y = P₀(y) - y² ∫_0^1 B(2 y² (1 - t²)) P₀(y t) dt`. -/
theorem chmdPrimeWave_eq_half_lightCone (y : ℝ) :
    chmdPrimeWave y = masslessPrimeWave y -
      y ^ 2 * ∫ t in (0 : ℝ)..1,
        lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * masslessPrimeWave (y * t) := by
  rw [chmdPrimeWave_eq_lightConeTransmute,
    lightConeTransmute_eq_of_even continuous_masslessPrimeWave masslessPrimeWave_neg]

/-- The **cumulative d'Alembert prime wave** `S₀(x) = ∫_0^x P₀(s) ds`. -/
def cumulativeMasslessPrimeWave (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..x, masslessPrimeWave s

theorem cumulativeMasslessPrimeWave_zero : cumulativeMasslessPrimeWave 0 = 0 := by
  simp [cumulativeMasslessPrimeWave]

theorem hasDerivAt_cumulativeMasslessPrimeWave (x : ℝ) :
    HasDerivAt cumulativeMasslessPrimeWave (masslessPrimeWave x) x :=
  intervalIntegral.integral_hasDerivAt_right (continuous_masslessPrimeWave.intervalIntegrable 0 x)
    (continuous_masslessPrimeWave.stronglyMeasurableAtFilter volume (nhds x))
    continuous_masslessPrimeWave.continuousAt

theorem continuous_cumulativeMasslessPrimeWave : Continuous cumulativeMasslessPrimeWave :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_cumulativeMasslessPrimeWave x).continuousAt

/-- Chain-rule derivative of `t ↦ ∫_0^{y t} P₀(s) ds`:
`(d/dt)[cumulativeMasslessPrimeWave(y t)] = y * masslessPrimeWave(y t)`. -/
theorem hasDerivAt_cumulativeMasslessPrimeWave_mul (y t : ℝ) :
    HasDerivAt (fun s : ℝ => cumulativeMasslessPrimeWave (y * s))
      (y * masslessPrimeWave (y * t)) t := by
  have hd := (hasDerivAt_cumulativeMasslessPrimeWave (y * t)).comp t
    (((hasDerivAt_id t).const_mul y).congr_deriv (by ring))
  refine hd.congr_deriv ?_
  ring

/-- Change-of-variables relation between `cumulativeMasslessPrimeWave (y * t) = ∫_0^{y t} P₀(s) ds`
and the normalized cumulative integral `∫_0^t P₀(y u) du`. -/
theorem cumulativeMasslessPrimeWave_mul_eq (y t : ℝ) :
    cumulativeMasslessPrimeWave (y * t) =
      y * ∫ u in (0 : ℝ)..t, masslessPrimeWave (y * u) := by
  unfold cumulativeMasslessPrimeWave
  by_cases hy : y = 0
  · subst hy; simp
  · have hc := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := t)
      masslessPrimeWave hy
    simp only [mul_zero, smul_eq_mul] at hc
    rw [← hc]
    field_simp

/-- Strict positivity of the cumulative d'Alembert prime wave for `x > 0`. -/
theorem cumulativeMasslessPrimeWave_pos {x : ℝ} (hx : 0 < x) :
    0 < cumulativeMasslessPrimeWave x := by
  unfold cumulativeMasslessPrimeWave
  exact intervalIntegral.integral_pos hx continuous_masslessPrimeWave.continuousOn
    (fun s _ => (masslessPrimeWave_pos s).le) (masslessPrimeWave_pos x)

theorem cumulativeMasslessPrimeWave_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ cumulativeMasslessPrimeWave x := by
  rcases hx.eq_or_lt with rfl | hpos
  · simp [cumulativeMasslessPrimeWave_zero]
  · exact (cumulativeMasslessPrimeWave_pos hpos).le

/-- **General Integration-by-Parts Identity for the Light-Cone Bessel Hierarchy**:
for any `C¹` function `G` on `[0, 1]`,
`∫_0^1 lightConeBesselZeroReal(c y² (1 - t²)) G'(t) dt = G(1) - lightConeBesselZeroReal(c y²) G(0) - (c y² / 2) ∫_0^1 t lightConeBesselReal(c y² (1 - t²)) G(t) dt`. -/
theorem integral_lightConeBesselZeroReal_mul_deriv_eq (c y : ℝ) {G G' : ℝ → ℝ}
    (hG : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt G (G' t) t)
    (hG' : Continuous G') :
    ∫ t in (0 : ℝ)..1, lightConeBesselZeroReal (c * y ^ 2 * (1 - t ^ 2)) * G' t =
      G 1 - lightConeBesselZeroReal (c * y ^ 2) * G 0 -
        c * y ^ 2 / 2 * ∫ t in (0 : ℝ)..1,
          t * lightConeBesselReal (c * y ^ 2 * (1 - t ^ 2)) * G t := by
  set u : ℝ → ℝ := fun t => lightConeBesselZeroReal (c * y ^ 2 * (1 - t ^ 2))
  set u' : ℝ → ℝ := fun t => c * y ^ 2 * t / 2 * lightConeBesselReal (c * y ^ 2 * (1 - t ^ 2))
  have hu' : Continuous u' :=
    (by fun_prop : Continuous fun t : ℝ => c * y ^ 2 * t / 2).mul
      (continuous_lightConeBesselReal.comp (by fun_prop))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1) (u := u) (u' := u') (v := G) (v' := G')
    (fun t _ => hasDerivAt_lightConeBesselZeroReal_light_cone c y t)
    hG
    (hu'.intervalIntegrable 0 1)
    (hG'.intervalIntegrable 0 1)
  have hu1 : u 1 = 1 := by simp [u, lightConeBesselZeroReal_zero]
  have hu0 : u 0 = lightConeBesselZeroReal (c * y ^ 2) := by simp [u]
  have hcongr : (∫ t in (0 : ℝ)..1, u' t * G t) =
      c * y ^ 2 / 2 * ∫ t in (0 : ℝ)..1,
        t * lightConeBesselReal (c * y ^ 2 * (1 - t ^ 2)) * G t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by simp only [u']; ring
  rw [hibp, hu1, hu0, one_mul, hcongr]

/-- **Integration-by-Parts Identity for the Cumulative D'Alembert Prime Wave and `lightConeBesselZeroReal`**:
`y ∫_0^1 lightConeBesselZeroReal(2 y² (1 - t²)) P₀(y t) dt = ∫_0^y P₀(s) ds - y² ∫_0^1 t lightConeBesselReal(2 y² (1 - t²)) (∫_0^{y t} P₀(s) ds) dt`. -/
theorem mul_integral_lightConeBesselZeroReal_masslessPrimeWave_eq (y : ℝ) :
    y * (∫ t in (0 : ℝ)..1,
        lightConeBesselZeroReal (2 * y ^ 2 * (1 - t ^ 2)) * masslessPrimeWave (y * t)) =
      cumulativeMasslessPrimeWave y -
        y ^ 2 * ∫ t in (0 : ℝ)..1,
          t * lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
            cumulativeMasslessPrimeWave (y * t) := by
  have hibp := integral_lightConeBesselZeroReal_mul_deriv_eq 2 y
    (G := fun t => cumulativeMasslessPrimeWave (y * t))
    (G' := fun t => y * masslessPrimeWave (y * t))
    (fun t _ => hasDerivAt_cumulativeMasslessPrimeWave_mul y t)
    (continuous_const.mul (continuous_masslessPrimeWave.comp (by fun_prop)))
  have hleft : (∫ t in (0 : ℝ)..1,
      lightConeBesselZeroReal (2 * y ^ 2 * (1 - t ^ 2)) * (y * masslessPrimeWave (y * t))) =
      y * ∫ t in (0 : ℝ)..1,
        lightConeBesselZeroReal (2 * y ^ 2 * (1 - t ^ 2)) * masslessPrimeWave (y * t) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hleft, mul_one, mul_zero, cumulativeMasslessPrimeWave_zero, mul_zero, sub_zero,
    show 2 * y ^ 2 / 2 = y ^ 2 by ring] at hibp
  exact hibp

/-- **Integration-by-Parts Identity for the Cumulative D'Alembert Prime Wave and `J₀`**:
`y ∫_0^1 J₀(√(2 y² (1 - t²))) P₀(y t) dt = ∫_0^y P₀(s) ds - y² ∫_0^1 t B(2 y² (1 - t²)) (∫_0^{y t} P₀(s) ds) dt`. -/
theorem mul_integral_besselJ_zero_masslessPrimeWave_eq (y : ℝ) :
    y * (∫ t in (0 : ℝ)..1,
        besselJ 0 (Real.sqrt (2 * y ^ 2 * (1 - t ^ 2))) * masslessPrimeWave (y * t)) =
      (∫ s in (0 : ℝ)..y, masslessPrimeWave s) -
        y ^ 2 * ∫ t in (0 : ℝ)..1,
          t * lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
            (∫ s in (0 : ℝ)..(y * t), masslessPrimeWave s) := by
  have hcongr : (∫ t in (0 : ℝ)..1,
      besselJ 0 (Real.sqrt (2 * y ^ 2 * (1 - t ^ 2))) * masslessPrimeWave (y * t)) =
      ∫ t in (0 : ℝ)..1,
        lightConeBesselZeroReal (2 * y ^ 2 * (1 - t ^ 2)) * masslessPrimeWave (y * t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    rw [lightConeBesselZeroReal_eq_besselJ_zero_sqrt (by nlinarith [sq_nonneg y])]
  rw [hcongr]
  exact mul_integral_lightConeBesselZeroReal_masslessPrimeWave_eq y

/-- Normalized integration-by-parts identity without the outer `y` factor (valid for all `y : ℝ`):
`∫_0^1 lightConeBesselZeroReal(2 y² (1 - t²)) P₀(y t) dt = ∫_0^1 P₀(y u) du - y² ∫_0^1 t B(2 y² (1 - t²)) (∫_0^t P₀(y u) du) dt`. -/
theorem integral_lightConeBesselZeroReal_masslessPrimeWave_eq (y : ℝ) :
    (∫ t in (0 : ℝ)..1,
        lightConeBesselZeroReal (2 * y ^ 2 * (1 - t ^ 2)) * masslessPrimeWave (y * t)) =
      (∫ u in (0 : ℝ)..1, masslessPrimeWave (y * u)) -
        y ^ 2 * ∫ t in (0 : ℝ)..1,
          t * lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
            (∫ u in (0 : ℝ)..t, masslessPrimeWave (y * u)) := by
  have hG : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ∫ u in (0 : ℝ)..s, masslessPrimeWave (y * u))
      (masslessPrimeWave (y * t)) t := by
    intro t
    have hc : Continuous (fun u : ℝ => masslessPrimeWave (y * u)) :=
      continuous_masslessPrimeWave.comp (by fun_prop)
    exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      (hc.stronglyMeasurableAtFilter volume (nhds t)) hc.continuousAt
  have hibp := integral_lightConeBesselZeroReal_mul_deriv_eq 2 y
    (G := fun s => ∫ u in (0 : ℝ)..s, masslessPrimeWave (y * u))
    (G' := fun s => masslessPrimeWave (y * s))
    (fun t _ => hG t)
    (continuous_masslessPrimeWave.comp (by fun_prop))
  simpa [show 2 * y ^ 2 / 2 = y ^ 2 by ring] using hibp

/-- **Expression of `chmdPrimeWave(y)` via Integration by Parts, `lightConeBesselZeroReal`, and the
Cumulative D'Alembert Prime Wave**:
`chmdPrimeWave y = P₀(y) - ∫_0^1 P₀(y u) du + ∫_0^1 lightConeBesselZeroReal(2 y² (1 - t²)) P₀(y t) dt - y² ∫_0^1 B(2 y² (1 - t²)) (P₀(y t) - t ∫_0^t P₀(y u) du) dt`. -/
theorem chmdPrimeWave_eq_lightConeBesselZeroReal_and_cumulative (y : ℝ) :
    chmdPrimeWave y =
      masslessPrimeWave y - (∫ u in (0 : ℝ)..1, masslessPrimeWave (y * u)) +
        (∫ t in (0 : ℝ)..1,
          lightConeBesselZeroReal (2 * y ^ 2 * (1 - t ^ 2)) * masslessPrimeWave (y * t)) -
        y ^ 2 * ∫ t in (0 : ℝ)..1,
          lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
            (masslessPrimeWave (y * t) - t * ∫ u in (0 : ℝ)..t, masslessPrimeWave (y * u)) := by
  have hB : Continuous (fun t : ℝ => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2))) :=
    continuous_lightConeBesselReal.comp (by fun_prop)
  have hP : Continuous (fun t : ℝ => masslessPrimeWave (y * t)) :=
    continuous_masslessPrimeWave.comp (by fun_prop)
  have hC : Continuous (fun t : ℝ => ∫ u in (0 : ℝ)..t, masslessPrimeWave (y * u)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact (intervalIntegral.integral_hasDerivAt_right (hP.intervalIntegrable 0 t)
      (hP.stronglyMeasurableAtFilter volume (nhds t)) hP.continuousAt).continuousAt
  have hsplit : (∫ t in (0 : ℝ)..1,
      lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        (masslessPrimeWave (y * t) - t * ∫ u in (0 : ℝ)..t, masslessPrimeWave (y * u))) =
      (∫ t in (0 : ℝ)..1,
        lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * masslessPrimeWave (y * t)) -
      (∫ t in (0 : ℝ)..1,
        t * lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
          (∫ u in (0 : ℝ)..t, masslessPrimeWave (y * u))) := by
    rw [← intervalIntegral.integral_sub
      ((hB.mul hP).intervalIntegrable 0 1)
      (((by fun_prop : Continuous fun t : ℝ => t).mul hB |>.mul hC).intervalIntegrable 0 1)]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hsplit, chmdPrimeWave_eq_half_lightCone, integral_lightConeBesselZeroReal_masslessPrimeWave_eq]
  ring

/-- **Expression of `y * chmdPrimeWave(y)` in Terms of the Cumulative D'Alembert Prime Wave
`∫_0^{y t} P₀(s) ds` and the Bounded Kernel `J₀`**:
`y * chmdPrimeWave y = y P₀(y) - ∫_0^y P₀(s) ds + y ∫_0^1 J₀(√(2 y² (1 - t²))) P₀(y t) dt - y² ∫_0^1 B(2 y² (1 - t²)) (y P₀(y t) - t ∫_0^{y t} P₀(s) ds) dt`. -/
theorem mul_chmdPrimeWave_eq_besselJ_zero_and_cumulative (y : ℝ) :
    y * chmdPrimeWave y =
      y * masslessPrimeWave y - (∫ s in (0 : ℝ)..y, masslessPrimeWave s) +
        y * (∫ t in (0 : ℝ)..1,
          besselJ 0 (Real.sqrt (2 * y ^ 2 * (1 - t ^ 2))) * masslessPrimeWave (y * t)) -
        y ^ 2 * ∫ t in (0 : ℝ)..1,
          lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
            (y * masslessPrimeWave (y * t) - t * ∫ s in (0 : ℝ)..(y * t), masslessPrimeWave s) := by
  have hB : Continuous (fun t : ℝ => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2))) :=
    continuous_lightConeBesselReal.comp (by fun_prop)
  have hP : Continuous (fun t : ℝ => masslessPrimeWave (y * t)) :=
    continuous_masslessPrimeWave.comp (by fun_prop)
  have hC : Continuous (fun t : ℝ => cumulativeMasslessPrimeWave (y * t)) :=
    continuous_cumulativeMasslessPrimeWave.comp (by fun_prop)
  have hsplit : (∫ t in (0 : ℝ)..1,
      lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        (y * masslessPrimeWave (y * t) - t * cumulativeMasslessPrimeWave (y * t))) =
      y * (∫ t in (0 : ℝ)..1,
        lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * masslessPrimeWave (y * t)) -
      (∫ t in (0 : ℝ)..1,
        t * lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
          cumulativeMasslessPrimeWave (y * t)) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub
        ((continuous_const.mul (hB.mul hP)).intervalIntegrable 0 1)
        (((by fun_prop : Continuous fun t : ℝ => t).mul hB |>.mul hC).intervalIntegrable 0 1)]
    exact intervalIntegral.integral_congr fun t _ => by ring
  change y * chmdPrimeWave y =
    y * masslessPrimeWave y - cumulativeMasslessPrimeWave y +
      y * (∫ t in (0 : ℝ)..1,
        besselJ 0 (Real.sqrt (2 * y ^ 2 * (1 - t ^ 2))) * masslessPrimeWave (y * t)) -
      y ^ 2 * ∫ t in (0 : ℝ)..1,
        lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
          (y * masslessPrimeWave (y * t) - t * cumulativeMasslessPrimeWave (y * t))
  rw [hsplit, chmdPrimeWave_eq_half_lightCone, mul_integral_besselJ_zero_masslessPrimeWave_eq]
  unfold cumulativeMasslessPrimeWave
  ring

/-- **Uniform Cumulative Bound on the `J₀` Light-Cone Prime Integral**:
because `|J₀(√(2 y² (1 - t²)))| ≤ 1` and `P₀ > 0`,
`|∫_0^1 lightConeBesselZeroReal(2 y² (1 - t²)) P₀(y t) dt| ≤ ∫_0^1 P₀(y t) dt`. -/
theorem abs_integral_lightConeBesselZeroReal_masslessPrimeWave_le (y : ℝ) :
    |∫ t in (0 : ℝ)..1,
        lightConeBesselZeroReal (2 * y ^ 2 * (1 - t ^ 2)) * masslessPrimeWave (y * t)| ≤
      ∫ t in (0 : ℝ)..1, masslessPrimeWave (y * t) := by
  have hB0 : Continuous (fun t : ℝ => lightConeBesselZeroReal (2 * y ^ 2 * (1 - t ^ 2))) :=
    continuous_lightConeBesselZeroReal.comp (by fun_prop)
  have hP : Continuous (fun t : ℝ => masslessPrimeWave (y * t)) :=
    continuous_masslessPrimeWave.comp (by fun_prop)
  rw [abs_le]
  constructor
  · rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_mono_on (by norm_num)
      (hP.neg.intervalIntegrable 0 1) ((hB0.mul hP).intervalIntegrable 0 1) fun t ht => ?_
    have hta : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hb := (abs_le.mp (abs_lightConeBesselZeroReal_light_cone_le_one (by norm_num) y hta)).1
    have hp := (masslessPrimeWave_pos (y * t)).le
    nlinarith
  · refine intervalIntegral.integral_mono_on (by norm_num)
      ((hB0.mul hP).intervalIntegrable 0 1) (hP.intervalIntegrable 0 1) fun t ht => ?_
    have hta : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hb := (abs_le.mp (abs_lightConeBesselZeroReal_light_cone_le_one (by norm_num) y hta)).2
    have hp := (masslessPrimeWave_pos (y * t)).le
    nlinarith

/-- **Nonnegativity and `2 ∫_0^y P₀(s) ds` Upper Bound for the `t`-Weighted Dispersive Bessel Tail
Against the Cumulative Prime Wave** (`y ≥ 0`):
integrating by parts into the bounded kernel `J₀` eliminates the `e^{y²/2}` Gaussian factor and
sandwiches the oscillatory Bessel tail between `0` and `2 ∫_0^y P₀(s) ds`. -/
theorem cumulative_bessel_tail_nonneg_and_le_two_mul {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ y ^ 2 * (∫ t in (0 : ℝ)..1,
        t * lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
          cumulativeMasslessPrimeWave (y * t)) ∧
      y ^ 2 * (∫ t in (0 : ℝ)..1,
        t * lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
          cumulativeMasslessPrimeWave (y * t)) ≤
        2 * cumulativeMasslessPrimeWave y := by
  have hibp := mul_integral_lightConeBesselZeroReal_masslessPrimeWave_eq y
  have habs := abs_integral_lightConeBesselZeroReal_masslessPrimeWave_le y
  have h1 := (abs_le.mp habs).1
  have h2 := (abs_le.mp habs).2
  have hcum : cumulativeMasslessPrimeWave y = y * ∫ t in (0 : ℝ)..1, masslessPrimeWave (y * t) := by
    simpa using cumulativeMasslessPrimeWave_mul_eq y 1
  have hm1 := mul_le_mul_of_nonneg_left h1 hy
  have hm2 := mul_le_mul_of_nonneg_left h2 hy
  rw [mul_neg, ← hcum] at hm1
  rw [← hcum] at hm2
  constructor <;> linarith

end RHTower.CHMDLightConeBesselZero

end
