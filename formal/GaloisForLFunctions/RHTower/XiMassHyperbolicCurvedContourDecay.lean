import GaloisForLFunctions.RHTower.XiMassHyperbolicFourierRepresentation
import GaloisForLFunctions.RHTower.XiMassBottomPrimeAtomization

/-!
# Exact curved-contour Fourier decay for the Xi mass carrier

The hyperbolic substitution from `XiMassHyperbolicFourierRepresentation` makes the mass Fourier
kernel entire.  This module proves a genuinely one-sided lower contour deformation, identifies its
terminal Lorentz rate

`q² = (sigma cos theta + h sin theta)² - (u sin theta)²`,

and bounds the transform by the exact order-one Schlaefli carrier `2 a exp(r) K₁(aq)`.  The final
comparison retains the full exponential coefficient:

`K₁(s) ≤ exp (-(s-s₀)) K₁(s₀)` for `0 < s₀ ≤ s`.

No asymptotic expansion, numerical certificate, or unproved contour identity is used.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

def xiMassHyperbolicEntireKernel
    (a sigma u h : ℝ) (z : ℂ) : ℂ :=
  (a : ℂ) * Complex.cosh z *
    Complex.exp (-((sigma : ℂ) + (u : ℂ) * I) *
      ((a : ℂ) * Complex.cosh z)) *
    Complex.exp (-(I * (h : ℂ) * (a : ℂ) * Complex.sinh z))

theorem xiMassHyperbolicEntireKernel_ofReal
    (a sigma u h t : ℝ) :
    xiMassHyperbolicEntireKernel a sigma u h (t : ℂ) =
      xiMassHyperbolicFourierKernel a sigma u h t := by
  rw [xiMassHyperbolicEntireKernel, xiMassHyperbolicFourierKernel,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  have hc : (a : ℂ) * (Real.cosh t : ℂ) =
      ((a * Real.cosh t : ℝ) : ℂ) := by push_cast; ring
  have hs : (a : ℂ) * (Real.sinh t : ℂ) =
      ((a * Real.sinh t : ℝ) : ℂ) := by push_cast; ring
  rw [hc]
  congr 2
  rw [← hs]
  ring

theorem differentiable_xiMassHyperbolicEntireKernel
    (a sigma u h : ℝ) :
    Differentiable ℂ (xiMassHyperbolicEntireKernel a sigma u h) := by
  unfold xiMassHyperbolicEntireKernel
  fun_prop

private theorem cosh_sub_mul_I_re (x v : ℝ) :
    (Complex.cosh ((x : ℂ) - (v : ℂ) * I)).re =
      Real.cosh x * Real.cos v := by
  rw [Complex.cosh_sub, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

private theorem cosh_sub_mul_I_im (x v : ℝ) :
    (Complex.cosh ((x : ℂ) - (v : ℂ) * I)).im =
      -(Real.sinh x * Real.sin v) := by
  rw [Complex.cosh_sub, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

private theorem sinh_sub_mul_I_re (x v : ℝ) :
    (Complex.sinh ((x : ℂ) - (v : ℂ) * I)).re =
      Real.sinh x * Real.cos v := by
  rw [Complex.sinh_sub, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

private theorem sinh_sub_mul_I_im (x v : ℝ) :
    (Complex.sinh ((x : ℂ) - (v : ℂ) * I)).im =
      -(Real.cosh x * Real.sin v) := by
  rw [Complex.sinh_sub, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

theorem norm_xiMassHyperbolicEntireKernel_shift
    {a sigma u h x v : ℝ} (ha : 0 < a) :
    ‖xiMassHyperbolicEntireKernel a sigma u h
        ((x : ℂ) - (v : ℂ) * I)‖ =
      a * ‖Complex.cosh ((x : ℂ) - (v : ℂ) * I)‖ *
        Real.exp (-a * ((sigma * Real.cos v + h * Real.sin v) * Real.cosh x +
          u * Real.sin v * Real.sinh x)) := by
  rw [xiMassHyperbolicEntireKernel, norm_mul, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
    Complex.norm_exp, Complex.norm_exp]
  have hfirst :
      (-((sigma : ℂ) + (u : ℂ) * I) *
        ((a : ℂ) * Complex.cosh ((x : ℂ) - (v : ℂ) * I))).re =
        -a * (sigma * Real.cos v * Real.cosh x +
          u * Real.sin v * Real.sinh x) := by
    simp [Complex.mul_re, Complex.mul_im, cosh_sub_mul_I_re,
      cosh_sub_mul_I_im]
    ring
  have hsecond :
      (-(I * (h : ℂ) * (a : ℂ) *
        Complex.sinh ((x : ℂ) - (v : ℂ) * I))).re =
        -a * (h * Real.sin v * Real.cosh x) := by
    simp [Complex.mul_re, Complex.mul_im, sinh_sub_mul_I_re,
      sinh_sub_mul_I_im]
    ring
  rw [hfirst, hsecond]
  calc
    a * ‖Complex.cosh ((x : ℂ) - (v : ℂ) * I)‖ *
          Real.exp (-a * (sigma * Real.cos v * Real.cosh x +
            u * Real.sin v * Real.sinh x)) *
          Real.exp (-a * (h * Real.sin v * Real.cosh x)) =
        a * ‖Complex.cosh ((x : ℂ) - (v : ℂ) * I)‖ *
          (Real.exp (-a * (sigma * Real.cos v * Real.cosh x +
            u * Real.sin v * Real.sinh x)) *
          Real.exp (-a * (h * Real.sin v * Real.cosh x))) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

theorem norm_cosh_sub_mul_I_le_cosh (x v : ℝ) :
    ‖Complex.cosh ((x : ℂ) - (v : ℂ) * I)‖ ≤ Real.cosh x := by
  rw [← sq_le_sq₀ (norm_nonneg _) (Real.cosh_pos x).le]
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, cosh_sub_mul_I_re, cosh_sub_mul_I_im]
  have htrig := Real.sin_sq_add_cos_sq v
  have hhyp := Real.cosh_sq_sub_sinh_sq x
  nlinarith [sq_nonneg (Real.sin v), sq_nonneg (Real.sinh x)]

theorem mul_exp_neg_mul_le_two_div_sq_mul_inv
    {K y : ℝ} (hK : 0 < K) (hy : 0 < y) :
    y * Real.exp (-(K * y)) ≤ (2 / K ^ (2 : ℕ)) * y⁻¹ := by
  have hKy : 0 ≤ K * y := (mul_pos hK hy).le
  have hseries := Real.pow_div_factorial_le_exp (K * y) hKy 2
  norm_num [Nat.factorial] at hseries
  have hmul := mul_le_mul_of_nonneg_right hseries (Real.exp_nonneg (-(K * y)))
  have hcancel : Real.exp (K * y) * Real.exp (-(K * y)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hcancel] at hmul
  have hden : 0 < K ^ (2 : ℕ) * y := mul_pos (sq_pos_of_pos hK) hy
  rw [show (2 / K ^ (2 : ℕ)) * y⁻¹ = 2 / (K ^ (2 : ℕ) * y) by field_simp]
  rw [le_div_iff₀ hden]
  calc
    y * Real.exp (-(K * y)) * (K ^ (2 : ℕ) * y) =
        2 * (((K * y) ^ (2 : ℕ) / 2) * Real.exp (-(K * y))) := by ring
    _ ≤ 2 * 1 := by gcongr
    _ = 2 := by ring

theorem linear_cosh_sinh_lower
    {A B m x : ℝ} (hB : 0 ≤ B) (hAB : m ≤ A - B) :
    m * Real.cosh x ≤ A * Real.cosh x + B * Real.sinh x := by
  have hA : m ≤ A := by linarith
  by_cases hx : 0 ≤ x
  · have hsinh : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx
    have hcosh : 0 ≤ Real.cosh x := (Real.cosh_pos x).le
    nlinarith [mul_nonneg hB hsinh,
      mul_le_mul_of_nonneg_right hA hcosh]
  · have hexp : 0 ≤ Real.cosh x + Real.sinh x := by
      rw [Real.cosh_add_sinh]
      exact (Real.exp_pos x).le
    have hcosh : 0 ≤ Real.cosh x := (Real.cosh_pos x).le
    have hmain := mul_le_mul_of_nonneg_right hAB hcosh
    have htail := mul_nonneg hB hexp
    nlinarith

theorem exp_abs_div_two_le_cosh_local (x : ℝ) :
    Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    nlinarith [Real.exp_pos (-x)]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    nlinarith [Real.exp_pos x]

theorem contour_phase_lower_exp_abs
    {A B m x : ℝ} (hm : 0 ≤ m) (hB : 0 ≤ B) (hAB : m ≤ A - B) :
    (m / 2) * Real.exp |x| ≤ A * Real.cosh x + B * Real.sinh x := by
  have hcosh := exp_abs_div_two_le_cosh_local x
  calc
    (m / 2) * Real.exp |x| = m * (Real.exp |x| / 2) := by ring
    _ ≤ m * Real.cosh x := mul_le_mul_of_nonneg_left hcosh hm
    _ ≤ _ := linear_cosh_sinh_lower hB hAB

theorem norm_xiMassHyperbolicEntireKernel_shift_le_exp_abs
    {a sigma u h theta x v : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u ≤ h)
    (htheta0 : 0 ≤ theta) (hthetaPi : theta < Real.pi / 2)
    (hv0 : 0 ≤ v) (hvtheta : v ≤ theta) :
    ‖RHTower.xiMassHyperbolicEntireKernel a sigma u h
        ((x : ℂ) - (v : ℂ) * I)‖ ≤
      (2 * a / (a * (sigma * Real.cos theta) / 2) ^ (2 : ℕ)) *
        Real.exp (-|x|) := by
  let m : ℝ := sigma * Real.cos theta
  let K : ℝ := a * m / 2
  have hthetaNeg : -(Real.pi / 2) < theta := by
    have hp : 0 < Real.pi / 2 := half_pos Real.pi_pos
    linarith
  have hcostheta : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨hthetaNeg, hthetaPi⟩
  have hm : 0 < m := mul_pos hsigma hcostheta
  have hK : 0 < K := div_pos (mul_pos ha hm) (by norm_num)
  have hthetaLePi : theta ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hvLePi : v ≤ Real.pi := hvtheta.trans hthetaLePi
  have hsinv : 0 ≤ Real.sin v :=
    Real.sin_nonneg_of_nonneg_of_le_pi hv0 hvLePi
  have hcos : Real.cos theta ≤ Real.cos v :=
    Real.cos_le_cos_of_nonneg_of_le_pi hv0 hthetaLePi hvtheta
  have hB : 0 ≤ u * Real.sin v := mul_nonneg hu hsinv
  have hAB : m ≤
      (sigma * Real.cos v + h * Real.sin v) - u * Real.sin v := by
    dsimp only [m]
    have hsigcos := mul_le_mul_of_nonneg_left hcos hsigma.le
    have htail : 0 ≤ (h - u) * Real.sin v :=
      mul_nonneg (sub_nonneg.mpr huh) hsinv
    nlinarith
  have hphase : (m / 2) * Real.exp |x| ≤
      (sigma * Real.cos v + h * Real.sin v) * Real.cosh x +
        u * Real.sin v * Real.sinh x :=
    contour_phase_lower_exp_abs hm.le hB hAB
  have hcosh := RHTower.norm_cosh_sub_mul_I_le_cosh x v
  have hcoshexp := GaloisForLFunctions.HTGeometry.cosh_le_exp_abs x
  rw [RHTower.norm_xiMassHyperbolicEntireKernel_shift ha]
  calc
    a * ‖Complex.cosh ((x : ℂ) - (v : ℂ) * I)‖ *
          Real.exp (-a * ((sigma * Real.cos v + h * Real.sin v) * Real.cosh x +
            u * Real.sin v * Real.sinh x)) ≤
        a * Real.exp |x| *
          Real.exp (-a * ((sigma * Real.cos v + h * Real.sin v) * Real.cosh x +
            u * Real.sin v * Real.sinh x)) := by gcongr; exact hcosh.trans hcoshexp
    _ ≤ a * Real.exp |x| * Real.exp (-(K * Real.exp |x|)) := by
      gcongr
      dsimp only [K]
      nlinarith
    _ = a * (Real.exp |x| * Real.exp (-(K * Real.exp |x|))) := by ring
    _ ≤ a * ((2 / K ^ (2 : ℕ)) * (Real.exp |x|)⁻¹) := by
      exact mul_le_mul_of_nonneg_left
        (mul_exp_neg_mul_le_two_div_sq_mul_inv hK (Real.exp_pos _)) ha.le
    _ = (2 * a / (a * (sigma * Real.cos theta) / 2) ^ (2 : ℕ)) *
        Real.exp (-|x|) := by
      rw [← Real.exp_neg]
      dsimp only [K, m]
      field_simp

theorem integral_xiMassHyperbolicEntireKernel_shift_eq
    {a sigma u h theta : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u ≤ h)
    (htheta0 : 0 ≤ theta) (hthetaPi : theta < Real.pi / 2) :
    (∫ x : ℝ, RHTower.xiMassHyperbolicEntireKernel a sigma u h
      ((x : ℂ) - (theta : ℂ) * I)) =
        ∫ x : ℝ, RHTower.xiMassHyperbolicEntireKernel a sigma u h (x : ℂ) := by
  let c : ℝ := theta / 2
  let C : ℝ := 2 * a / (a * (sigma * Real.cos theta) / 2) ^ (2 : ℕ)
  let F : ℂ → ℂ := RHTower.xiMassHyperbolicEntireKernel a sigma u h
  let G : ℂ → ℂ := fun z => F (z - (c : ℂ) * I)
  have hc : 0 ≤ c := by dsimp only [c]; linarith
  have hGdiff : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ G z := by
    intro z hz
    dsimp only [G, F]
    exact (RHTower.differentiable_xiMassHyperbolicEntireKernel a sigma u h).differentiableAt.comp
      z (by fun_prop)
  have hGbound : ∀ z : ℂ, |z.im| ≤ c →
      ‖G z‖ ≤ C * Real.exp (-(1 * |z.re|)) := by
    intro z hz
    have him : -c ≤ z.im ∧ z.im ≤ c := (abs_le.mp hz)
    have him' : -(theta / 2) ≤ z.im ∧ z.im ≤ theta / 2 := by
      simpa only [c] using him
    let v : ℝ := c - z.im
    have hv0 : 0 ≤ v := by dsimp only [v]; linarith
    have hvtheta : v ≤ theta := by dsimp only [v, c]; linarith [him'.1]
    have hz : z - (c : ℂ) * I =
        ((z.re : ℂ) - (v : ℂ) * I) := by
      apply Complex.ext <;> simp [v]
    change ‖F (z - (c : ℂ) * I)‖ ≤ C * Real.exp (-(1 * |z.re|))
    rw [hz]
    simpa only [F, C, one_mul] using
      (norm_xiMassHyperbolicEntireKernel_shift_le_exp_abs
        ha hsigma hu huh htheta0 hthetaPi hv0 hvtheta (x := z.re))
  have hneg := RHTower.integral_horizontal_shift_neg_of_decay
    (F := G) (c := c) (C := C) (r := 1) hc (by norm_num) hGdiff hGbound
  have hpos := RHTower.integral_horizontal_shift_of_decay
    (F := G) (c := c) (C := C) (r := 1) hc (by norm_num) hGdiff hGbound
  have hneg' :
      (∫ x : ℝ, F ((x : ℂ) - (theta : ℂ) * I)) =
        ∫ x : ℝ, F ((x : ℂ) - (c : ℂ) * I) := by
    calc
      (∫ x : ℝ, F ((x : ℂ) - (theta : ℂ) * I)) =
          ∫ x : ℝ, G ((x : ℂ) - (c : ℂ) * I) := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [G]
        congr 1
        dsimp only [c]
        norm_num
        ring
      _ = ∫ x : ℝ, G (x : ℂ) := hneg
      _ = ∫ x : ℝ, F ((x : ℂ) - (c : ℂ) * I) := by rfl
  have hpos' :
      (∫ x : ℝ, F (x : ℂ)) =
        ∫ x : ℝ, F ((x : ℂ) - (c : ℂ) * I) := by
    calc
      (∫ x : ℝ, F (x : ℂ)) =
          ∫ x : ℝ, G ((x : ℂ) + (c : ℂ) * I) := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [G]
        congr 1
        ring
      _ = ∫ x : ℝ, G (x : ℂ) := hpos
      _ = ∫ x : ℝ, F ((x : ℂ) - (c : ℂ) * I) := by rfl
  exact hneg'.trans hpos'.symm

theorem cosh_arsinh_div_sqrt_sq_sub_sq
    {A B : ℝ} (hB : 0 ≤ B) (hBA : B < A) :
    Real.cosh (Real.arsinh (B / Real.sqrt (A ^ (2 : ℕ) - B ^ (2 : ℕ)))) =
      A / Real.sqrt (A ^ (2 : ℕ) - B ^ (2 : ℕ)) := by
  have hD : 0 < A ^ (2 : ℕ) - B ^ (2 : ℕ) := by nlinarith
  have hq : 0 < Real.sqrt (A ^ (2 : ℕ) - B ^ (2 : ℕ)) := Real.sqrt_pos.2 hD
  have hA : 0 < A := lt_of_le_of_lt hB hBA
  rw [Real.cosh_arsinh]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg hA.le hq.le)).mp
  rw [Real.sq_sqrt (by positivity)]
  rw [div_pow]
  rw [Real.sq_sqrt hD.le]
  field_simp
  rw [Real.sq_sqrt hD.le]
  ring

theorem hyperbolic_boost_identity
    {A B x : ℝ} (hB : 0 ≤ B) (hBA : B < A) :
    let q := Real.sqrt (A ^ (2 : ℕ) - B ^ (2 : ℕ))
    let r := Real.arsinh (B / q)
    A * Real.cosh x + B * Real.sinh x = q * Real.cosh (x + r) := by
  dsimp only
  have hD : 0 < A ^ (2 : ℕ) - B ^ (2 : ℕ) := by nlinarith
  have hq : 0 < Real.sqrt (A ^ (2 : ℕ) - B ^ (2 : ℕ)) := Real.sqrt_pos.2 hD
  rw [Real.cosh_add, Real.sinh_arsinh,
    cosh_arsinh_div_sqrt_sq_sub_sq hB hBA]
  field_simp

theorem abs_sinh_le_cosh_local (x : ℝ) :
    |Real.sinh x| ≤ Real.cosh x := by
  rw [← sq_le_sq₀ (abs_nonneg _) (Real.cosh_pos x).le, sq_abs]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem cosh_sub_le_exp_mul_cosh {y r : ℝ} (hr : 0 ≤ r) :
    Real.cosh (y - r) ≤ Real.exp r * Real.cosh y := by
  rw [Real.cosh_sub, ← Real.cosh_add_sinh r]
  have hsinhR : 0 ≤ Real.sinh r := Real.sinh_nonneg_iff.mpr hr
  have hcoshY : 0 ≤ Real.cosh y := (Real.cosh_pos y).le
  have habs := abs_sinh_le_cosh_local y
  have hneg : -(Real.sinh y) ≤ |Real.sinh y| := neg_le_abs _
  have hmul := mul_le_mul_of_nonneg_right (hneg.trans habs) hsinhR
  nlinarith

theorem integrable_realBesselOrderKernel_one_full {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : ℝ => Real.exp (-s * Real.cosh x) * Real.cosh x) := by
  have hk := (RHTower.integrable_xiMassHyperbolicFourierKernel
    (a := 1) (sigma := s) (u := 0) (h := 0) (by norm_num) hs).norm
  exact hk.congr (ae_of_all _ fun x => by
    change ‖RHTower.xiMassHyperbolicFourierKernel 1 s 0 0 x‖ =
      Real.exp (-s * Real.cosh x) * Real.cosh x
    rw [RHTower.norm_xiMassHyperbolicFourierKernel (by norm_num : (0 : ℝ) < 1)]
    ring_nf)

theorem integral_realBesselOrderKernel_one_full_eq
    {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ, Real.exp (-s * Real.cosh x) * Real.cosh x) =
      2 * GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder s 1 := by
  let f : ℝ → ℝ := fun x => Real.exp (-s * Real.cosh x) * Real.cosh x
  have hf : Integrable f := integrable_realBesselOrderKernel_one_full hs
  change (∫ x : ℝ, f x) = _
  have hsplit := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hf
  simp only [compl_Ioi] at hsplit
  have hneg : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f (-x) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 f).symm
  have heven : ∀ x : ℝ, f (-x) = f x := by
    intro x
    simp only [f, Real.cosh_neg]
  have hreflect : (∫ x in Ioi (0 : ℝ), f (-x)) = ∫ x in Ioi (0 : ℝ), f x := by
    apply integral_congr_ae
    filter_upwards with x
    exact heven x
  rw [← hsplit, hneg, hreflect]
  rw [GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder]
  have hhalf :
      (∫ x in Ioi (0 : ℝ), f x) =
        ∫ x in Ioi (0 : ℝ),
          GaloisForLFunctions.HTGeometry.realBesselOrderKernel s 1 x := by
    apply integral_congr_ae
    filter_upwards with x
    simp [f, GaloisForLFunctions.HTGeometry.realBesselOrderKernel]
  rw [hhalf]
  ring

theorem integral_cosh_exp_neg_hyperbolic_linear_le_bessel
    {a A B : ℝ} (ha : 0 < a) (hB : 0 ≤ B) (hBA : B < A) :
    let q := Real.sqrt (A ^ (2 : ℕ) - B ^ (2 : ℕ))
    let r := Real.arsinh (B / q)
    (∫ x : ℝ, Real.cosh x *
      Real.exp (-a * (A * Real.cosh x + B * Real.sinh x))) ≤
        2 * Real.exp r *
          GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q) 1 := by
  dsimp only
  let q : ℝ := Real.sqrt (A ^ (2 : ℕ) - B ^ (2 : ℕ))
  let r : ℝ := Real.arsinh (B / q)
  let base : ℝ → ℝ := fun y =>
    Real.exp (-(a * q) * Real.cosh y) * Real.cosh y
  let f : ℝ → ℝ := fun x => Real.cosh x *
    Real.exp (-a * (A * Real.cosh x + B * Real.sinh x))
  let g : ℝ → ℝ := fun x => Real.exp r * base (x + r)
  have hD : 0 < A ^ (2 : ℕ) - B ^ (2 : ℕ) := by nlinarith
  have hq : 0 < q := by exact Real.sqrt_pos.2 hD
  have hr : 0 ≤ r := by
    rw [Real.arsinh_nonneg_iff]
    exact div_nonneg hB hq.le
  have hbase : Integrable base := by
    simpa only [base] using integrable_realBesselOrderKernel_one_full (mul_pos ha hq)
  have hg : Integrable g := by
    exact (hbase.comp_add_right r).const_mul (Real.exp r)
  have hfnonneg : 0 ≤ᵐ[volume] f := Filter.Eventually.of_forall fun x => by
    exact mul_nonneg (Real.cosh_pos x).le (Real.exp_nonneg _)
  have hfg : f ≤ᵐ[volume] g := Filter.Eventually.of_forall fun x => by
    have hboost := hyperbolic_boost_identity (x := x) hB hBA
    have hcosh : Real.cosh x ≤ Real.exp r * Real.cosh (x + r) := by
      have h := cosh_sub_le_exp_mul_cosh (y := x + r) hr
      simpa only [add_sub_cancel_right] using h
    dsimp only [f, g, base]
    rw [hboost]
    have hexp :
        Real.exp (-a * (q * Real.cosh (x + r))) =
          Real.exp (-(a * q) * Real.cosh (x + r)) := by congr 1; ring
    rw [hexp]
    calc
      Real.cosh x * Real.exp (-(a * q) * Real.cosh (x + r)) ≤
          (Real.exp r * Real.cosh (x + r)) *
            Real.exp (-(a * q) * Real.cosh (x + r)) :=
        mul_le_mul_of_nonneg_right hcosh (Real.exp_nonneg _)
      _ = Real.exp r *
          (Real.exp (-(a * q) * Real.cosh (x + r)) * Real.cosh (x + r)) := by ring
  have hint := integral_mono_of_nonneg hfnonneg hg hfg
  have hgval : (∫ x : ℝ, g x) =
      2 * Real.exp r *
        GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q) 1 := by
    calc
      (∫ x : ℝ, g x) = Real.exp r * ∫ x : ℝ, base (x + r) := by
        simp only [g, integral_const_mul]
      _ = Real.exp r * ∫ x : ℝ, base x := by
        rw [MeasureTheory.integral_add_right_eq_self base r]
      _ = Real.exp r *
          (2 * GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q) 1) := by
        rw [integral_realBesselOrderKernel_one_full_eq (mul_pos ha hq)]
      _ = _ := by ring
  dsimp only [f] at hint
  rw [hgval] at hint
  simpa only [q, r] using hint

theorem integrable_cosh_exp_neg_hyperbolic_linear
    {a A B : ℝ} (ha : 0 < a) (hB : 0 ≤ B) (hBA : B < A) :
    Integrable (fun x : ℝ => Real.cosh x *
      Real.exp (-a * (A * Real.cosh x + B * Real.sinh x))) := by
  let q : ℝ := Real.sqrt (A ^ (2 : ℕ) - B ^ (2 : ℕ))
  let r : ℝ := Real.arsinh (B / q)
  let base : ℝ → ℝ := fun y =>
    Real.exp (-(a * q) * Real.cosh y) * Real.cosh y
  let f : ℝ → ℝ := fun x => Real.cosh x *
    Real.exp (-a * (A * Real.cosh x + B * Real.sinh x))
  let g : ℝ → ℝ := fun x => Real.exp r * base (x + r)
  have hD : 0 < A ^ (2 : ℕ) - B ^ (2 : ℕ) := by nlinarith
  have hq : 0 < q := Real.sqrt_pos.2 hD
  have hr : 0 ≤ r := by
    rw [Real.arsinh_nonneg_iff]
    exact div_nonneg hB hq.le
  have hbase : Integrable base := by
    simpa only [base] using integrable_realBesselOrderKernel_one_full (mul_pos ha hq)
  have hg : Integrable g := (hbase.comp_add_right r).const_mul (Real.exp r)
  apply hg.mono'
  · fun_prop
  · filter_upwards with x
    have hboost := hyperbolic_boost_identity (x := x) hB hBA
    have hcosh : Real.cosh x ≤ Real.exp r * Real.cosh (x + r) := by
      have h := cosh_sub_le_exp_mul_cosh (y := x + r) hr
      simpa only [add_sub_cancel_right] using h
    have hfn : 0 ≤ f x :=
      mul_nonneg (Real.cosh_pos x).le (Real.exp_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hfn]
    dsimp only [f, g, base]
    rw [hboost]
    have hexp :
        Real.exp (-a * (q * Real.cosh (x + r))) =
          Real.exp (-(a * q) * Real.cosh (x + r)) := by congr 1; ring
    rw [hexp]
    calc
      Real.cosh x * Real.exp (-(a * q) * Real.cosh (x + r)) ≤
          (Real.exp r * Real.cosh (x + r)) *
            Real.exp (-(a * q) * Real.cosh (x + r)) :=
        mul_le_mul_of_nonneg_right hcosh (Real.exp_nonneg _)
      _ = Real.exp r *
          (Real.exp (-(a * q) * Real.cosh (x + r)) * Real.cosh (x + r)) := by ring

theorem realModifiedBesselKOrder_one_full_exponent
    {s₀ s : ℝ} (hs₀ : 0 < s₀) (hss₀ : s₀ ≤ s) :
    GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder s 1 ≤
      Real.exp (-(s - s₀)) *
        GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder s₀ 1 := by
  have hs : 0 < s := lt_of_lt_of_le hs₀ hss₀
  let f : ℝ → ℝ := GaloisForLFunctions.HTGeometry.realBesselOrderKernel s 1
  let g : ℝ → ℝ := fun t => Real.exp (-(s - s₀)) *
    GaloisForLFunctions.HTGeometry.realBesselOrderKernel s₀ 1 t
  have hf : IntegrableOn f (Ioi 0) :=
    GaloisForLFunctions.HTGeometry.integrableOn_realBesselOrderKernel hs 1
  have hg : IntegrableOn g (Ioi 0) :=
    (GaloisForLFunctions.HTGeometry.integrableOn_realBesselOrderKernel hs₀ 1).const_mul _
  have hfg : f ≤ᵐ[volume.restrict (Ioi 0)] g := Filter.Eventually.of_forall fun t => by
    have hcosh : 1 ≤ Real.cosh t := Real.one_le_cosh t
    have hdecay : Real.exp (-(s - s₀) * Real.cosh t) ≤
        Real.exp (-(s - s₀)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    dsimp only [f, g, GaloisForLFunctions.HTGeometry.realBesselOrderKernel]
    simp only [one_mul]
    have hsplit : Real.exp (-s * Real.cosh t) =
        Real.exp (-(s - s₀) * Real.cosh t) *
          Real.exp (-s₀ * Real.cosh t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    have htail : 0 ≤ Real.exp (-s₀ * Real.cosh t) * Real.cosh t :=
      mul_nonneg (Real.exp_nonneg _) (Real.cosh_pos t).le
    calc
      Real.exp (-(s - s₀) * Real.cosh t) *
          Real.exp (-s₀ * Real.cosh t) * Real.cosh t =
        Real.exp (-(s - s₀) * Real.cosh t) *
          (Real.exp (-s₀ * Real.cosh t) * Real.cosh t) := by ring
      _ ≤ Real.exp (-(s - s₀)) *
          (Real.exp (-s₀ * Real.cosh t) * Real.cosh t) :=
        mul_le_mul_of_nonneg_right hdecay htail
  have hint := integral_mono_ae hf hg hfg
  simpa only [f, g, GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder,
    integral_const_mul] using hint

theorem norm_stripFourier_xiMass_le_curvedBessel
    {a sigma u h theta : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u ≤ h)
    (htheta0 : 0 ≤ theta) (hthetaPi : theta < Real.pi / 2) :
    let A := sigma * Real.cos theta + h * Real.sin theta
    let B := u * Real.sin theta
    let q := Real.sqrt (A ^ (2 : ℕ) - B ^ (2 : ℕ))
    let r := Real.arsinh (B / q)
    ‖RHTower.stripFourier
      (RHTower.xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖ ≤
        2 * a * Real.exp r *
          GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q) 1 := by
  dsimp only
  let A : ℝ := sigma * Real.cos theta + h * Real.sin theta
  let B : ℝ := u * Real.sin theta
  let q : ℝ := Real.sqrt (A ^ (2 : ℕ) - B ^ (2 : ℕ))
  let r : ℝ := Real.arsinh (B / q)
  let F : ℂ → ℂ := RHTower.xiMassHyperbolicEntireKernel a sigma u h
  let major : ℝ → ℝ := fun x => a * (Real.cosh x *
    Real.exp (-a * (A * Real.cosh x + B * Real.sinh x)))
  have hthetaNeg : -(Real.pi / 2) < theta := by
    nlinarith [Real.pi_pos]
  have hcostheta : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨hthetaNeg, hthetaPi⟩
  have hthetaLePi : theta ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hsintheta : 0 ≤ Real.sin theta :=
    Real.sin_nonneg_of_nonneg_of_le_pi htheta0 hthetaLePi
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hBA : B < A := by
    dsimp only [A, B]
    have hmain : 0 < sigma * Real.cos theta := mul_pos hsigma hcostheta
    have htail : 0 ≤ (h - u) * Real.sin theta :=
      mul_nonneg (sub_nonneg.mpr huh) hsintheta
    nlinarith
  have hq : 0 < q := by
    apply Real.sqrt_pos.2
    nlinarith
  have hmajor : Integrable major := by
    have hbase := integrable_cosh_exp_neg_hyperbolic_linear ha hB hBA
    exact hbase.const_mul a
  have hnorm : ‖∫ x : ℝ, F ((x : ℂ) - (theta : ℂ) * I)‖ ≤
      ∫ x : ℝ, major x := by
    apply norm_integral_le_of_norm_le hmajor
    filter_upwards with x
    dsimp only [F, major, A, B]
    rw [RHTower.norm_xiMassHyperbolicEntireKernel_shift ha]
    calc
      a * ‖Complex.cosh ((x : ℂ) - (theta : ℂ) * I)‖ *
          Real.exp (-a * ((sigma * Real.cos theta + h * Real.sin theta) * Real.cosh x +
            u * Real.sin theta * Real.sinh x)) ≤
        (a * Real.cosh x) *
          Real.exp (-a * ((sigma * Real.cos theta + h * Real.sin theta) * Real.cosh x +
            u * Real.sin theta * Real.sinh x)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (RHTower.norm_cosh_sub_mul_I_le_cosh x theta) ha.le)
          (Real.exp_nonneg _)
      _ = a * (Real.cosh x *
          Real.exp (-a * ((sigma * Real.cos theta + h * Real.sin theta) * Real.cosh x +
            u * Real.sin theta * Real.sinh x))) := by ring
  have hbessel := integral_cosh_exp_neg_hyperbolic_linear_le_bessel ha hB hBA
  have hmajorBessel : (∫ x : ℝ, major x) ≤
      2 * a * Real.exp r *
        GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q) 1 := by
    dsimp only [major]
    rw [integral_const_mul]
    have hscaled := mul_le_mul_of_nonneg_left hbessel ha.le
    calc
      a * ∫ x : ℝ, Real.cosh x *
          Real.exp (-a * (A * Real.cosh x + B * Real.sinh x)) ≤
        a * (2 * Real.exp r *
          GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q) 1) := by
        simpa only [q, r] using hscaled
      _ = _ := by ring
  have hreal :
      RHTower.stripFourier
          (RHTower.xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ) =
        ∫ x : ℝ, F (x : ℂ) := by
    calc
      RHTower.stripFourier
          (RHTower.xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ) =
          ∫ x : ℝ, RHTower.xiMassHyperbolicFourierKernel a sigma u h x :=
        RHTower.stripFourier_xiMass_eq_integral_hyperbolicFourier ha hsigma
      _ = ∫ x : ℝ, F (x : ℂ) := by
        apply integral_congr_ae
        filter_upwards with x
        exact (RHTower.xiMassHyperbolicEntireKernel_ofReal a sigma u h x).symm
  have hshift := integral_xiMassHyperbolicEntireKernel_shift_eq
    ha hsigma hu huh htheta0 hthetaPi
  have hrepresentation :
      RHTower.stripFourier
          (RHTower.xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ) =
        ∫ x : ℝ, F ((x : ℂ) - (theta : ℂ) * I) := by
    exact hreal.trans hshift.symm
  rw [hrepresentation]
  exact hnorm.trans hmajorBessel

theorem norm_stripFourier_xiMass_le_curvedBessel_full_exponent
    {a sigma u h theta q₀ : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u ≤ h)
    (htheta0 : 0 ≤ theta) (hthetaPi : theta < Real.pi / 2)
    (hq₀ : 0 < q₀)
    (hq₀q : q₀ ≤ Real.sqrt
      ((sigma * Real.cos theta + h * Real.sin theta) ^ (2 : ℕ) -
        (u * Real.sin theta) ^ (2 : ℕ))) :
    let A := sigma * Real.cos theta + h * Real.sin theta
    let B := u * Real.sin theta
    let q := Real.sqrt (A ^ (2 : ℕ) - B ^ (2 : ℕ))
    let r := Real.arsinh (B / q)
    ‖RHTower.stripFourier
      (RHTower.xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖ ≤
        2 * a * Real.exp r * Real.exp (-(a * (q - q₀))) *
          GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q₀) 1 := by
  dsimp only
  let A : ℝ := sigma * Real.cos theta + h * Real.sin theta
  let B : ℝ := u * Real.sin theta
  let q : ℝ := Real.sqrt (A ^ (2 : ℕ) - B ^ (2 : ℕ))
  let r : ℝ := Real.arsinh (B / q)
  have hbase := norm_stripFourier_xiMass_le_curvedBessel
    ha hsigma hu huh htheta0 hthetaPi
  have hq₀q' : q₀ ≤ q := by simpa only [q, A, B] using hq₀q
  have hK := realModifiedBesselKOrder_one_full_exponent
    (s₀ := a * q₀) (s := a * q) (mul_pos ha hq₀)
    (mul_le_mul_of_nonneg_left hq₀q' ha.le)
  have hcoef : 0 ≤ 2 * a * Real.exp r := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hK hcoef
  calc
    ‖RHTower.stripFourier
        (RHTower.xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖ ≤
        2 * a * Real.exp r *
          GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q) 1 := by
      simpa only [q, r, A, B] using hbase
    _ ≤ (2 * a * Real.exp r) *
        (Real.exp (-(a * q - a * q₀)) *
          GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q₀) 1) := by
      simpa only [mul_assoc] using hscaled
    _ = 2 * a * Real.exp r * Real.exp (-(a * (q - q₀))) *
        GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * q₀) 1 := by
      have hexp : Real.exp (-(a * q - a * q₀)) =
          Real.exp (-(a * (q - q₀))) := by congr 1; ring
      rw [hexp]
      ring


end

end RHTower
