import GaloisForLFunctions.RHTower.ZetaNotchCriticalTail
import GaloisForLFunctions.RHTower.ZetaVerticalSqrtBound

/-!
# The mixed `|ζ|²` notch with the Gamma-weight poles moved to `±2i`

Replace the weight `(2/(¼+z²))²` of the mixed test by `(2/(4+z²))²`. The new test
`G = Ω_L Q (2/(4+z²))² Γℝ(½+iz)^{−1} Γℝ(½−iz)^{−1}` is holomorphic on `|Im z| < 2`, and on the line
`Ξ² G = Ω_L q r |ζ|²` with `r(t) = ((¼+t²)/(4+t²))²`. Consequences:

* **pairing** (`sum_mul_re_shiftMoment_nonpos`): `Σ_n v(n) Re M_r(log n) ≤ 0` as soon as
  `Σ_n |v(n)| n^{−3/4} < ∞`, for `M_r(y) = ∫ Ω_L q r |ζ|² e^{−iyt}`;
* **tail** (`exists_norm_shiftMoment_le`): `r` vanishes at `±i/2`, so the residue at the pole of
  `ζ` disappears and `‖M_r(y)‖ ≤ C (1 + L) e^{−y}`;
* **defect** (`exists_norm_defectMoment_le`): `M_r = M_Ω − M_{1−r}` with `1 − r ≤ (15/2)/(4 + t²)`
  and `|ζ(½+it)|² ≤ 36(|t| + 3)`, so `‖M_{1−r}(y)‖ ≤ C/(2 + L)` uniformly in `y`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry
open FourierTransform
open scoped ComplexConjugate

namespace RHTower.ZetaNotch

/-! ## The shift factor -/

/-- The holomorphic shift factor `((¼+z²)/(4+z²))²`. -/
def shiftFactorC (z : ℂ) : ℂ := ((1 / 4 + z ^ 2) / (4 + z ^ 2)) ^ 2

/-- The shift factor on the real line. -/
def shiftFactor (t : ℝ) : ℝ := ((1 / 4 + t ^ 2) / (4 + t ^ 2)) ^ 2

theorem shiftFactorC_ofReal (t : ℝ) : shiftFactorC t = shiftFactor t := by
  unfold shiftFactorC shiftFactor
  push_cast
  ring

theorem shiftFactor_nonneg (t : ℝ) : 0 ≤ shiftFactor t := by unfold shiftFactor; positivity

theorem shiftFactor_le_one (t : ℝ) : shiftFactor t ≤ 1 := by
  unfold shiftFactor
  have h : (1 / 4 + t ^ 2) / (4 + t ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have h0 : 0 ≤ (1 / 4 + t ^ 2) / (4 + t ^ 2) := by positivity
  nlinarith

/-- `1 − r(t) ≤ (15/2)/(4 + t²)`. -/
theorem one_sub_shiftFactor_le (t : ℝ) : 1 - shiftFactor t ≤ 15 / 2 / (4 + t ^ 2) := by
  unfold shiftFactor
  set a := (1 / 4 + t ^ 2) / (4 + t ^ 2) with ha
  have h4 : 0 < 4 + t ^ 2 := by positivity
  have ha1 : 1 - a = 15 / 4 / (4 + t ^ 2) := by
    rw [ha]; field_simp; ring
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb : 0 ≤ 15 / 4 / (4 + t ^ 2) := by positivity
  have : 1 - a ^ 2 = (1 - a) * (1 + a) := by ring
  rw [this, ha1]
  have hle : a ≤ 1 := by linarith
  calc 15 / 4 / (4 + t ^ 2) * (1 + a) ≤ 15 / 4 / (4 + t ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) hb
    _ = 15 / 2 / (4 + t ^ 2) := by ring

theorem four_add_sq_re (z : ℂ) : (4 + z ^ 2).re = 4 + z.re ^ 2 - z.im ^ 2 := by
  simp [sq]; ring

theorem four_add_sq_ne_zero {z : ℂ} (hz : |z.im| < 2) : (4 : ℂ) + z ^ 2 ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  rw [four_add_sq_re, Complex.zero_re] at h1
  have := abs_lt.mp hz
  nlinarith [sq_nonneg z.re]

theorem differentiableAt_shiftFactorC {z : ℂ} (hz : |z.im| < 2) :
    DifferentiableAt ℂ shiftFactorC z := by
  have hn : DifferentiableAt ℂ (fun w : ℂ => (1 / 4 : ℂ) + w ^ 2) z := by fun_prop
  have hd : DifferentiableAt ℂ (fun w : ℂ => (4 : ℂ) + w ^ 2) z := by fun_prop
  exact (hn.div hd (four_add_sq_ne_zero hz)).pow 2

/-- `‖r(z)‖ ≤ 1` on `|Im z| ≤ 1`. -/
theorem norm_shiftFactorC_le_one {z : ℂ} (hz : |z.im| ≤ 1) : ‖shiftFactorC z‖ ≤ 1 := by
  have hne := four_add_sq_ne_zero (z := z) (by linarith)
  have hpos : 0 < ‖(4 : ℂ) + z ^ 2‖ := norm_pos_iff.mpr hne
  have hle : ‖(1 / 4 : ℂ) + z ^ 2‖ ≤ ‖(4 : ℂ) + z ^ 2‖ := by
    have hy : z.im ^ 2 ≤ 1 := by have := abs_le.mp hz; nlinarith
    have hre1 : ((1 / 4 : ℂ) + z ^ 2).re = 1 / 4 + z.re ^ 2 - z.im ^ 2 := re_quarter_add_sq z
    have him1 : ((1 / 4 : ℂ) + z ^ 2).im = 2 * z.re * z.im := by simp [sq]; ring
    have hre2 : ((4 : ℂ) + z ^ 2).re = 4 + z.re ^ 2 - z.im ^ 2 := four_add_sq_re z
    have him2 : ((4 : ℂ) + z ^ 2).im = 2 * z.re * z.im := by simp [sq]; ring
    have e1 : ‖(1 / 4 : ℂ) + z ^ 2‖ ^ 2 =
        (1 / 4 + z.re ^ 2 - z.im ^ 2) ^ 2 + (2 * z.re * z.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre1, him1]; ring
    have e2 : ‖(4 : ℂ) + z ^ 2‖ ^ 2 = (4 + z.re ^ 2 - z.im ^ 2) ^ 2 + (2 * z.re * z.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre2, him2]; ring
    have h2 : ‖(1 / 4 : ℂ) + z ^ 2‖ ^ 2 ≤ ‖(4 : ℂ) + z ^ 2‖ ^ 2 := by
      rw [e1, e2]; nlinarith [sq_nonneg z.re]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h2
  unfold shiftFactorC
  rw [norm_pow, norm_div]
  have : ‖(1 / 4 : ℂ) + z ^ 2‖ / ‖(4 : ℂ) + z ^ 2‖ ≤ 1 := by rw [div_le_one hpos]; exact hle
  have h0 : 0 ≤ ‖(1 / 4 : ℂ) + z ^ 2‖ / ‖(4 : ℂ) + z ^ 2‖ := by positivity
  calc (‖(1 / 4 : ℂ) + z ^ 2‖ / ‖(4 : ℂ) + z ^ 2‖) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 this 2
    _ = 1 := one_pow 2

theorem shiftFactorC_neg_half_I : shiftFactorC (-I / 2) = 0 := by
  unfold shiftFactorC
  have : (1 / 4 : ℂ) + (-I / 2) ^ 2 = 0 := by ring_nf; rw [I_sq]; ring
  rw [this, zero_div, zero_pow two_ne_zero]

/-! ## The shifted-pole Gamma weight -/

/-- The weight `(2/(4+z²))² Γℝ(½+iz)^{−1} Γℝ(½−iz)^{−1}`. -/
def shiftWeightC (z : ℂ) : ℂ :=
  (2 / (4 + z ^ 2)) ^ 2 * ((Complex.Gammaℝ (1 / 2 + z * I))⁻¹ * (Complex.Gammaℝ (1 / 2 - z * I))⁻¹)

theorem shiftWeightC_eq (z : ℂ) (hq : (1 / 4 : ℂ) + z ^ 2 ≠ 0) :
    shiftWeightC z = gammaWeightC z * shiftFactorC z := by
  have e : (2 / (4 + z ^ 2)) ^ 2 = (2 / (1 / 4 + z ^ 2)) ^ 2 * ((1 / 4 + z ^ 2) / (4 + z ^ 2)) ^ 2 := by
    rw [div_pow, div_pow, div_pow, div_mul_div_comm, mul_comm ((2 : ℂ) ^ 2),
      mul_div_mul_left _ _ (pow_ne_zero 2 hq)]
  unfold shiftWeightC gammaWeightC shiftFactorC
  rw [e]
  ring

theorem shiftWeightC_ofReal (t : ℝ) : shiftWeightC t = gammaWeightInv t * (shiftFactor t : ℂ) := by
  have hq : (1 / 4 : ℂ) + (t : ℂ) ^ 2 ≠ 0 := quarter_add_sq_ne_zero (by simp)
  rw [shiftWeightC_eq _ hq, gammaWeightC_ofReal, shiftFactorC_ofReal]

theorem differentiableAt_shiftWeightC {z : ℂ} (hz : |z.im| < 2) :
    DifferentiableAt ℂ shiftWeightC z := by
  have hG : Differentiable ℂ fun s : ℂ => (Complex.Gammaℝ s)⁻¹ := Complex.differentiable_Gammaℝ_inv
  have hd : DifferentiableAt ℂ (fun w : ℂ => (4 : ℂ) + w ^ 2) z := by fun_prop
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (2 / ((4 : ℂ) + w ^ 2)) ^ 2) z :=
    ((differentiableAt_const (2 : ℂ)).div hd (four_add_sq_ne_zero hz)).pow 2
  have h2 : DifferentiableAt ℂ (fun w : ℂ => (Complex.Gammaℝ (1 / 2 + w * I))⁻¹) z :=
    DifferentiableAt.comp (g := fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
      (f := fun w : ℂ => 1 / 2 + w * I) z hG.differentiableAt (by fun_prop)
  have h3 : DifferentiableAt ℂ (fun w : ℂ => (Complex.Gammaℝ (1 / 2 - w * I))⁻¹) z :=
    DifferentiableAt.comp (g := fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
      (f := fun w : ℂ => 1 / 2 - w * I) z hG.differentiableAt (by fun_prop)
  exact h1.mul (h2.mul h3)

/-- `‖Γℝ(½ + iz)^{−1}‖ ≤ C e^{π|Re z|/2}` on `|Im z| ≤ 3/4`. -/
theorem exists_norm_inv_Gammaℝ_half_add_le_wide :
    ∃ C, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ 3 / 4 →
      ‖(Complex.Gammaℝ (1 / 2 + z * I))⁻¹‖ ≤ C * Real.exp (Real.pi * |z.re| / 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_norm_inv_Gammaℝ (-1) 2 (by norm_num)
  have hG : Differentiable ℂ fun s : ℂ => (Complex.Gammaℝ s)⁻¹ := Complex.differentiable_Gammaℝ_inv
  obtain ⟨M, hM0, hM⟩ := exists_bound_on_box (f := fun z : ℂ => (Complex.Gammaℝ (1 / 2 + z * I))⁻¹)
    (a := 2) (c := 3 / 4) fun z _ _ => (hG.differentiableAt.comp z (by fun_prop)).continuousAt
  refine ⟨max C₁ M, le_max_of_le_left hC₁0, fun z hz => ?_⟩
  have hre : (1 / 2 + z * I).re = 1 / 2 - z.im := by simp; ring
  have him : (1 / 2 + z * I).im = z.re := by simp
  have he : 1 ≤ Real.exp (Real.pi * |z.re| / 2) := Real.one_le_exp (by positivity)
  rcases le_or_gt 2 |z.re| with h2 | h2
  · have h := hC₁ (1 / 2 + z * I) (by rw [hre]; linarith [(abs_le.mp hz).2])
      (by rw [hre]; linarith [(abs_le.mp hz).1]) (by rw [him]; exact h2)
    rw [him] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · calc ‖(Complex.Gammaℝ (1 / 2 + z * I))⁻¹‖ ≤ M := hM z h2.le hz
      _ ≤ max C₁ M * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ max C₁ M * Real.exp (Real.pi * |z.re| / 2) :=
          mul_le_mul_of_nonneg_left he (le_max_of_le_left hC₁0)

/-- `‖W₂(z)‖ ≤ C e^{π|Re z|}` on `|Im z| ≤ 3/4`. -/
theorem exists_norm_shiftWeightC_le :
    ∃ C, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ 3 / 4 → ‖shiftWeightC z‖ ≤ C * Real.exp (Real.pi * |z.re|) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_inv_Gammaℝ_half_add_le_wide
  refine ⟨(2 / (55 / 16)) ^ 2 * (C * C), by positivity, fun z hz => ?_⟩
  have h1 := hC z hz
  have h2 := hC (-z) (by rw [Complex.neg_im, abs_neg]; exact hz)
  rw [Complex.neg_re, abs_neg, show (1 / 2 : ℂ) + -z * I = 1 / 2 - z * I by ring] at h2
  have hnq : 55 / 16 ≤ ‖(4 : ℂ) + z ^ 2‖ := by
    have h := Complex.re_le_norm ((4 : ℂ) + z ^ 2)
    rw [four_add_sq_re] at h
    have : z.im ^ 2 ≤ 9 / 16 := by have := abs_le.mp hz; nlinarith
    nlinarith [sq_nonneg z.re]
  have hfrac : ‖(2 / (4 + z ^ 2)) ^ 2‖ ≤ (2 / (55 / 16)) ^ 2 := by
    rw [norm_pow, norm_div]
    have hn2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hn2]
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnq) 2
  unfold shiftWeightC
  rw [norm_mul, norm_mul]
  have hexp : Real.exp (Real.pi * |z.re| / 2) * Real.exp (Real.pi * |z.re| / 2) =
      Real.exp (Real.pi * |z.re|) := by rw [← Real.exp_add]; ring_nf
  calc ‖(2 / (4 + z ^ 2)) ^ 2‖ * (‖(Complex.Gammaℝ (1 / 2 + z * I))⁻¹‖ *
        ‖(Complex.Gammaℝ (1 / 2 - z * I))⁻¹‖)
      ≤ (2 / (55 / 16)) ^ 2 * ((C * Real.exp (Real.pi * |z.re| / 2)) *
          (C * Real.exp (Real.pi * |z.re| / 2))) :=
        mul_le_mul hfrac (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
          (by positivity) (by positivity)
    _ = (2 / (55 / 16)) ^ 2 * (C * C) * Real.exp (Real.pi * |z.re|) := by
        rw [← hexp]; ring

/-! ## The shifted-pole test and its moment -/

/-- The shifted-pole test `Ω_L Q W₂`. -/
def shiftTest (L : ℝ) (Q : ℂ → ℂ) (z : ℂ) : ℂ := mixWindow L z * Q z * shiftWeightC z

/-- The shifted-pole moment `M_r(y) = ∫ Ω_L(t) q(t) r(t) |ζ(½+it)|² e^{−iyt} dt`. -/
def shiftMoment (L : ℝ) (q : ℝ → ℝ) (y : ℝ) : ℂ :=
  ∫ t : ℝ, mixWindow L t * (q t : ℂ) * (shiftFactor t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I)

/-- The defect moment `M_{1−r}(y)`. -/
def defectMoment (L : ℝ) (q : ℝ → ℝ) (y : ℝ) : ℂ :=
  ∫ t : ℝ, mixWindow L t * (q t : ℂ) * ((1 - shiftFactor t : ℝ) : ℂ) * zetaSq t *
    Complex.exp (-(y * t) * I)

theorem differentiableAt_shiftTest (L : ℝ) {Q : ℂ → ℂ} (hQd : Differentiable ℂ Q) {z : ℂ}
    (hz : |z.im| < 2) : DifferentiableAt ℂ (shiftTest L Q) z :=
  (((differentiable_mixWindow L) z).mul (hQd z)).mul (differentiableAt_shiftWeightC hz)

theorem continuous_shiftTest_ofReal (L : ℝ) {Q : ℂ → ℂ} (hQd : Differentiable ℂ Q) :
    Continuous fun t : ℝ => shiftTest L Q t := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (differentiableAt_shiftTest L hQd (by simp)).continuousAt.comp
    Complex.continuous_ofReal.continuousAt

/-- **The shifted-pole test decays in the real direction** on `|Im z| ≤ 3/4`. -/
theorem exists_norm_shiftTest_le (L : ℝ) {Q : ℂ → ℂ} {CQ : ℝ}
    (hQb : ∀ z : ℂ, |z.im| ≤ 3 / 4 → ‖Q z‖ ≤ CQ) :
    ∃ C, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ 3 / 4 → ‖shiftTest L Q z‖ ≤ C * Real.exp (-|z.re|) := by
  obtain ⟨CW, hCW0, hCW⟩ := exists_norm_shiftWeightC_le
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hQb 0 (by norm_num))
  refine ⟨Real.exp (9 / 4) * (4 * Real.exp (L ^ 2)) * CQ * CW * Real.exp 56, by positivity,
    fun z hz => ?_⟩
  have h1 : ‖mixWindow L z‖ ≤
      Real.exp (9 / 4) * (4 * (Real.exp (L ^ 2) * Real.exp (-(2 / 25) * z.re ^ 2))) := by
    refine (norm_mixWindow_le_line L z).trans (mul_le_mul (Real.exp_le_exp.mpr ?_)
      (mixWindowReal_le_gauss L z.re) (mixWindowReal_nonneg _ _) (Real.exp_pos _).le)
    have := abs_le.mp hz
    nlinarith
  have h2 := hQb z hz
  have h3 := hCW z hz
  have h4 := gauss_mul_exp_pi_le z.re
  unfold shiftTest
  rw [norm_mul, norm_mul]
  calc ‖mixWindow L z‖ * ‖Q z‖ * ‖shiftWeightC z‖
      ≤ (Real.exp (9 / 4) * (4 * (Real.exp (L ^ 2) * Real.exp (-(2 / 25) * z.re ^ 2)))) * CQ *
          (CW * Real.exp (Real.pi * |z.re|)) :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _)
          (by positivity)
    _ = Real.exp (9 / 4) * (4 * Real.exp (L ^ 2)) * CQ * CW *
          (Real.exp (-(2 / 25) * z.re ^ 2) * Real.exp (Real.pi * |z.re|)) := by ring
    _ ≤ Real.exp (9 / 4) * (4 * Real.exp (L ^ 2)) * CQ * CW * (Real.exp 56 * Real.exp (-|z.re|)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

theorem shiftTest_ofReal (L : ℝ) {Q : ℂ → ℂ} {q : ℝ → ℝ} (hQq : ∀ t : ℝ, Q t = q t) (t : ℝ) :
    shiftTest L Q t = ((mixWindowReal L t * q t *
      ((2 / (1 / 4 + t ^ 2)) ^ 2 / Complex.normSq (Complex.Gammaℝ (linePt t))) *
        shiftFactor t : ℝ) : ℂ) := by
  unfold shiftTest
  rw [mixWindow_ofReal, hQq, shiftWeightC_ofReal, gammaWeightInv_eq_ofReal]
  push_cast
  ring

theorem XiC_sq_mul_shiftTest (L : ℝ) {Q : ℂ → ℂ} {q : ℝ → ℝ} (hQq : ∀ t : ℝ, Q t = q t) (t : ℝ) :
    XiC (t : ℂ) ^ 2 * shiftTest L Q t =
      mixWindow L t * (q t : ℂ) * (shiftFactor t : ℂ) * zetaSq t := by
  unfold shiftTest
  rw [hQq, shiftWeightC_ofReal, ← XiC_sq_mul_gammaWeightInv]
  ring

theorem fourier_riemannXi_sq_mul_shiftTest (L : ℝ) {Q : ℂ → ℂ} {q : ℝ → ℝ}
    (hQq : ∀ t : ℝ, Q t = q t) (y : ℝ) :
    𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * shiftTest L Q ((2 * Real.pi * ξ : ℝ) : ℂ))
        y = ((1 / (2 * Real.pi) : ℝ) : ℂ) * shiftMoment L q y := by
  rw [RHTower.WeilExcess.fourier_eq_integral]
  set f : ℝ → ℂ := fun t => mixWindow L t * (q t : ℂ) * (shiftFactor t : ℂ) * zetaSq t *
    Complex.exp (-(y * t) * I) with hf
  have e : (fun ξ : ℝ => Complex.exp (-(2 * Real.pi * ξ * y : ℝ) * I) *
      (RHTower.WeilExcess.riemannXi ξ ^ 2 * shiftTest L Q ((2 * Real.pi * ξ : ℝ) : ℂ))) =
      fun ξ : ℝ => f (2 * Real.pi * ξ) := by
    funext ξ
    rw [RHTower.WeilExcess.riemannXi_eq_XiC,
      show (2 * Real.pi * ξ : ℂ) = ((2 * Real.pi * ξ : ℝ) : ℂ) by push_cast; ring,
      XiC_sq_mul_shiftTest L hQq, hf]
    simp only
    rw [show -((2 * Real.pi * ξ * y : ℝ) : ℂ) * I = -((y : ℂ) * ((2 * Real.pi * ξ : ℝ) : ℂ)) * I by
      push_cast; ring]
    ring
  rw [e, Measure.integral_comp_mul_left f (2 * Real.pi), Complex.real_smul]
  congr 1
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), one_div]

theorem shiftMoment_neg (L : ℝ) (q : ℝ → ℝ) (y : ℝ) :
    shiftMoment L q (-y) = conj (shiftMoment L q y) := by
  unfold shiftMoment
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [map_mul, mixWindow_ofReal, Complex.conj_ofReal, zetaSq_eq_normSq]
  rw [← Complex.exp_conj]
  congr 2
  simp

/-- **The pairing inequality for the shifted-pole notch.** It needs only `Σ |v(n)| n^{−3/4} < ∞`. -/
theorem sum_mul_re_shiftMoment_nonpos {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hs : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-(3 / 4 : ℝ)))
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    (L : ℝ) {Q : ℂ → ℂ} (hQd : Differentiable ℂ Q) {CQ : ℝ}
    (hQb : ∀ z : ℂ, |z.im| ≤ 3 / 4 → ‖Q z‖ ≤ CQ) {q : ℝ → ℝ} (hQq : ∀ t : ℝ, Q t = q t)
    (hq0 : ∀ t, 0 ≤ q t) :
    ∑' n : ℕ, v n * (shiftMoment L q (Real.log n)).re ≤ 0 := by
  have hcont := RHTower.WeilRegular.continuous_nullPotential_of_log hv0 hA ha
  obtain ⟨σ, hσf, hσ⟩ := exists_charFun_eq_of_positiveDefinite hPD
    (Complex.continuous_ofReal.comp hcont.neg)
  set G : ℂ → ℂ := shiftTest L Q with hG
  set g : ℝ → ℂ := fun ξ => G ((2 * Real.pi * ξ : ℝ) : ℂ) with hg
  obtain ⟨CG, hCG0, hGb⟩ := exists_norm_shiftTest_le L hQb
  have hGd : ∀ z : ℂ, |z.im| ≤ 3 / 4 → DifferentiableAt ℂ G z := fun z hz =>
    differentiableAt_shiftTest L hQd (by linarith)
  have hGc : Continuous fun t : ℝ => G t := continuous_shiftTest_ofReal L hQd
  have hgc : Continuous g := hGc.comp (by fun_prop)
  have hgb : ∀ ξ : ℝ, ‖g ξ‖ ≤ CG * Real.exp (-(1 * |ξ|)) := by
    intro ξ
    have h := hGb ((2 * Real.pi * ξ : ℝ) : ℂ) (by simp; norm_num)
    rw [Complex.ofReal_re] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCG0)
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), one_mul]
    have := Real.pi_gt_three
    nlinarith [abs_nonneg ξ]
  have hgi : Integrable g :=
    ((integrable_exp_neg_mul_abs' one_pos).const_mul CG).mono' hgc.aestronglyMeasurable
      (Eventually.of_forall hgb)
  set E : ℝ := ∫ x : ℝ, Real.exp (-(1 * |x|)) with hE
  have hdec : ∀ w, ‖𝓕 g w‖ ≤ ((2 * Real.pi)⁻¹ * (CG * E)) * Real.exp (-(3 / 4 * |w|)) := by
    intro w
    rw [RHTower.WeilExcess.fourier_eq_integral]
    set h : ℝ → ℂ := fun t => G t * Complex.exp (-(w * t) * I) with hh
    have e : (fun ξ : ℝ => Complex.exp (-(2 * Real.pi * ξ * w : ℝ) * I) * g ξ) =
        fun ξ : ℝ => h (2 * Real.pi * ξ) := by
      funext ξ
      rw [hh, hg]
      simp only
      rw [show -((2 * Real.pi * ξ * w : ℝ) : ℂ) * I = -((w : ℂ) * ((2 * Real.pi * ξ : ℝ) : ℂ)) * I by
        push_cast; ring]
      ring
    rw [e, Measure.integral_comp_mul_left h (2 * Real.pi), norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < |(2 * Real.pi)⁻¹|),
      abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹)]
    have hb := norm_integral_mul_cexp_le_of_strip (by norm_num : (0 : ℝ) ≤ 3 / 4) hGd hGb w
    calc (2 * Real.pi)⁻¹ * ‖∫ t, h t‖ ≤ (2 * Real.pi)⁻¹ * (CG * E * Real.exp (-(3 / 4 * |w|))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  have hpair := RHTower.WeilRegular.nullPotential_pairing_exp hv0 (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num) hs σ hσ hgc hgi hdec
  set k : ℝ := 1 / (2 * Real.pi) with hk
  have hF : ∀ y, 𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) y =
      (k : ℂ) * shiftMoment L q y := fun y => fourier_riemannXi_sq_mul_shiftTest L hQq y
  have hterm : ∀ n : ℕ, (v n : ℂ) *
      (𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (Real.log n) +
        𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (-Real.log n)) =
      ((2 * k * (v n * (shiftMoment L q (Real.log n)).re) : ℝ) : ℂ) := by
    intro n
    rw [hF, hF, shiftMoment_neg, ← mul_add, Complex.add_conj]
    push_cast
    ring
  rw [tsum_congr hterm, ← Complex.ofReal_tsum] at hpair
  have hre := congrArg Complex.re hpair
  rw [Complex.ofReal_re, Complex.neg_re] at hre
  have hGeq : (fun t => g (t / (2 * Real.pi))) = fun t : ℝ => G t := by
    funext t
    rw [hg]
    simp only
    congr 2
    field_simp
  have hGb1 : ∀ t : ℝ, ‖G t‖ ≤ CG := fun t => by
    have h := hGb t (by simp; norm_num)
    exact h.trans (mul_le_of_le_one_right hCG0 (Real.exp_le_one_iff.mpr (by
      simp only [Complex.ofReal_re]; linarith [abs_nonneg t])))
  have hGi : Integrable (fun t : ℝ => G t) σ :=
    Integrable.of_bound hGc.aestronglyMeasurable CG (Eventually.of_forall hGb1)
  have hnn : 0 ≤ (∫ t, g (t / (2 * Real.pi)) ∂σ).re := by
    have h := integral_re hGi
    simp only [RCLike.re_to_complex] at h
    rw [hGeq, ← h]
    refine integral_nonneg fun t => ?_
    rw [hG, shiftTest_ofReal L hQq, Complex.ofReal_re]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mixWindowReal_nonneg L t) (hq0 t))
      (gammaWeightInv_real_pos t).le) (shiftFactor_nonneg t)
  rw [tsum_mul_left] at hre
  have h2k : 0 < 2 * k := by positivity
  by_contra hpos
  push Not at hpos
  have : 0 < 2 * k * ∑' n : ℕ, v n * (shiftMoment L q (Real.log n)).re := mul_pos h2k hpos
  linarith

/-! ## The defect and the tail -/

theorem integrable_mixWindow_mul_bounded {L : ℝ} {q a : ℝ → ℝ} (hqc : Continuous q)
    (hac : Continuous a) {CQ : ℝ} (hqb : ∀ t, |q t| ≤ CQ) (hab : ∀ t, |a t| ≤ 1) (y : ℝ) :
    Integrable fun t : ℝ => mixWindow L t * (q t : ℂ) * (a t : ℂ) * zetaSq t *
      Complex.exp (-(y * t) * I) := by
  obtain ⟨CZ, hCZ0, hCZ⟩ := exists_norm_zetaSq_le
  have hCQ0 : 0 ≤ CQ := (abs_nonneg _).trans (hqb 0)
  refine ((integrable_mixWindowReal_mul_sq L).const_mul (CQ * CZ)).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have hw : Continuous fun t : ℝ => mixWindow L t := by
      simp_rw [mixWindow_ofReal]; exact Complex.continuous_ofReal.comp (continuous_mixWindowReal L)
    exact (((hw.mul (Complex.continuous_ofReal.comp hqc)).mul
      (Complex.continuous_ofReal.comp hac)).mul (contDiff_zetaSq 0).continuous).mul (by fun_prop)
  · refine Eventually.of_forall fun t => ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, mixWindow_ofReal, Complex.norm_real,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mixWindowReal_nonneg L t), Complex.norm_exp]
    have hre : (-((y : ℂ) * t) * I).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one]
    have h1 := hqb t
    have h2 := hab t
    have h3 := hCZ t
    have hm := mixWindowReal_nonneg L t
    calc mixWindowReal L t * |q t| * |a t| * ‖zetaSq t‖
        ≤ mixWindowReal L t * CQ * 1 * (CZ * (1 + |t|) ^ 2) := by gcongr
      _ = CQ * CZ * (mixWindowReal L t * (1 + |t|) ^ 2) := by ring

/-- **Decomposition**: `M_r = M_Ω − M_{1−r}`. -/
theorem shiftMoment_eq_sub (L : ℝ) {q : ℝ → ℝ} (hqc : Continuous q) {CQ : ℝ}
    (hqb : ∀ t, |q t| ≤ CQ) (y : ℝ) :
    shiftMoment L q y = mixMoment L q y - defectMoment L q y := by
  have hsc : Continuous shiftFactor :=
    ((by fun_prop : Continuous fun t : ℝ => 1 / 4 + t ^ 2).div (by fun_prop)
      (fun t => by positivity)).pow 2
  have h1 := integrable_mixWindow_mul_bounded (L := L) hqc hsc hqb
    (fun t => by rw [abs_of_nonneg (shiftFactor_nonneg t)]; exact shiftFactor_le_one t) y
  have h2 := integrable_mixWindow_mul_bounded (L := L) (a := fun t => 1 - shiftFactor t) hqc
    (continuous_const.sub hsc) hqb (fun t => by
      have h0 := shiftFactor_nonneg t
      have h1 := shiftFactor_le_one t
      rw [abs_of_nonneg (by linarith)]
      linarith) y
  unfold shiftMoment defectMoment mixMoment
  rw [eq_sub_iff_add_eq, ← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  push_cast
  ring

/-- `‖ζ(½ + it)‖ ‖ζ(½ − it)‖ ≤ 36 (|t| + 3)`. -/
theorem norm_zetaSq_le_linear (t : ℝ) : ‖zetaSq t‖ ≤ 36 * (|t| + 3) := by
  have hone : ∀ τ : ℝ, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ 6 * Real.sqrt (|τ| + 3) := by
    intro τ
    set s : ℂ := ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I with hsdef
    have hre : 1 / 2 ≤ s.re := by simp [hsdef]
    have hsep : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      have hr : (s - 1).re = -(1 / 2) := by simp [hsdef]; norm_num
      rw [hr, abs_neg, abs_of_pos (by norm_num)] at this
      exact this
    have h := norm_riemannZeta_le_sqrt_norm_add_two_half hre (by norm_num : (0 : ℝ) < 1 / 2) hsep
    have hs : ‖s‖ ≤ 1 / 2 + |τ| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc ‖riemannZeta s‖ ≤ (2 + 1 / (1 / 2) + 2) * Real.sqrt (‖s‖ + 2) := h
      _ ≤ 6 * Real.sqrt (|τ| + 3) := by
          norm_num
          exact Real.sqrt_le_sqrt (by linarith)
  rw [← zetaPairC_ofReal]
  unfold zetaPairC
  rw [norm_mul]
  have h1 := hone t
  have h2 := hone (-t)
  rw [abs_neg] at h2
  have e : ((1 / 2 : ℝ) : ℂ) + -(t : ℂ) * I = ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
  rw [e]
  have hsq : Real.sqrt (|t| + 3) * Real.sqrt (|t| + 3) = |t| + 3 :=
    Real.mul_self_sqrt (by positivity)
  calc ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖
      ≤ (6 * Real.sqrt (|t| + 3)) * (6 * Real.sqrt (|t| + 3)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = 36 * (Real.sqrt (|t| + 3) * Real.sqrt (|t| + 3)) := by ring
    _ = 36 * (|t| + 3) := by rw [hsq]

/-- **The defect is uniformly small**: `‖M_{1−r}(y)‖ ≤ C/(2 + L)` for `L ≥ 0` and every `y`. -/
theorem exists_norm_defectMoment_le {q : ℝ → ℝ} {CQ : ℝ} (hqb : ∀ t, |q t| ≤ CQ) :
    ∃ C, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∀ y : ℝ, ‖defectMoment L q y‖ ≤ C / (2 + L) := by
  obtain ⟨Cm, hCm0, hCm⟩ := exists_integral_mixWindowReal_div_one_add_le
  have hCQ0 : 0 ≤ CQ := (abs_nonneg _).trans (hqb 0)
  refine ⟨540 * CQ * Cm, by positivity, fun L hL y => ?_⟩
  have hf : Continuous fun t : ℝ => (1 + |t|)⁻¹ :=
    Continuous.inv₀ (by fun_prop) (fun t => by positivity)
  have hmi : Integrable fun t => mixWindowReal L t * (1 + |t|)⁻¹ :=
    integrable_mixWindowReal_mul_of_le hf (fun t => by positivity) (fun t => by
      have h1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
      calc (1 + |t|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
        _ ≤ (1 + |t|) ^ 2 := one_le_pow₀ h1)
  have hpt : ∀ t : ℝ, ‖mixWindow L t * (q t : ℂ) * ((1 - shiftFactor t : ℝ) : ℂ) * zetaSq t *
      Complex.exp (-(y * t) * I)‖ ≤ 540 * CQ * (mixWindowReal L t * (1 + |t|)⁻¹) := by
    intro t
    rw [norm_mul, norm_mul, norm_mul, norm_mul, mixWindow_ofReal, Complex.norm_real,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mixWindowReal_nonneg L t), Complex.norm_exp,
      abs_of_nonneg (by linarith [shiftFactor_le_one t] : (0 : ℝ) ≤ 1 - shiftFactor t)]
    have hre : (-((y : ℂ) * t) * I).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one]
    have h1 := hqb t
    have h2 := one_sub_shiftFactor_le t
    have h3 := norm_zetaSq_le_linear t
    have hm := mixWindowReal_nonneg L t
    have hs0 : 0 ≤ 1 - shiftFactor t := by linarith [shiftFactor_le_one t]
    have hkey : 15 / 2 / (4 + t ^ 2) * (36 * (|t| + 3)) ≤ 540 * (1 + |t|)⁻¹ := by
      have hp : 0 < 1 + |t| := by positivity
      have h4 : 0 < 4 + t ^ 2 := by positivity
      rw [show 15 / 2 / (4 + t ^ 2) * (36 * (|t| + 3)) = 270 * (|t| + 3) / (4 + t ^ 2) by
        field_simp; ring, ← div_eq_mul_inv, div_le_div_iff₀ h4 hp]
      nlinarith [sq_abs t, abs_nonneg t, sq_nonneg (|t| - 2)]
    calc mixWindowReal L t * |q t| * (1 - shiftFactor t) * ‖zetaSq t‖
        ≤ mixWindowReal L t * CQ * (15 / 2 / (4 + t ^ 2)) * (36 * (|t| + 3)) := by gcongr
      _ = mixWindowReal L t * CQ * (15 / 2 / (4 + t ^ 2) * (36 * (|t| + 3))) := by ring
      _ ≤ mixWindowReal L t * CQ * (540 * (1 + |t|)⁻¹) := by gcongr
      _ = 540 * CQ * (mixWindowReal L t * (1 + |t|)⁻¹) := by ring
  unfold defectMoment
  refine (norm_integral_le_of_norm_le (hmi.const_mul _) (Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul]
  calc 540 * CQ * ∫ t, mixWindowReal L t * (1 + |t|)⁻¹ ≤ 540 * CQ * (Cm / (2 + L)) :=
        mul_le_mul_of_nonneg_left (hCm L hL) (by positivity)
    _ = 540 * CQ * Cm / (2 + L) := by ring

/-- **The shifted-pole moment decays past the pole without a residue**:
`‖M_r(y)‖ ≤ C (1 + L) e^{−y}` for `L, y ≥ 0`. -/
theorem exists_norm_shiftMoment_le {Q : ℂ → ℂ} (hQd : Differentiable ℂ Q) {CQ : ℝ}
    (hQb : ∀ z : ℂ, |z.im| ≤ 1 → ‖Q z‖ ≤ CQ) {q : ℝ → ℝ} (hQq : ∀ t : ℝ, Q t = q t) :
    ∃ C, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∀ y : ℝ, 0 ≤ y →
      ‖shiftMoment L q y‖ ≤ C * (1 + L) * Real.exp (-y) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ := exists_norm_weightedMixMoment_le hQd hQb hQq (R := shiftFactorC)
    (fun z h1 h2 => differentiableAt_shiftFactorC (by rw [abs_lt]; constructor <;> linarith))
    (CR := 1) (fun z h1 h2 => norm_shiftFactorC_le_one (by rw [abs_le]; constructor <;> linarith))
    (r := fun t => (shiftFactor t : ℂ)) (fun t => shiftFactorC_ofReal t)
  refine ⟨C₁, hC₁, fun L hL y hy => ?_⟩
  have e : shiftMoment L q y = ∫ t : ℝ, mixWindow L t * (q t : ℂ) *
      (fun t : ℝ => (shiftFactor t : ℂ)) t * zetaSq t * Complex.exp (-(y * t) * I) := rfl
  rw [e]
  refine (h L hL y hy).trans (le_of_eq ?_)
  rw [shiftFactorC_neg_half_I, norm_zero, mul_zero, zero_mul, add_zero]

end RHTower.ZetaNotch
