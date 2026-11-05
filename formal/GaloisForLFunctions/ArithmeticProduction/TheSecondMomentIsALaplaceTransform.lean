import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The second moment on vertical lines is a Laplace transform

Let `F` be holomorphic on a vertical strip with `C/(1+t²)` decay, and write `f_x(t) = F(½ + x + it)`.  Contour shifting gives
`𝓕f_x(ξ) = e^{2πξx} 𝓕f_0(ξ)` (`fourier_lineFun_eq`), so Plancherel gives

  `∫ |f_x|² dt = ∫ e^{4πξx} |𝓕f_0(ξ)|² dξ`  (`integral_norm_sq_lineFun_eq`):

the second moment on the line `½ + x` is the Laplace transform of one positive measure, the spectral measure of `f_0`.  In the
variable `u = −2πξ`, the frequency of a term `n^{−s}` is `u = log n`.

If the spectrum sits in `u ∈ [−B, L + B]`, the second moments at `x = ±a` control the middle line through the elementary bound
`cosh(a(L − 2u)) ≤ cosh(a(L + 2B))` (`cosh_interpolation`):

  `e^{La} ∫|f_a|² + e^{−La} ∫|f_{−a}|² ≤ 2 cosh(a(L + 2B)) ∫|f_0|² + R`,

where `R` bounds the spectrum outside the band, through `|𝓕f_0(ξ)| ≤ e^{−2πξx} ‖f_x‖₁` (`norm_fourier_lineFun_le`).
This inequality is an anti-concentration principle: a band-limited function cannot have a kink in its second-moment profile.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace GaloisForLFunctions.ArithmeticProduction

/-- The restriction of `F` to the vertical line `Re s = ½ + x`. -/
def lineFun (F : ℂ → ℂ) (x t : ℝ) : ℂ := F (((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I)

/-- Holomorphy with `C/(1+t²)` decay on the strip `½ + x₁ ≤ Re s ≤ ½ + x₂`. -/
structure StripDecay (F : ℂ → ℂ) (x₁ x₂ C : ℝ) : Prop where
  diff : ∀ s : ℂ, s.re ∈ Icc (1 / 2 + x₁) (1 / 2 + x₂) → DifferentiableAt ℂ F s
  bound : ∀ s : ℂ, s.re ∈ Icc (1 / 2 + x₁) (1 / 2 + x₂) → ‖F s‖ ≤ C / (1 + s.im ^ 2)

private theorem re_line {x : ℝ} (t : ℝ) : (((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I).re = 1 / 2 + x := by
  simp

private theorem im_line {x : ℝ} (t : ℝ) : (((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I).im = t := by
  simp

namespace StripDecay

variable {F : ℂ → ℂ} {x₁ x₂ C : ℝ} (hF : StripDecay F x₁ x₂ C)
include hF

theorem continuous_lineFun {x : ℝ} (hx : x ∈ Icc x₁ x₂) : Continuous (lineFun F x) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hd := hF.diff _ (by
    rw [re_line t]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩ :
      (((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I).re ∈ Icc (1 / 2 + x₁) (1 / 2 + x₂))
  exact ContinuousAt.comp (f := fun t : ℝ => ((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I) (g := F)
    hd.continuousAt (by fun_prop)

theorem norm_lineFun_le {x : ℝ} (hx : x ∈ Icc x₁ x₂) (t : ℝ) : ‖lineFun F x t‖ ≤ C / (1 + t ^ 2) := by
  have h := hF.bound (((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I) (by
    rw [re_line t]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  rwa [im_line t] at h

theorem C_nonneg (h : (x₁ ≤ x₂)) : 0 ≤ C := by
  have h1 := hF.norm_lineFun_le (x := x₁) ⟨le_rfl, h⟩ 0
  have h2 := norm_nonneg (lineFun F x₁ 0)
  simpa using h2.trans h1

theorem integrable_lineFun {x : ℝ} (hx : x ∈ Icc x₁ x₂) : Integrable (lineFun F x) := by
  have hb : Integrable fun t : ℝ => C * (1 + t ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul C
  refine Integrable.mono' hb (hF.continuous_lineFun hx).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [← div_eq_mul_inv]
  exact hF.norm_lineFun_le hx t

theorem memLp_two_lineFun {x : ℝ} (hx : x ∈ Icc x₁ x₂) : MemLp (lineFun F x) 2 := by
  rw [memLp_two_iff_integrable_sq_norm (hF.continuous_lineFun hx).aestronglyMeasurable]
  have hC : 0 ≤ C := hF.C_nonneg (hx.1.trans hx.2)
  have hb : Integrable fun t : ℝ => C ^ 2 * (1 + t ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hb
    (((hF.continuous_lineFun hx).norm.pow 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 := hF.norm_lineFun_le hx t
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hle1 : (1 + t ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t])
  calc ‖lineFun F x t‖ ^ 2 ≤ (C * (1 + t ^ 2)⁻¹) ^ 2 := by
        rw [← div_eq_mul_inv]
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = C ^ 2 * (1 + t ^ 2)⁻¹ * (1 + t ^ 2)⁻¹ := by ring
    _ ≤ C ^ 2 * (1 + t ^ 2)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hle1 (by positivity)
    _ = C ^ 2 * (1 + t ^ 2)⁻¹ := mul_one _

/-- **Contour shift of the Fourier transform.** -/
theorem fourier_lineFun_eq {x : ℝ} (hx : x ∈ Icc x₁ x₂) (h0 : (0 : ℝ) ∈ Icc x₁ x₂) (ξ : ℝ) :
    𝓕 (lineFun F x) ξ =
      ((Real.exp (2 * Real.pi * ξ * x) : ℝ) : ℂ) * 𝓕 (lineFun F 0) ξ := by
  set Φ : ℂ → ℂ := fun s => F s * Complex.exp (-(2 * Real.pi * ξ : ℝ) * (s - 1 / 2)) with hΦ
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = |x₁| + |x₂| := ⟨_, rfl⟩
  have hsub : ∀ s : ℂ, s.re ∈ uIcc (1 / 2 + x : ℝ) (1 / 2 + 0) →
      s.re ∈ Icc (1 / 2 + x₁) (1 / 2 + x₂) := by
    intro s hs
    rcases Set.mem_uIcc.mp hs with h | h
    · exact ⟨by linarith [h.1, hx.1], by linarith [h.2, h0.2]⟩
    · exact ⟨by linarith [h.1, h0.1], by linarith [h.2, hx.2]⟩
  have hd : ∀ s : ℂ, s.re ∈ uIcc (1 / 2 + x : ℝ) (1 / 2 + 0) → DifferentiableAt ℂ Φ s := by
    intro s hs
    exact (hF.diff s (hsub s hs)).mul (by fun_prop)
  have hC : 0 ≤ C := hF.C_nonneg (h0.1.trans h0.2)
  have hb : ∀ s : ℂ, s.re ∈ uIcc (1 / 2 + x : ℝ) (1 / 2 + 0) →
      ‖Φ s‖ ≤ (C * Real.exp (2 * Real.pi * |ξ| * X)) / (1 + s.im ^ 2) := by
    intro s hs
    have hs' := hsub s hs
    have hnorm : ‖Complex.exp (-(2 * Real.pi * ξ : ℝ) * (s - 1 / 2))‖ ≤
        Real.exp (2 * Real.pi * |ξ| * X) := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have hre : (-(2 * Real.pi * ξ : ℝ) * (s - 1 / 2) : ℂ).re =
          -(2 * Real.pi * ξ) * (s.re - 1 / 2) := by
        simp [Complex.mul_re]
      rw [hre]
      have hb1 : |s.re - 1 / 2| ≤ X := by
        rw [hX, abs_le]
        constructor
        · linarith [hs'.1, neg_abs_le x₁, abs_nonneg x₂]
        · linarith [hs'.2, le_abs_self x₂, abs_nonneg x₁]
      have hpi := Real.pi_pos
      calc -(2 * Real.pi * ξ) * (s.re - 1 / 2) ≤ |-(2 * Real.pi * ξ) * (s.re - 1 / 2)| :=
            le_abs_self _
        _ = 2 * Real.pi * |ξ| * |s.re - 1 / 2| := by
            rw [abs_mul, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
        _ ≤ 2 * Real.pi * |ξ| * X := mul_le_mul_of_nonneg_left hb1 (by positivity)
    calc ‖Φ s‖ = ‖F s‖ * ‖Complex.exp (-(2 * Real.pi * ξ : ℝ) * (s - 1 / 2))‖ := norm_mul _ _
      _ ≤ (C / (1 + s.im ^ 2)) * Real.exp (2 * Real.pi * |ξ| * X) :=
        mul_le_mul (hF.bound s hs') hnorm (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hshift := GaloisForLFunctions.HTGeometry.integral_vertical_line_shift_of_decay hd hb
  have hline : ∀ y : ℝ, ∀ t : ℝ, Φ (((1 / 2 + y : ℝ) : ℂ) + (t : ℂ) * I) =
      ((Real.exp (-(2 * Real.pi * ξ * y)) : ℝ) : ℂ) *
        (Real.fourierChar (-(t * ξ)) • lineFun F y t) := by
    intro y t
    simp only [hΦ, lineFun, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
    have hexp : Complex.exp (-(2 * Real.pi * ξ : ℝ) * (((1 / 2 + y : ℝ) : ℂ) + (t : ℂ) * I - 1 / 2)) =
        ((Real.exp (-(2 * Real.pi * ξ * y)) : ℝ) : ℂ) *
          Complex.exp (((2 * Real.pi * (-(t * ξ)) : ℝ) : ℂ) * I) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  simp_rw [hline] at hshift
  rw [integral_const_mul, integral_const_mul] at hshift
  simp only [mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul] at hshift
  simp only [Real.fourier_real_eq]
  rw [← hshift, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  simp

/-- `|𝓕f_0(ξ)| ≤ e^{−2πξx} ‖f_x‖₁`: the bound that localizes the spectrum. -/
theorem norm_fourier_lineFun_le {x : ℝ} (hx : x ∈ Icc x₁ x₂) (h0 : (0 : ℝ) ∈ Icc x₁ x₂) (ξ : ℝ) :
    ‖𝓕 (lineFun F 0) ξ‖ ≤ Real.exp (-(2 * Real.pi * ξ * x)) * ∫ t, ‖lineFun F x t‖ := by
  have h := hF.fourier_lineFun_eq hx h0 ξ
  have hE := Real.exp_pos (2 * Real.pi * ξ * x)
  have hle : ‖𝓕 (lineFun F x) ξ‖ ≤ ∫ t, ‖lineFun F x t‖ := by
    rw [Real.fourier_real_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Circle.norm_smul]
  have hval : ‖𝓕 (lineFun F 0) ξ‖ = Real.exp (-(2 * Real.pi * ξ * x)) * ‖𝓕 (lineFun F x) ξ‖ := by
    rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg hE.le, ← mul_assoc, ← Real.exp_add]
    simp
  rw [hval]
  exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

/-- **Plancherel on a line.** -/
theorem integral_norm_sq_lineFun_eq {x : ℝ} (hx : x ∈ Icc x₁ x₂) (h0 : (0 : ℝ) ∈ Icc x₁ x₂) :
    ∫ t, ‖lineFun F x t‖ ^ 2 = ∫ ξ, Real.exp (4 * Real.pi * ξ * x) * ‖𝓕 (lineFun F 0) ξ‖ ^ 2 := by
  rw [← GaloisForLFunctions.HTGeometry.integral_norm_sq_fourier (hF.integrable_lineFun hx)
    (hF.memLp_two_lineFun hx)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [hF.fourier_lineFun_eq hx h0 ξ, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

end StripDecay

/-- The transform of an `L¹ ∩ L²` function is `L²`. -/
theorem integrable_norm_sq_fourier {φ : ℝ → ℂ} (hφ : Integrable φ) (hφ2 : MemLp φ 2) :
    Integrable fun ξ => ‖𝓕 φ ξ‖ ^ 2 := by
  have hP := GaloisForLFunctions.HTGeometry.integral_norm_sq_fourier hφ hφ2
  by_cases h0 : ∫ x, ‖φ x‖ ^ 2 = 0
  · have hae : φ =ᵐ[volume] 0 := by
      have hnn : 0 ≤ᵐ[volume] fun u => ‖φ u‖ ^ 2 :=
        Filter.Eventually.of_forall fun u => by positivity
      have hi : Integrable (fun u => ‖φ u‖ ^ 2) := by
        rw [← memLp_two_iff_integrable_sq_norm hφ.aestronglyMeasurable]
        exact hφ2
      have := (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp h0
      exact this.mono fun u hu => by simpa using hu
    have hF0 : ∀ ξ, 𝓕 φ ξ = 0 := by
      intro ξ
      rw [Real.fourier_real_eq]
      have h0' : (fun v : ℝ => Real.fourierChar (-(v * ξ)) • φ v) =ᵐ[volume] fun _ => (0 : ℂ) :=
        hae.mono fun u hu => by simp [hu]
      rw [integral_congr_ae h0', integral_zero]
    simp [hF0]
  · by_contra hni
    rw [integral_undef hni] at hP
    exact h0 hP.symm

/-- **The cosh interpolation inequality.**  A spectrum in `u ∈ [−B, L + B]` forces
`e^{La} ∫|f_a|² + e^{−La} ∫|f_{−a}|² ≤ 2 cosh(a(L + 2B)) ∫|f_0|² + R`. -/
theorem cosh_interpolation {F : ℂ → ℂ} {x₁ x₂ C : ℝ} (hF : StripDecay F x₁ x₂ C) (hx₁ : x₁ < 0)
    (hx₂ : 0 < x₂) {a L B : ℝ} (ha : 0 < a) (ha₁ : a < -x₁) (ha₂ : a < x₂) (hL : 0 ≤ L)
    (hB : 0 ≤ B) :
    Real.exp (L * a) * (∫ t, ‖lineFun F a t‖ ^ 2) +
        Real.exp (-(L * a)) * (∫ t, ‖lineFun F (-a) t‖ ^ 2) ≤
      2 * Real.cosh (a * (L + 2 * B)) * (∫ t, ‖lineFun F 0 t‖ ^ 2) +
        ((∫ t, ‖lineFun F x₂ t‖) ^ 2 * Real.exp (L * a) * Real.exp (-(2 * B * (x₂ - a))) /
            (2 * Real.pi * (x₂ - a)) +
          (∫ t, ‖lineFun F x₁ t‖) ^ 2 * Real.exp (-(L * a)) *
              Real.exp (-(2 * (L + B) * (-x₁ - a))) / (2 * Real.pi * (-x₁ - a))) := by
  have h0 : (0 : ℝ) ∈ Icc x₁ x₂ := ⟨hx₁.le, hx₂.le⟩
  have hap : a ∈ Icc x₁ x₂ := ⟨by linarith, ha₂.le⟩
  have ham : -a ∈ Icc x₁ x₂ := ⟨by linarith, by linarith⟩
  have hx₂m : x₂ ∈ Icc x₁ x₂ := ⟨by linarith, le_rfl⟩
  have hx₁m : x₁ ∈ Icc x₁ x₂ := ⟨le_rfl, by linarith⟩
  have hpi := Real.pi_pos
  set N₂ := ∫ t, ‖lineFun F x₂ t‖ with hN₂
  set N₁ := ∫ t, ‖lineFun F x₁ t‖ with hN₁
  have hN₂0 : 0 ≤ N₂ := integral_nonneg fun t => norm_nonneg _
  have hN₁0 : 0 ≤ N₁ := integral_nonneg fun t => norm_nonneg _
  set G : ℝ → ℝ := fun ξ => ‖𝓕 (lineFun F 0) ξ‖ ^ 2 with hG
  have hGint : Integrable G :=
    integrable_norm_sq_fourier (hF.integrable_lineFun h0) (hF.memLp_two_lineFun h0)
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun ξ => by positivity
  have hval0 : ∫ t, ‖lineFun F 0 t‖ ^ 2 = ∫ ξ, G ξ :=
    (GaloisForLFunctions.HTGeometry.integral_norm_sq_fourier (hF.integrable_lineFun h0)
      (hF.memLp_two_lineFun h0)).symm
  -- the integrable weighted spectra at `±a`
  have hint : ∀ {x : ℝ}, x ∈ Icc x₁ x₂ →
      Integrable fun ξ => Real.exp (4 * Real.pi * ξ * x) * G ξ := by
    intro x hx
    have h := integrable_norm_sq_fourier (hF.integrable_lineFun hx) (hF.memLp_two_lineFun hx)
    refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hG]
    rw [hF.fourier_lineFun_eq hx h0 ξ, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  -- the remainder
  set c₂ := x₂ - a with hc₂
  set c₁ := -x₁ - a with hc₁
  have hc₂0 : 0 < c₂ := by rw [hc₂]; linarith
  have hc₁0 : 0 < c₁ := by rw [hc₁]; linarith
  set ξ₂ : ℝ := B / (2 * Real.pi) with hξ₂
  set ξ₁ : ℝ := -(L + B) / (2 * Real.pi) with hξ₁
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hξ₂0 : 0 ≤ ξ₂ := by rw [hξ₂]; positivity
  have hξ₁0 : ξ₁ ≤ 0 := by
    rw [hξ₁]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have h4ξ₂ : 4 * Real.pi * ξ₂ = 2 * B := by
    rw [hξ₂]
    field_simp
    ring
  have h4ξ₁ : 4 * Real.pi * ξ₁ = -(2 * (L + B)) := by
    rw [hξ₁]
    field_simp
    ring
  set Rem₂ : ℝ → ℝ := (Ioi ξ₂).indicator fun ξ =>
    2 * N₂ ^ 2 * Real.exp (L * a) * Real.exp ((-(4 * Real.pi * c₂)) * ξ) with hRem₂
  set Rem₁ : ℝ → ℝ := (Iio ξ₁).indicator fun ξ =>
    2 * N₁ ^ 2 * Real.exp (-(L * a)) * Real.exp ((4 * Real.pi * c₁) * ξ) with hRem₁
  have hRem₂int : Integrable Rem₂ := by
    rw [hRem₂, integrable_indicator_iff measurableSet_Ioi]
    have h := (integrableOn_exp_mul_Ioi (a := -(4 * Real.pi * c₂)) (by
      have : 0 < 4 * Real.pi * c₂ := by positivity
      linarith) ξ₂)
    exact h.const_mul _
  have hRem₁int : Integrable Rem₁ := by
    rw [hRem₁, integrable_indicator_iff measurableSet_Iio]
    have h := (integrableOn_exp_mul_Iic (a := 4 * Real.pi * c₁) (by positivity) ξ₁)
    exact IntegrableOn.mono_set (h.const_mul _) Iio_subset_Iic_self
  have hRem₂val : ∫ ξ, Rem₂ ξ =
      N₂ ^ 2 * Real.exp (L * a) * Real.exp (-(2 * B * c₂)) / (2 * Real.pi * c₂) := by
    rw [hRem₂, integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_exp_mul_Ioi (by
        have : 0 < 4 * Real.pi * c₂ := by positivity
        linarith) ξ₂]
    have hexp : -(4 * Real.pi * c₂) * ξ₂ = -(2 * B * c₂) := by
      have : 4 * Real.pi * c₂ * ξ₂ = (4 * Real.pi * ξ₂) * c₂ := by ring
      rw [neg_mul, this, h4ξ₂]
    rw [hexp]
    field_simp
    ring
  have hRem₁val : ∫ ξ, Rem₁ ξ =
      N₁ ^ 2 * Real.exp (-(L * a)) * Real.exp (-(2 * (L + B) * c₁)) / (2 * Real.pi * c₁) := by
    rw [hRem₁, integral_indicator measurableSet_Iio, integral_const_mul,
      ← integral_Iic_eq_integral_Iio, integral_exp_mul_Iic (by positivity) ξ₁]
    have hexp : 4 * Real.pi * c₁ * ξ₁ = -(2 * (L + B) * c₁) := by
      have : 4 * Real.pi * c₁ * ξ₁ = (4 * Real.pi * ξ₁) * c₁ := by ring
      rw [this, h4ξ₁]
      ring
    rw [hexp]
    field_simp
    ring
  -- the spectrum outside the band
  have hbound₂ : ∀ ξ, G ξ ≤ N₂ ^ 2 * Real.exp (-(4 * Real.pi * ξ * x₂)) := by
    intro ξ
    have h := hF.norm_fourier_lineFun_le hx₂m h0 ξ
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    refine h2.trans (le_of_eq ?_)
    rw [mul_pow, ← Real.exp_nat_mul, mul_comm]
    congr 2
    push_cast
    ring
  have hbound₁ : ∀ ξ, G ξ ≤ N₁ ^ 2 * Real.exp (4 * Real.pi * ξ * -x₁) := by
    intro ξ
    have h := hF.norm_fourier_lineFun_le hx₁m h0 ξ
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    refine h2.trans (le_of_eq ?_)
    rw [mul_pow, ← Real.exp_nat_mul, mul_comm]
    congr 2
    push_cast
    ring
  -- the pointwise inequality
  set W : ℝ → ℝ := fun ξ => Real.exp (L * a) * Real.exp (4 * Real.pi * ξ * a) +
    Real.exp (-(L * a)) * Real.exp (4 * Real.pi * ξ * -a) with hW
  have hWcosh : ∀ ξ, W ξ = 2 * Real.cosh (a * (L + 4 * Real.pi * ξ)) := by
    intro ξ
    simp only [hW]
    rw [Real.cosh_eq, ← Real.exp_add, ← Real.exp_add]
    have h1 : L * a + 4 * Real.pi * ξ * a = a * (L + 4 * Real.pi * ξ) := by ring
    have h2 : -(L * a) + 4 * Real.pi * ξ * -a = -(a * (L + 4 * Real.pi * ξ)) := by ring
    rw [h1, h2]
    ring
  have hcoshpos : 0 ≤ 2 * Real.cosh (a * (L + 2 * B)) := by
    have := Real.cosh_pos (a * (L + 2 * B))
    positivity
  have hRem₂0 : ∀ ξ, 0 ≤ Rem₂ ξ := by
    intro ξ
    rw [hRem₂]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _
  have hRem₁0 : ∀ ξ, 0 ≤ Rem₁ ξ := by
    intro ξ
    rw [hRem₁]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _
  have hpoint : ∀ ξ, W ξ * G ξ ≤ 2 * Real.cosh (a * (L + 2 * B)) * G ξ + (Rem₂ ξ + Rem₁ ξ) := by
    intro ξ
    by_cases h2 : ξ₂ < ξ
    · -- right of the band
      have hval : Rem₂ ξ = 2 * N₂ ^ 2 * Real.exp (L * a) * Real.exp ((-(4 * Real.pi * c₂)) * ξ) := by
        rw [hRem₂, Set.indicator_of_mem (show ξ ∈ Ioi ξ₂ from h2)]
      have hξpos : 0 ≤ ξ := hξ₂0.trans h2.le
      have hWle : W ξ ≤ 2 * Real.exp (L * a + 4 * Real.pi * ξ * a) := by
        simp only [hW]
        rw [Real.exp_add]
        have h3 : Real.exp (-(L * a)) * Real.exp (4 * Real.pi * ξ * -a) ≤
            Real.exp (L * a) * Real.exp (4 * Real.pi * ξ * a) := by
          rw [← Real.exp_add, ← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          have : 0 ≤ L * a := by positivity
          have : 0 ≤ 4 * Real.pi * ξ * a := by positivity
          linarith
        linarith
      have hstep : W ξ * G ξ ≤ Rem₂ ξ := by
        rw [hval]
        calc W ξ * G ξ ≤ (2 * Real.exp (L * a + 4 * Real.pi * ξ * a)) *
              (N₂ ^ 2 * Real.exp (-(4 * Real.pi * ξ * x₂))) :=
              mul_le_mul hWle (hbound₂ ξ) (hG0 ξ) (by positivity)
          _ = 2 * N₂ ^ 2 * Real.exp (L * a) * Real.exp ((-(4 * Real.pi * c₂)) * ξ) := by
              have hsplit : Real.exp (L * a + 4 * Real.pi * ξ * a) * Real.exp (-(4 * Real.pi * ξ * x₂)) =
                  Real.exp (L * a) * Real.exp ((-(4 * Real.pi * c₂)) * ξ) := by
                rw [← Real.exp_add, ← Real.exp_add]
                congr 1
                rw [hc₂]
                ring
              calc _ = 2 * N₂ ^ 2 * (Real.exp (L * a + 4 * Real.pi * ξ * a) *
                    Real.exp (-(4 * Real.pi * ξ * x₂))) := by ring
                _ = _ := by rw [hsplit]; ring
      have := mul_nonneg hcoshpos (hG0 ξ)
      linarith [hRem₁0 ξ]
    · by_cases h1 : ξ < ξ₁
      · -- left of the band
        have hval : Rem₁ ξ = 2 * N₁ ^ 2 * Real.exp (-(L * a)) * Real.exp ((4 * Real.pi * c₁) * ξ) := by
          rw [hRem₁, Set.indicator_of_mem (show ξ ∈ Iio ξ₁ from h1)]
        have hξneg : ξ ≤ 0 := h1.le.trans hξ₁0
        have h4ξ : 4 * Real.pi * ξ ≤ -(2 * (L + B)) := by
          rw [← h4ξ₁]
          exact mul_le_mul_of_nonneg_left h1.le (by positivity)
        have hWle : W ξ ≤ 2 * Real.exp (-(L * a) + 4 * Real.pi * ξ * -a) := by
          simp only [hW]
          rw [Real.exp_add]
          have h3 : Real.exp (L * a) * Real.exp (4 * Real.pi * ξ * a) ≤
              Real.exp (-(L * a)) * Real.exp (4 * Real.pi * ξ * -a) := by
            rw [← Real.exp_add, ← Real.exp_add]
            refine Real.exp_le_exp.mpr ?_
            nlinarith
          linarith
        have hstep : W ξ * G ξ ≤ Rem₁ ξ := by
          rw [hval]
          calc W ξ * G ξ ≤ (2 * Real.exp (-(L * a) + 4 * Real.pi * ξ * -a)) *
                (N₁ ^ 2 * Real.exp (4 * Real.pi * ξ * -x₁)) :=
                mul_le_mul hWle (hbound₁ ξ) (hG0 ξ) (by positivity)
            _ = 2 * N₁ ^ 2 * Real.exp (-(L * a)) * Real.exp ((4 * Real.pi * c₁) * ξ) := by
                have hsplit : Real.exp (-(L * a) + 4 * Real.pi * ξ * -a) *
                      Real.exp (4 * Real.pi * ξ * -x₁) =
                    Real.exp (-(L * a)) * Real.exp ((4 * Real.pi * c₁) * ξ) := by
                  rw [← Real.exp_add, ← Real.exp_add]
                  congr 1
                  rw [hc₁]
                  ring
                calc _ = 2 * N₁ ^ 2 * (Real.exp (-(L * a) + 4 * Real.pi * ξ * -a) *
                      Real.exp (4 * Real.pi * ξ * -x₁)) := by ring
                  _ = _ := by rw [hsplit]; ring
        have := mul_nonneg hcoshpos (hG0 ξ)
        linarith [hRem₂0 ξ]
      · -- inside the band
        have hξ2 : ξ ≤ ξ₂ := not_lt.mp h2
        have hξ1 : ξ₁ ≤ ξ := not_lt.mp h1
        have hup : 4 * Real.pi * ξ ≤ 2 * B := by
          rw [← h4ξ₂]
          exact mul_le_mul_of_nonneg_left hξ2 (by positivity)
        have hlo : -(2 * (L + B)) ≤ 4 * Real.pi * ξ := by
          rw [← h4ξ₁]
          exact mul_le_mul_of_nonneg_left hξ1 (by positivity)
        have hcosh : Real.cosh (a * (L + 4 * Real.pi * ξ)) ≤ Real.cosh (a * (L + 2 * B)) := by
          rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos ha]
          refine mul_le_mul_of_nonneg_left ?_ ha.le
          rw [abs_le]
          have hpos : 0 ≤ L + 2 * B := by positivity
          rw [abs_of_nonneg hpos]
          constructor <;> linarith
        rw [hWcosh]
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcosh (by norm_num : (0 : ℝ) ≤ 2)) (hG0 ξ)
        linarith [hRem₁0 ξ, hRem₂0 ξ]
  -- integrate
  have hWint : Integrable fun ξ => W ξ * G ξ := by
    have h1 := (hint hap).const_mul (Real.exp (L * a))
    have h2 := (hint ham).const_mul (Real.exp (-(L * a)))
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hW, Pi.add_apply]
    ring
  have hmain := integral_mono hWint
    ((hGint.const_mul (2 * Real.cosh (a * (L + 2 * B)))).add (hRem₂int.add hRem₁int)) hpoint
  have hRHS : ∫ ξ, (2 * Real.cosh (a * (L + 2 * B)) * G ξ + (Rem₂ ξ + Rem₁ ξ)) =
      2 * Real.cosh (a * (L + 2 * B)) * (∫ ξ, G ξ) + ((∫ ξ, Rem₂ ξ) + ∫ ξ, Rem₁ ξ) := by
    have hR : Integrable fun ξ => Rem₂ ξ + Rem₁ ξ := hRem₂int.add hRem₁int
    rw [integral_add (hGint.const_mul _) hR, integral_const_mul, integral_add hRem₂int hRem₁int]
  have hLHS : ∫ ξ, W ξ * G ξ = Real.exp (L * a) * (∫ t, ‖lineFun F a t‖ ^ 2) +
      Real.exp (-(L * a)) * ∫ t, ‖lineFun F (-a) t‖ ^ 2 := by
    rw [hF.integral_norm_sq_lineFun_eq hap h0, hF.integral_norm_sq_lineFun_eq ham h0,
      ← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hint hap).const_mul _) ((hint ham).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hW, hG]
    ring
  have hmain' : ∫ ξ, W ξ * G ξ ≤
      ∫ ξ, (2 * Real.cosh (a * (L + 2 * B)) * G ξ + (Rem₂ ξ + Rem₁ ξ)) := hmain
  rw [hLHS, hRHS, hRem₂val, hRem₁val, ← hval0] at hmain'
  exact hmain'

end GaloisForLFunctions.ArithmeticProduction
