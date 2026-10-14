import GaloisForLFunctions.RHTower.WeilConeXiDivisibleBlindTest
import GaloisForLFunctions.RHTower.StripHorizontalShift

/-!
# `Ξ`-divisible prime-blind tests from strip functions

Let `Φ` be holomorphic on the closed strip `|Im z| ≤ b` with `b > ½`, with
`‖Φ(z)‖ ≤ C e^{−ε|Re z|}` there (`StripDecay`), and with `Φ(−r) = conj Φ(r)` for real `r`.  Its inverse
Fourier transform

`F(x) = (1/2π) ∫ Φ(r) e^{−irx} dr`   (`stripTest`)

is a real `C²` test, and:

* `|F(x)|, |F'(x)| ≤ K e^{−b|x|}` (`norm_stripInvFT_le`): shift the line of integration to
  `Im z = −b` for `x ≥ 0` and to `Im z = b` for `x ≤ 0`; the derivative is the transform of `−izΦ(z)`,
  which satisfies the same hypotheses with `ε/2`;
* `F̂(z) = ∫ F(u) e^{izu} du = Φ(z)` on the open strip `|Im z| < b` (`paperFT_stripTest`): Fourier
  inversion on `ℝ`, analyticity of `F̂` on the strip from the decay of `F`, and the identity theorem;
* `(F ⋆ F̃)(y) = ∫ F(t) F(t − y) dt = (1/2π) ∫ |Φ(r)|² cos(ry) dr` (`crossCorr_stripTest`), by Fubini.

**Theorem** (`xiDivisibleBlindTest_stripTest`).  If moreover `Φ = Ξ·g` on `|Im z| ≤ ½` with `g` zero-free
on `ℝ`, and `∫ |Φ(r)|² cos(r log n) dr = 0` for every `n ≥ 2`, then `F` is a `Ξ`-divisible prime-blind
test.  Consequently RH is equivalent to prime-blind positivity
(`riemannHypothesis_iff_primeBlindPositive_of_stripFactor`).

So the (N1) problem is the existence of a strip function `Φ = Ξ·g` of exponential decay whose spectral
square `|Φ|²` has vanishing cosine moments at every `log n`, `n ≥ 2`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate FourierTransform

noncomputable section

namespace RHTower.WeilSpectral

/-- Holomorphy on the closed strip `|Im z| ≤ b` with real-direction decay `C e^{−ε|Re z|}`. -/
structure StripDecay (Φ : ℂ → ℂ) (b ε C : ℝ) : Prop where
  diff : ∀ z : ℂ, |z.im| ≤ b → DifferentiableAt ℂ Φ z
  bound : ∀ z : ℂ, |z.im| ≤ b → ‖Φ z‖ ≤ C * Real.exp (-(ε * |z.re|))

theorem StripDecay.const_nonneg {Φ : ℂ → ℂ} {b ε C : ℝ} (hΦ : StripDecay Φ b ε C) (hb : 0 ≤ b) :
    0 ≤ C := by
  have h := hΦ.bound 0 (by simpa using hb)
  simp only [Complex.zero_re, abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
  exact (norm_nonneg _).trans h

/-- `t e^{−εt} ≤ (2/ε) e^{−εt/2}` for `t ≥ 0`. -/
theorem mul_exp_neg_le {ε t : ℝ} (hε : 0 < ε) :
    t * Real.exp (-(ε * t)) ≤ 2 / ε * Real.exp (-(ε / 2 * t)) := by
  have h1 : ε / 2 * t ≤ Real.exp (ε / 2 * t) := by
    linarith [Real.add_one_le_exp (ε / 2 * t)]
  have h2 : Real.exp (-(ε * t)) = Real.exp (-(ε / 2 * t)) * Real.exp (-(ε / 2 * t)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : t * Real.exp (-(ε / 2 * t)) ≤ 2 / ε := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hε]
    nlinarith [Real.exp_pos (ε / 2 * t)]
  rw [h2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le

/-- Multiplication by `z` keeps the strip hypotheses at half the decay rate. -/
theorem StripDecay.mul_id {Φ : ℂ → ℂ} {b ε C : ℝ} (hΦ : StripDecay Φ b ε C) (hb : 0 ≤ b)
    (hε : 0 < ε) : StripDecay (fun z => z * Φ z) b (ε / 2) (C * (2 / ε + b)) := by
  have hC := hΦ.const_nonneg hb
  refine ⟨fun z hz => differentiableAt_id.mul (hΦ.diff z hz), fun z hz => ?_⟩
  rw [norm_mul]
  have hz1 : ‖z‖ ≤ |z.re| + b := (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have hm := mul_exp_neg_le (t := |z.re|) hε
  have he : Real.exp (-(ε * |z.re|)) ≤ Real.exp (-(ε / 2 * |z.re|)) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.re])
  calc ‖z‖ * ‖Φ z‖ ≤ (|z.re| + b) * (C * Real.exp (-(ε * |z.re|))) :=
        mul_le_mul hz1 (hΦ.bound z hz) (norm_nonneg _) (by positivity)
    _ = C * (|z.re| * Real.exp (-(ε * |z.re|)) + b * Real.exp (-(ε * |z.re|))) := by ring
    _ ≤ C * (2 / ε * Real.exp (-(ε / 2 * |z.re|)) + b * Real.exp (-(ε / 2 * |z.re|))) := by
        gcongr
    _ = C * (2 / ε + b) * Real.exp (-(ε / 2 * |z.re|)) := by ring

/-- The inverse Fourier transform `(1/2π) ∫ Φ(r) e^{−irx} dr`. -/
def stripInvFT (Φ : ℂ → ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Φ r * cexp (-(I * r * x))

/-- The real test attached to a strip function. -/
def stripTest (Φ : ℂ → ℂ) (x : ℝ) : ℝ := (stripInvFT Φ x).re

theorem continuous_ofReal_comp_of_stripDecay {Φ : ℂ → ℂ} {b ε C : ℝ} (hΦ : StripDecay Φ b ε C)
    (hb : 0 ≤ b) : Continuous fun r : ℝ => Φ r := by
  rw [continuous_iff_continuousAt]
  intro r
  exact (hΦ.diff r (by simpa using hb)).continuousAt.comp Complex.continuous_ofReal.continuousAt

theorem norm_cexp_neg_I_mul (z : ℂ) (x : ℝ) : ‖cexp (-(I * z * x))‖ = Real.exp (z.im * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- Lower horizontal contour shift on a symmetric strip. -/
theorem integral_horizontal_shift_lower {G : ℂ → ℂ} {c C r : ℝ} (hc : 0 ≤ c) (hr : 0 < r)
    (hG : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ G z)
    (hbound : ∀ z : ℂ, |z.im| ≤ c → ‖G z‖ ≤ C * Real.exp (-(r * |z.re|))) :
    (∫ x : ℝ, G ((x : ℂ) - (c : ℂ) * I)) = ∫ x : ℝ, G (x : ℂ) := by
  set H : ℂ → ℂ := fun z => G (-z) with hH
  have hHd : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ H z := fun z hz =>
    (hG (-z) (by simpa using hz)).comp z (by fun_prop)
  have hHb : ∀ z : ℂ, |z.im| ≤ c → ‖H z‖ ≤ C * Real.exp (-(r * |z.re|)) := fun z hz => by
    simpa [hH] using hbound (-z) (by simpa using hz)
  have hshift := RHTower.integral_horizontal_shift_of_decay hc hr hHd hHb
  have hleft : (∫ x : ℝ, H ((x : ℂ) + (c : ℂ) * I)) = ∫ x : ℝ, G ((x : ℂ) - (c : ℂ) * I) := by
    rw [← integral_neg_eq_self (fun x : ℝ => G ((x : ℂ) - (c : ℂ) * I)) volume]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hH]
    congr 1
    push_cast
    ring
  have hright : (∫ x : ℝ, H (x : ℂ)) = ∫ x : ℝ, G (x : ℂ) := by
    simpa [hH] using integral_neg_eq_self (fun x : ℝ => G (x : ℂ)) volume
  rw [← hleft, hshift, hright]

/-- **Exponential decay of the inverse transform.** -/
theorem norm_stripInvFT_le {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) (x : ℝ) :
    ‖stripInvFT Φ x‖ ≤
      C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi) * Real.exp (-(b * |x|)) := by
  have hC := hΦ.const_nonneg hb
  set G : ℂ → ℂ := fun z => Φ z * cexp (-(I * z * x)) with hGdef
  have hGd : ∀ z : ℂ, |z.im| ≤ b → DifferentiableAt ℂ G z := fun z hz =>
    (hΦ.diff z hz).mul (by fun_prop)
  have hGb : ∀ z : ℂ, |z.im| ≤ b →
      ‖G z‖ ≤ (C * Real.exp (b * |x|)) * Real.exp (-(ε * |z.re|)) := by
    intro z hz
    rw [hGdef]
    simp only
    rw [norm_mul, norm_cexp_neg_I_mul]
    have h1 : Real.exp (z.im * x) ≤ Real.exp (b * |x|) := by
      apply Real.exp_le_exp.mpr
      calc z.im * x ≤ |z.im * x| := le_abs_self _
        _ = |z.im| * |x| := abs_mul _ _
        _ ≤ b * |x| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
    calc ‖Φ z‖ * Real.exp (z.im * x) ≤ (C * Real.exp (-(ε * |z.re|))) * Real.exp (b * |x|) :=
          mul_le_mul (hΦ.bound z hz) h1 (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hI := RHTower.integrable_exp_neg_mul_abs' hε
  have hline : ∀ (y : ℝ), |y| ≤ b → (∀ r : ℝ, ‖G ((r : ℂ) + (y : ℂ) * I)‖ ≤
      C * Real.exp (-(ε * |r|)) * Real.exp (y * x)) := by
    intro y hy r
    have hz : |((r : ℂ) + (y : ℂ) * I).im| ≤ b := by simpa using hy
    rw [hGdef]
    simp only
    rw [norm_mul, norm_cexp_neg_I_mul]
    have := hΦ.bound _ hz
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      zero_add] at this ⊢
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hnorm : ∀ y : ℝ, |y| ≤ b → y * x = -(b * |x|) →
      ‖∫ r : ℝ, G ((r : ℂ) + (y : ℂ) * I)‖ ≤
        C * (∫ r : ℝ, Real.exp (-(ε * |r|))) * Real.exp (-(b * |x|)) := by
    intro y hy hyx
    refine (norm_integral_le_of_norm_le ((hI.const_mul C).mul_const (Real.exp (y * x)))
      (Eventually.of_forall (hline y hy))).trans (le_of_eq ?_)
    rw [integral_mul_const, integral_const_mul, hyx]
  have hval : ‖∫ r : ℝ, Φ r * cexp (-(I * r * x))‖ ≤
      C * (∫ r : ℝ, Real.exp (-(ε * |r|))) * Real.exp (-(b * |x|)) := by
    rcases le_total 0 x with hx | hx
    · have hs := integral_horizontal_shift_lower hb hε hGd hGb
      have e : (∫ r : ℝ, Φ r * cexp (-(I * r * x))) = ∫ r : ℝ, G ((r : ℂ) + ((-b : ℝ) : ℂ) * I) := by
        rw [← hs]
        refine integral_congr_ae (Eventually.of_forall fun r => ?_)
        simp only [hGdef]
        push_cast
        ring_nf
      rw [e]
      exact hnorm (-b) (by rw [abs_neg, abs_of_nonneg hb]) (by rw [abs_of_nonneg hx]; ring)
    · have hs := RHTower.integral_horizontal_shift_of_decay hb hε hGd hGb
      have e : (∫ r : ℝ, Φ r * cexp (-(I * r * x))) = ∫ r : ℝ, G ((r : ℂ) + (b : ℂ) * I) := by
        rw [hs]
      rw [e]
      exact hnorm b (by rw [abs_of_nonneg hb]) (by rw [abs_of_nonpos hx]; ring)
  unfold stripInvFT
  rw [norm_mul]
  have h2 : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h2]
  calc 1 / (2 * Real.pi) * ‖∫ r : ℝ, Φ r * cexp (-(I * r * x))‖ ≤
      1 / (2 * Real.pi) * (C * (∫ r : ℝ, Real.exp (-(ε * |r|))) * Real.exp (-(b * |x|))) :=
        mul_le_mul_of_nonneg_left hval (by positivity)
    _ = _ := by ring

/-! ### Reality -/

theorem conj_integral_strip {Φ : ℂ → ℂ} (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) (x : ℝ) :
    conj (∫ r : ℝ, Φ r * cexp (-(I * r * x))) = ∫ r : ℝ, Φ r * cexp (-(I * r * x)) := by
  rw [← integral_conj]
  rw [← integral_neg_eq_self (fun r : ℝ => Φ r * cexp (-(I * r * x))) volume]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [map_mul, ← Complex.exp_conj]
  push_cast
  rw [hsym r]
  congr 2
  simp [Complex.conj_ofReal]

theorem stripInvFT_eq_ofReal {Φ : ℂ → ℂ} (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) (x : ℝ) :
    stripInvFT Φ x = (stripTest Φ x : ℂ) := by
  unfold stripTest
  refine (Complex.conj_eq_iff_re.mp ?_).symm
  unfold stripInvFT
  rw [map_mul, conj_integral_strip hsym x]
  congr 1
  rw [map_div₀, map_one, map_mul, Complex.conj_ofReal]
  simp [map_ofNat]

/-! ### The mathlib Fourier transform -/

theorem stripInvFT_eq_fourier (Φ : ℂ → ℂ) (x : ℝ) :
    stripInvFT Φ x = 𝓕 (fun ξ : ℝ => Φ ((2 * Real.pi * ξ : ℝ) : ℂ)) x := by
  rw [Real.fourier_eq']
  have h := Measure.integral_comp_mul_left
    (fun r : ℝ => Φ (r : ℂ) * cexp (-(I * r * x))) (2 * Real.pi)
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [abs_of_pos (inv_pos.mpr hpi)] at h
  unfold stripInvFT
  have e : (∫ ξ : ℝ, cexp (((-2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * I) •
      Φ ((2 * Real.pi * ξ : ℝ) : ℂ)) =
      ∫ ξ : ℝ, Φ ((2 * Real.pi * ξ : ℝ) : ℂ) * cexp (-(I * ((2 * Real.pi * ξ : ℝ) : ℂ) * x)) := by
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  rw [e, h, real_smul]
  push_cast
  ring

/-- Polynomial weights against a strip-decaying function are integrable on the line. -/
theorem integrable_pow_mul_norm_stripDecay {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) (n : ℕ) :
    Integrable (fun ξ : ℝ => ‖ξ‖ ^ n * ‖Φ ((2 * Real.pi * ξ : ℝ) : ℂ)‖) := by
  induction n generalizing Φ ε C with
  | zero =>
    have hc := continuous_ofReal_comp_of_stripDecay hΦ hb
    have hmeas : Continuous fun ξ : ℝ => ‖ξ‖ ^ 0 * ‖Φ ((2 * Real.pi * ξ : ℝ) : ℂ)‖ :=
      continuous_const.mul ((hc.comp (continuous_const.mul continuous_id)).norm)
    refine ((RHTower.integrable_exp_neg_mul_abs' (c := ε * (2 * Real.pi))
      (by positivity)).const_mul C).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [pow_zero, one_mul, norm_norm]
    have := hΦ.bound ((2 * Real.pi * ξ : ℝ) : ℂ) (by simpa using hb)
    simp only [Complex.ofReal_re, abs_mul, abs_of_pos Real.pi_pos,
      abs_two] at this
    refine this.trans (le_of_eq ?_)
    ring_nf
  | succ n ih =>
    have hb2 := ih (half_pos hε) (hΦ.mul_id hb hε)
    refine (hb2.div_const (2 * Real.pi)).congr (Eventually.of_forall fun ξ => ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      abs_two, pow_succ]
    field_simp

theorem integrable_stripInvFT {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) (hb0 : 0 < b)
    (hΦ : StripDecay Φ b ε C) : Integrable (stripInvFT Φ) := by
  have hcont : Continuous (stripInvFT Φ) := by
    have : stripInvFT Φ = 𝓕 (fun ξ : ℝ => Φ ((2 * Real.pi * ξ : ℝ) : ℂ)) :=
      funext (stripInvFT_eq_fourier Φ)
    rw [this]
    refine (Real.contDiff_fourier (N := 0) fun n hn => ?_).continuous
    exact integrable_pow_mul_norm_stripDecay hb hε hΦ n
  refine ((RHTower.integrable_exp_neg_mul_abs' hb0).const_mul
    (C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi))).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun x => norm_stripInvFT_le hb hε hΦ x)

/-! ### Regularity and decay of the test -/

theorem stripInvFT_eq_fourier_fun (Φ : ℂ → ℂ) :
    stripInvFT Φ = 𝓕 (fun ξ : ℝ => Φ ((2 * Real.pi * ξ : ℝ) : ℂ)) :=
  funext (stripInvFT_eq_fourier Φ)

theorem StripDecay.neg_I_mul_id {Φ : ℂ → ℂ} {b ε C : ℝ} (hΦ : StripDecay Φ b ε C) (hb : 0 ≤ b)
    (hε : 0 < ε) : StripDecay (fun z => -I * z * Φ z) b (ε / 2) (C * (2 / ε + b)) := by
  have h := hΦ.mul_id hb hε
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have := (h.diff z hz).const_mul (-I)
    simpa [mul_assoc] using this
  · have := h.bound z hz
    simpa [mul_assoc] using this

/-- The derivative of the inverse transform is the inverse transform of `−izΦ(z)`. -/
theorem hasDerivAt_stripInvFT {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) (x : ℝ) :
    HasDerivAt (stripInvFT Φ) (stripInvFT (fun z => -I * z * Φ z) x) x := by
  rw [stripInvFT_eq_fourier_fun Φ, stripInvFT_eq_fourier_fun]
  have h0 := integrable_pow_mul_norm_stripDecay hb hε hΦ 0
  have h1 := integrable_pow_mul_norm_stripDecay hb hε hΦ 1
  have hc := continuous_ofReal_comp_of_stripDecay hΦ hb
  have hφc : Continuous fun ξ : ℝ => Φ ((2 * Real.pi * ξ : ℝ) : ℂ) :=
    hc.comp (continuous_const.mul continuous_id)
  have hi0 : Integrable fun ξ : ℝ => Φ ((2 * Real.pi * ξ : ℝ) : ℂ) := by
    refine h0.mono' hφc.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    simp
  have hi1 : Integrable fun ξ : ℝ => ξ • Φ ((2 * Real.pi * ξ : ℝ) : ℂ) := by
    refine h1.mono' (continuous_id.smul hφc).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_smul, pow_one]
  have e : (fun ξ : ℝ => (fun z => -I * z * Φ z) ((2 * Real.pi * ξ : ℝ) : ℂ)) =
      fun ξ : ℝ => (-2 * (Real.pi : ℂ) * I * ξ) • Φ ((2 * Real.pi * ξ : ℝ) : ℂ) := by
    funext ξ
    rw [smul_eq_mul]
    push_cast
    ring
  rw [e]
  exact Real.hasDerivAt_fourier hi0 hi1 x

theorem stripTest_eq_comp (Φ : ℂ → ℂ) : stripTest Φ = Complex.reCLM ∘ stripInvFT Φ := by
  funext x
  simp [stripTest]

theorem contDiff_stripTest {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) : ContDiff ℝ 2 (stripTest Φ) := by
  have h : ContDiff ℝ 2 (stripInvFT Φ) := by
    rw [stripInvFT_eq_fourier_fun Φ]
    exact Real.contDiff_fourier (N := 2) fun n _ => integrable_pow_mul_norm_stripDecay hb hε hΦ n
  rw [stripTest_eq_comp]
  exact Complex.reCLM.contDiff.comp h

theorem deriv_stripTest {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) (x : ℝ) :
    deriv (stripTest Φ) x = (stripInvFT (fun z => -I * z * Φ z) x).re := by
  have h := (Complex.reCLM.hasFDerivAt (x := stripInvFT Φ x)).comp_hasDerivAt x
    (hasDerivAt_stripInvFT hb hε hΦ x)
  rw [stripTest_eq_comp, h.deriv]
  simp

/-- **The strip test is of the decay class.** -/
theorem expDecayTest_stripTest {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 1 / 2 < b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) : ExpDecayTest (stripTest Φ) := by
  have hb0 : 0 ≤ b := by linarith
  have hC := hΦ.const_nonneg hb0
  have hΦ1 := hΦ.neg_I_mul_id hb0 hε
  set K₀ := C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi)
  set K₁ := C * (2 / ε + b) * (∫ r : ℝ, Real.exp (-(ε / 2 * |r|))) / (2 * Real.pi)
  have hK₀ : 0 ≤ K₀ := by
    have : 0 ≤ ∫ r : ℝ, Real.exp (-(ε * |r|)) := integral_nonneg fun r => (Real.exp_pos _).le
    positivity
  have hK₁ : 0 ≤ K₁ := by
    have : 0 ≤ ∫ r : ℝ, Real.exp (-(ε / 2 * |r|)) := integral_nonneg fun r => (Real.exp_pos _).le
    have : 0 ≤ C * (2 / ε + b) := mul_nonneg hC (by positivity)
    positivity
  refine ⟨contDiff_stripTest hb0 hε hΦ, b - 1 / 2, max K₀ K₁, by linarith,
    le_max_of_le_left hK₀, fun x => ⟨?_, ?_⟩⟩
  · rw [show 1 / 2 + (b - 1 / 2) = b by ring]
    calc |stripTest Φ x| ≤ ‖stripInvFT Φ x‖ := Complex.abs_re_le_norm _
      _ ≤ K₀ * Real.exp (-(b * |x|)) := norm_stripInvFT_le hb0 hε hΦ x
      _ ≤ max K₀ K₁ * Real.exp (-(b * |x|)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · rw [show 1 / 2 + (b - 1 / 2) = b by ring, deriv_stripTest hb0 hε hΦ]
    calc |(stripInvFT (fun z => -I * z * Φ z) x).re| ≤ ‖stripInvFT (fun z => -I * z * Φ z) x‖ :=
          Complex.abs_re_le_norm _
      _ ≤ K₁ * Real.exp (-(b * |x|)) := norm_stripInvFT_le hb0 (half_pos hε) hΦ1 x
      _ ≤ max K₀ K₁ * Real.exp (-(b * |x|)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-! ### The Fourier transform of the test -/

/-- **Fourier inversion on the line.** -/
theorem paperFT_stripTest_ofReal {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 < b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) (r : ℝ) :
    Zeta23.paperFT (fun u => (stripTest Φ u : ℂ)) r = Φ r := by
  have hb0 := hb.le
  set φ : ℝ → ℂ := fun ξ => Φ ((2 * Real.pi * ξ : ℝ) : ℂ) with hφ
  have hc := continuous_ofReal_comp_of_stripDecay hΦ hb0
  have hφc : Continuous φ := hc.comp (continuous_const.mul continuous_id)
  have hi0 : Integrable φ := by
    refine (integrable_pow_mul_norm_stripDecay hb0 hε hΦ 0).mono' hφc.aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    simp [hφ]
  have hiF : Integrable (𝓕 φ) := by
    rw [← stripInvFT_eq_fourier_fun]
    exact integrable_stripInvFT hb0 hε hb hΦ
  have e1 : (fun u => (stripTest Φ u : ℂ)) = 𝓕 φ := by
    funext u
    rw [← stripInvFT_eq_ofReal hsym, stripInvFT_eq_fourier]
  have hinv := congrFun (Continuous.fourierInv_fourier_eq hφc hi0 hiF) (r / (2 * Real.pi))
  rw [Real.fourierInv_eq] at hinv
  rw [Zeta23.paperFT_def]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have e2 : φ (r / (2 * Real.pi)) = Φ r := by
    simp only [hφ]
    congr 2
    field_simp
  rw [← e2, ← hinv]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e1u : (stripTest Φ u : ℂ) = 𝓕 φ u := congrFun e1 u
  show (stripTest Φ u : ℂ) * cexp (I * r * u) = 𝐞 (inner ℝ u (r / (2 * Real.pi))) • 𝓕 φ u
  rw [e1u]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [mul_comm]
  congr 2
  push_cast
  field_simp

/-- **Strip analyticity of the Fourier transform** of an exponentially decaying function. -/
theorem differentiableAt_paperFT_of_expDecay {f : ℝ → ℂ} (hf : Continuous f) {K b : ℝ}
    (hfb : ∀ u, ‖f u‖ ≤ K * Real.exp (-(b * |u|))) {z : ℂ} (hz : |z.im| < b) :
    DifferentiableAt ℂ (Zeta23.paperFT f) z := by
  set δ := (b - |z.im|) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hK : 0 ≤ K := by
    have := hfb 0
    simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have key : ∀ w ∈ Metric.ball z δ, ∀ u : ℝ,
      ‖cexp (I * w * u)‖ ≤ Real.exp ((b - δ) * |u|) := by
    intro w hw u
    rw [Complex.norm_exp]
    have hre : (I * w * u).re = -(w.im * u) := by simp [Complex.mul_re]
    rw [hre]
    apply Real.exp_le_exp.mpr
    have hd : |w.im - z.im| ≤ ‖w - z‖ := by
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have hwz : ‖w - z‖ < δ := by rw [← Complex.dist_eq]; exact Metric.mem_ball.mp hw
    have hwim : |w.im| ≤ b - δ := by
      have := abs_sub_abs_le_abs_sub w.im z.im
      rw [hδ] at hwz ⊢
      linarith
    calc -(w.im * u) ≤ |w.im * u| := neg_le_abs _
      _ = |w.im| * |u| := abs_mul _ _
      _ ≤ (b - δ) * |u| := mul_le_mul_of_nonneg_right hwim (abs_nonneg u)
  have hexp : ∀ u : ℝ, Real.exp (-(b * |u|)) * Real.exp ((b - δ) * |u|) =
      Real.exp (-(δ * |u|)) := by
    intro u; rw [← Real.exp_add]; ring_nf
  have hbint : Integrable (fun u : ℝ => K * (2 / δ * Real.exp (-(δ / 2 * |u|)))) :=
    ((RHTower.integrable_exp_neg_mul_abs' (half_pos hδ0)).const_mul _).const_mul _
  have hderiv : ∀ u : ℝ, ∀ w : ℂ, HasDerivAt (fun w : ℂ => f u * cexp (I * w * u))
      (f u * (I * u * cexp (I * w * u))) w := by
    intro u w
    have h1 : HasDerivAt (fun w : ℂ => I * w * u) (I * u) w := by
      simpa using ((hasDerivAt_id w).const_mul I).mul_const (u : ℂ)
    have h2 := h1.cexp
    simpa [mul_comm, mul_left_comm, mul_assoc] using h2.const_mul (f u)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w : ℂ => fun u : ℝ => f u * cexp (I * w * u))
    (F' := fun w : ℂ => fun u : ℝ => f u * (I * u * cexp (I * w * u)))
    (bound := fun u : ℝ => K * (2 / δ * Real.exp (-(δ / 2 * |u|))))
    (Metric.ball_mem_nhds z hδ0)
    (Eventually.of_forall fun w => (hf.mul (by fun_prop)).aestronglyMeasurable)
    (by
      refine ((RHTower.integrable_exp_neg_mul_abs' hδ0).const_mul K).mono'
        (hf.mul (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
      rw [norm_mul]
      calc ‖f u‖ * ‖cexp (I * z * u)‖ ≤
            (K * Real.exp (-(b * |u|))) * Real.exp ((b - δ) * |u|) :=
            mul_le_mul (hfb u) (key z (Metric.mem_ball_self hδ0) u) (norm_nonneg _)
              (by positivity)
        _ = K * Real.exp (-(δ * |u|)) := by rw [mul_assoc, hexp])
    ((hf.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u w hw => by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      have hm := mul_exp_neg_le (t := |u|) hδ0
      calc ‖f u‖ * (|u| * ‖cexp (I * w * u)‖) ≤
            (K * Real.exp (-(b * |u|))) * (|u| * Real.exp ((b - δ) * |u|)) :=
            mul_le_mul (hfb u) (mul_le_mul_of_nonneg_left (key w hw u) (abs_nonneg _))
              (by positivity) (by positivity)
        _ = K * (|u| * Real.exp (-(δ * |u|))) := by rw [← hexp u]; ring
        _ ≤ K * (2 / δ * Real.exp (-(δ / 2 * |u|))) := mul_le_mul_of_nonneg_left hm hK)
    hbint
    (Eventually.of_forall fun u w _ => hderiv u w)
  have e : Zeta23.paperFT f = fun w : ℂ => ∫ u : ℝ, f u * cexp (I * w * u) := by
    funext w; rw [Zeta23.paperFT_def]
  rw [e]
  exact hmain.2.differentiableAt

theorem continuous_stripTest {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) : Continuous (stripTest Φ) :=
  (contDiff_stripTest hb hε hΦ).continuous

/-- **The Fourier transform of the strip test is `Φ` on the open strip.** -/
theorem paperFT_stripTest {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 < b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) {z : ℂ}
    (hz : |z.im| < b) :
    Zeta23.paperFT (fun u => (stripTest Φ u : ℂ)) z = Φ z := by
  have hb0 := hb.le
  set U : Set ℂ := {w | |w.im| < b} with hU
  have hUo : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hUc : IsPreconnected U := by
    have : U = Complex.imLm ⁻¹' Set.Ioo (-b) b := by
      ext w; simp [hU, abs_lt]
    rw [this]
    exact ((convex_Ioo (-b) b).linear_preimage Complex.imLm).isPreconnected
  have hcont : Continuous fun u => (stripTest Φ u : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_stripTest hb0 hε hΦ)
  have hdec : ∀ u, ‖(stripTest Φ u : ℂ)‖ ≤
      C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi) * Real.exp (-(b * |u|)) := by
    intro u
    rw [← stripInvFT_eq_ofReal hsym]
    exact norm_stripInvFT_le hb0 hε hΦ u
  have hf : AnalyticOnNhd ℂ (Zeta23.paperFT fun u => (stripTest Φ u : ℂ)) U :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (differentiableAt_paperFT_of_expDecay hcont hdec hw).differentiableWithinAt) hUo
  have hg : AnalyticOnNhd ℂ Φ U :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (hΦ.diff w (le_of_lt hw)).differentiableWithinAt) hUo
  have h0 : (0 : ℂ) ∈ U := by simp [hU, hb]
  have ht : Tendsto (fun n : ℕ => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [Complex.ofReal_zero] at this
      exact this
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ),
      Zeta23.paperFT (fun u => (stripTest Φ u : ℂ)) w = Φ w :=
    ht.frequently (Eventually.frequently (Eventually.of_forall fun n =>
      paperFT_stripTest_ofReal hb hε hΦ hsym _))
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hUc h0 hfreq hz

/-! ### The autocorrelation -/

theorem norm_cexp_neg_I_real (r t : ℝ) : ‖cexp (-(I * r * t))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

/-- **The autocorrelation of the strip test** is the cosine transform of `|Φ|²/2π`. -/
theorem crossCorr_stripTest {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 < b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) (y : ℝ) :
    crossCorr (stripTest Φ) (stripTest Φ) y =
      1 / (2 * Real.pi) * ∫ r : ℝ, ‖Φ r‖ ^ 2 * Real.cos (r * y) := by
  have hb0 := hb.le
  have hC := hΦ.const_nonneg hb0
  set G : ℝ → ℂ := stripInvFT Φ with hG
  have hGF : ∀ t, G t = (stripTest Φ t : ℂ) := stripInvFT_eq_ofReal hsym
  have hGi : Integrable G := integrable_stripInvFT hb0 hε hb hΦ
  have hGc : Continuous G := by
    have : G = fun t => (stripTest Φ t : ℂ) := funext hGF
    rw [this]
    exact Complex.continuous_ofReal.comp (continuous_stripTest hb0 hε hΦ)
  have hc := continuous_ofReal_comp_of_stripDecay hΦ hb0
  have hΦb : ∀ r : ℝ, ‖Φ r‖ ≤ C * Real.exp (-(ε * |r|)) := fun r => by
    simpa using hΦ.bound r (by simpa using hb0)
  have hΦi : Integrable fun r : ℝ => Φ r :=
    ((RHTower.integrable_exp_neg_mul_abs' hε).const_mul C).mono' hc.aestronglyMeasurable
      (Eventually.of_forall hΦb)
  set f : ℝ → ℝ → ℂ := fun t r => G t * (Φ r * cexp (-(I * r * (t - y)))) with hf
  have hfi : Integrable (Function.uncurry f) (volume.prod volume) := by
    have hcont : Continuous (Function.uncurry f) := by
      simp only [hf, Function.uncurry_def]
      exact (hGc.comp continuous_fst).mul ((hc.comp continuous_snd).mul (by fun_prop))
    refine (hGi.norm.mul_prod hΦi.norm).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    simp only [hf, Function.uncurry_def]
    rw [norm_mul, norm_mul, show (p.1 : ℂ) - y = ((p.1 - y : ℝ) : ℂ) by push_cast; ring,
      norm_cexp_neg_I_real, mul_one]
  -- inner integral in `t`
  have hinner : ∀ r : ℝ, ∫ t : ℝ, f t r = ((‖Φ r‖ ^ 2 : ℝ) : ℂ) * cexp (I * r * y) := by
    intro r
    have e : ∀ t : ℝ, f t r = Φ r * cexp (I * r * y) * (G t * cexp (I * ((-r : ℝ) : ℂ) * t)) := by
      intro t
      simp only [hf]
      rw [show cexp (-(I * r * (t - y))) = cexp (I * ((-r : ℝ) : ℂ) * t) * cexp (I * r * y) by
        rw [← Complex.exp_add]; push_cast; ring_nf]
      ring
    simp_rw [e]
    rw [integral_const_mul]
    have hP : ∫ t : ℝ, G t * cexp (I * ((-r : ℝ) : ℂ) * t) = Φ (-(r : ℂ)) := by
      have := paperFT_stripTest_ofReal hb hε hΦ hsym (-r)
      rw [Zeta23.paperFT_def] at this
      rw [Complex.ofReal_neg] at this ⊢
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hGF]
    rw [hP, hsym r, Complex.ofReal_pow, ← Complex.mul_conj']
    ring
  have hcomplex : ((crossCorr (stripTest Φ) (stripTest Φ) y : ℝ) : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, ((‖Φ r‖ ^ 2 : ℝ) : ℂ) * cexp (I * r * y) := by
    unfold RHTower.crossCorr
    rw [← integral_complex_ofReal]
    have e1 : ∀ t : ℝ, (((stripTest Φ t * stripTest Φ (t - y) : ℝ)) : ℂ) =
        (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, f t r := by
      intro t
      push_cast
      rw [← hGF, ← hGF]
      have hGt : G (t - y) =
          (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Φ r * cexp (-(I * r * ((t : ℂ) - y))) := by
        simp only [hG, stripInvFT, Complex.ofReal_sub]
      rw [hGt]
      simp only [hf]
      rw [integral_const_mul]
      ring
    simp_rw [e1]
    rw [integral_const_mul, integral_integral_swap hfi]
    simp_rw [hinner]
  have hi2 : Integrable fun r : ℝ => ((‖Φ r‖ ^ 2 : ℝ) : ℂ) * cexp (I * r * y) := by
    have hcont : Continuous fun r : ℝ => ((‖Φ r‖ ^ 2 : ℝ) : ℂ) * cexp (I * r * y) :=
      (Complex.continuous_ofReal.comp (hc.norm.pow 2)).mul (by fun_prop)
    refine (((RHTower.integrable_exp_neg_mul_abs' hε).const_mul C).const_mul C).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
    rw [norm_mul, show cexp (I * r * y) = cexp (-(I * ((-r : ℝ) : ℂ) * y)) by push_cast; ring_nf,
      norm_cexp_neg_I_real, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := hΦb r
    have h2 : C * Real.exp (-(ε * |r|)) ≤ C := by
      have : Real.exp (-(ε * |r|)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg r])
      nlinarith
    calc ‖Φ r‖ ^ 2 = ‖Φ r‖ * ‖Φ r‖ := sq _
      _ ≤ C * (C * Real.exp (-(ε * |r|))) :=
          mul_le_mul (h1.trans h2) h1 (norm_nonneg _) hC
  have hre := congrArg Complex.re hcomplex
  rw [Complex.ofReal_re] at hre
  rw [hre, show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, ← RCLike.re_eq_complex_re, ← integral_re hi2]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [RCLike.re_eq_complex_re]
  rw [Complex.re_ofReal_mul, show I * (r : ℂ) * y = ((r * y : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

/-! ### The (N1) object -/

/-- **A `Ξ`-divisible strip function with a blind spectral square gives a `Ξ`-divisible
prime-blind test.** -/
theorem xiDivisibleBlindTest_stripTest {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 1 / 2 < b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) {g : ℂ → ℂ}
    (hfac : ∀ z : ℂ, |z.im| ≤ 1 / 2 → Φ z = RHTower.XiC z * g z) (hg : ∀ r : ℝ, g r ≠ 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → ∫ r : ℝ, ‖Φ r‖ ^ 2 * Real.cos (r * Real.log n) = 0) :
    XiDivisibleBlindTest (stripTest Φ) := by
  have hb0 : 0 < b := by linarith
  refine ⟨expDecayTest_stripTest hb hε hΦ, fun n hn => ?_, g, fun z hz => ?_, hg⟩
  · rw [crossCorr_stripTest hb0 hε hΦ hsym, hblind n hn, mul_zero]
  · rw [paperFT_stripTest hb0 hε hΦ hsym (by linarith : |z.im| < b)]
    exact hfac z hz

/-- **RH is prime-blind positivity** as soon as a `Ξ`-divisible strip function of exponential decay
has a spectral square with vanishing cosine moments at every `log n`, `n ≥ 2`. -/
theorem riemannHypothesis_iff_primeBlindPositive_of_stripFactor {Φ : ℂ → ℂ} {b ε C : ℝ}
    (hb : 1 / 2 < b) (hε : 0 < ε) (hΦ : StripDecay Φ b ε C)
    (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) {g : ℂ → ℂ}
    (hfac : ∀ z : ℂ, |z.im| ≤ 1 / 2 → Φ z = RHTower.XiC z * g z) (hg : ∀ r : ℝ, g r ≠ 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → ∫ r : ℝ, ‖Φ r‖ ^ 2 * Real.cos (r * Real.log n) = 0) :
    RiemannHypothesis ↔ WeilOneSided.PrimeBlindPositive :=
  riemannHypothesis_iff_primeBlindPositive_of_exists_xiDivisibleBlindTest
    ⟨_, xiDivisibleBlindTest_stripTest hb hε hΦ hsym hfac hg hblind⟩

end RHTower.WeilSpectral
