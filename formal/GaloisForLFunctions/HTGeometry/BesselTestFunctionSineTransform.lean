import GaloisForLFunctions.HTGeometry.BesselJContourIdentity
import GaloisForLFunctions.HTGeometry.CoshSchwartzSpan
import GaloisForLFunctions.HTGeometry.BesselOrderLaplaceAsymptotic

/-!
# Bessel expansions of compactly supported test functions

Let `φ` be smooth and supported in `[a, b]`, `a > 0`, and put `ψ(y) = φ(y)/y`.  Its odd Bessel
coefficients `φ̃(l) = ∫ J_l(y) φ(y) dy/y` satisfy `|φ̃(l)| ≤ (|b|/2)^l/l! · e^{(b/2)²} ∫|ψ|`, and its
sine transform `S(u) = ∫ ψ(y) sin(yu) dy` has the two Jacobi–Anger expansions

`S(sin θ) = 2 ∑_k φ̃(2k+1) sin((2k+1)θ)`,
`S(cosh w) = 2 ∑_k (-1)^k φ̃(2k+1) cosh((2k+1)w) = P(e^w) + P(e^{-w})`,

with `P(x) = ∑_k (-1)^k φ̃(2k+1) x^{2k+1}` (`hasSum_sineTransform_sin`, `sineTransform_cosh_eq`).
The odd extension `χ(y) = ψ(y) - ψ(-y)` is a compactly supported smooth function with
`𝓕χ(ξ) = -2i S(2πξ)`, so `S(u) = (i/2) 𝓕χ(u/2π)` is a Schwartz function and Fourier inversion gives
the sine inversion formula `∫_0^∞ S(u) sin(Xu) du = (π/2) ψ(X)` for `X > 0`
(`integral_Ioi_sineTransform_mul_sin`).
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform ContDiff

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `J_l` is continuous: the power series converges uniformly on bounded sets. -/
theorem continuous_besselJ (l : ℕ) : Continuous (besselJ l) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  set R := |x₀| + 1
  set u : ℕ → ℝ := fun j => (R / 2) ^ l / l.factorial * (((R / 2) ^ 2) ^ j / j.factorial)
  have hu : Summable u := (Real.summable_pow_div_factorial ((R / 2) ^ 2)).mul_left _
  have hon : ContinuousOn (besselJ l) (Ioo (x₀ - 1) (x₀ + 1)) := by
    unfold besselJ
    refine continuousOn_tsum (fun j => Continuous.continuousOn (by fun_prop)) hu fun j x hx => ?_
    rw [Real.norm_eq_abs]
    refine (abs_besselJ_term_le l x j).trans ?_
    have hx' : |x / 2| ≤ R / 2 := by
      rw [abs_div, abs_two]
      have : |x| ≤ R := by
        obtain ⟨h1, h2⟩ := hx
        rw [abs_le]; constructor <;> cases abs_cases x₀ <;> linarith
      linarith
    have hx2 : (x / 2) ^ 2 ≤ (R / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx' 2
    simp only [u]
    gcongr
  exact hon.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))

/-- `e^{-iθ} - e^{iθ} = -2i sin θ`. -/
theorem cexp_neg_mul_I_sub_cexp_mul_I (z : ℂ) :
    cexp (-z * Complex.I) - cexp (z * Complex.I) = -2 * Complex.I * Complex.sin z := by
  rw [Complex.sin]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `sin((2k+1)π/2) = (-1)^k`. -/
theorem sin_odd_mul_pi_div_two (k : ℕ) : Real.sin ((2 * k + 1 : ℕ) * (Real.pi / 2)) = (-1) ^ k := by
  rw [show ((2 * k + 1 : ℕ) : ℝ) * (Real.pi / 2) = k * Real.pi + Real.pi / 2 by push_cast; ring,
    Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]

/-- `cos((2k+1)π/2) = 0`. -/
theorem cos_odd_mul_pi_div_two (k : ℕ) : Real.cos ((2 * k + 1 : ℕ) * (Real.pi / 2)) = 0 := by
  rw [show ((2 * k + 1 : ℕ) : ℝ) * (Real.pi / 2) = k * Real.pi + Real.pi / 2 by push_cast; ring,
    Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]

/-- **Jacobi–Anger at `θ = π/2 + iw`**: `sin(x cosh w) = 2 ∑_k (-1)^k J_{2k+1}(x) cosh((2k+1)w)`. -/
theorem hasSum_sin_mul_cosh (x w : ℝ) :
    HasSum (fun k : ℕ => 2 * besselJ (2 * k + 1) x * ((-1) ^ k * Real.cosh ((2 * k + 1 : ℕ) * w)))
      (Real.sin (x * Real.cosh w)) := by
  have h := hasSum_sin_mul_sin x ((Real.pi / 2 : ℝ) + w * Complex.I)
  have hs : Complex.sin ((Real.pi / 2 : ℝ) + w * Complex.I) = Real.cosh w := by
    rw [Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, Real.sin_pi_div_two, Real.cos_pi_div_two, Complex.ofReal_cosh]
    push_cast; ring
  have hk : ∀ k : ℕ, Complex.sin ((2 * k + 1 : ℕ) * ((Real.pi / 2 : ℝ) + w * Complex.I)) =
      (((-1) ^ k * Real.cosh ((2 * k + 1 : ℕ) * w) : ℝ) : ℂ) := fun k => by
    rw [show ((2 * k + 1 : ℕ) : ℂ) * ((Real.pi / 2 : ℝ) + w * Complex.I) =
        (((2 * k + 1 : ℕ) * (Real.pi / 2) : ℝ) : ℂ) + (((2 * k + 1 : ℕ) * w : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, sin_odd_mul_pi_div_two, cos_odd_mul_pi_div_two]
    push_cast; ring
  rw [hs] at h
  simp_rw [hk] at h
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  · funext k; push_cast; ring
  · push_cast; ring_nf

/-- A smooth test function supported in `[a, b]` with `a > 0`. -/
structure BesselTestFunction where
  /-- The test function. -/
  φ : ℝ → ℂ
  /-- Left end of the support interval. -/
  a : ℝ
  /-- Right end of the support interval. -/
  b : ℝ
  pos : 0 < a
  smooth : ContDiff ℝ ∞ φ
  vanish : ∀ y, y ∉ Icc a b → φ y = 0

namespace BesselTestFunction

variable (T : BesselTestFunction)

/-- `ψ(y) = φ(y)/y`. -/
def ψ (y : ℝ) : ℂ := T.φ y / y

theorem ψ_eq_zero {y : ℝ} (hy : y ∉ Icc T.a T.b) : T.ψ y = 0 := by
  simp [ψ, T.vanish y hy]

theorem ψ_eq_zero_of_nonpos {y : ℝ} (hy : y ≤ 0) : T.ψ y = 0 :=
  T.ψ_eq_zero fun h => by linarith [h.1, T.pos]

theorem contDiff_ψ : ContDiff ℝ ∞ T.ψ := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds T.pos] with z hz
    exact T.ψ_eq_zero fun h => absurd h.1 (not_le.2 hz)
  · have h1 : ContDiffAt ℝ ∞ (fun z : ℝ => ((z⁻¹ : ℝ) : ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y (contDiffAt_inv ℝ hy)
    have e : T.ψ = fun z => T.φ z * ((z⁻¹ : ℝ) : ℂ) := by
      funext z; simp [ψ, div_eq_mul_inv]
    rw [e]; exact T.smooth.contDiffAt.mul h1

theorem continuous_ψ : Continuous T.ψ := T.contDiff_ψ.continuous

theorem hasCompactSupport_ψ : HasCompactSupport T.ψ :=
  HasCompactSupport.intro isCompact_Icc fun _ hy => T.ψ_eq_zero hy

theorem integrable_ψ : Integrable T.ψ :=
  T.continuous_ψ.integrable_of_hasCompactSupport T.hasCompactSupport_ψ

/-! ## The odd Bessel coefficients -/

/-- The majorant `(|b|/2)^l/l! · e^{(b/2)²}` of `|J_l|` on `[a, b]`. -/
def besselMajor (l : ℕ) : ℝ := (|T.b| / 2) ^ l / l.factorial * Real.exp ((T.b / 2) ^ 2)

theorem besselMajor_nonneg (l : ℕ) : 0 ≤ T.besselMajor l := by unfold besselMajor; positivity

theorem abs_besselJ_le_besselMajor (l : ℕ) {y : ℝ} (hy : y ∈ Icc T.a T.b) :
    |besselJ l y| ≤ T.besselMajor l := by
  have hy0 : 0 < y := lt_of_lt_of_le T.pos hy.1
  refine (abs_besselJ_le l y).trans ?_
  unfold besselMajor
  have h1 : |y / 2| ≤ |T.b| / 2 := by
    rw [abs_div, abs_of_pos hy0, abs_two]
    have : y ≤ |T.b| := hy.2.trans (le_abs_self _)
    linarith
  have h2 : (y / 2) ^ 2 ≤ (T.b / 2) ^ 2 := by
    have hb : y ≤ T.b := hy.2
    nlinarith
  gcongr

theorem norm_besselJ_mul_ψ_le (l : ℕ) (y : ℝ) :
    ‖(besselJ l y : ℂ) * T.ψ y‖ ≤ T.besselMajor l * ‖T.ψ y‖ := by
  by_cases hy : y ∈ Icc T.a T.b
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (T.abs_besselJ_le_besselMajor l hy) (norm_nonneg _)
  · simp [T.ψ_eq_zero hy]

theorem integrable_besselJ_mul_ψ (l : ℕ) : Integrable fun y => (besselJ l y : ℂ) * T.ψ y :=
  (T.integrable_ψ.norm.const_mul (T.besselMajor l)).mono'
    (((continuous_ofReal.comp (continuous_besselJ l)).mul T.continuous_ψ).aestronglyMeasurable)
    (Eventually.of_forall (T.norm_besselJ_mul_ψ_le l))

/-- `φ̃(l) = ∫ J_l(y) φ(y) dy/y`. -/
def besselCoeff (l : ℕ) : ℂ := ∫ y, (besselJ l y : ℂ) * T.ψ y

theorem norm_besselCoeff_le (l : ℕ) : ‖T.besselCoeff l‖ ≤ T.besselMajor l * ∫ y, ‖T.ψ y‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    (T.integrable_ψ.norm.const_mul _) (Eventually.of_forall (T.norm_besselJ_mul_ψ_le l))

theorem summable_besselMajor_mul_pow (r : ℝ) :
    Summable fun k : ℕ => T.besselMajor (2 * k + 1) * r ^ (2 * k + 1) := by
  have hs := (Real.summable_pow_div_factorial (|T.b| / 2 * r)).comp_injective
    (i := fun k : ℕ => 2 * k + 1) (fun x y h => by simp only at h; omega)
  refine (hs.mul_right (Real.exp ((T.b / 2) ^ 2))).congr fun k => ?_
  simp only [Function.comp, besselMajor, mul_pow]
  ring

/-! ## Jacobi–Anger expansions of the sine transform -/

/-- **Integrated Jacobi–Anger expansion**: if `g(y) = 2 ∑_k J_{2k+1}(y) t_k` with
`|t_k| ≤ r^{2k+1}`, then `∫ ψ g = 2 ∑_k φ̃(2k+1) t_k`. -/
theorem hasSum_integral_of_besselExpansion (t : ℕ → ℝ) (r : ℝ)
    (ht : ∀ k, |t k| ≤ r ^ (2 * k + 1)) (g : ℝ → ℝ)
    (hg : ∀ y, HasSum (fun k => 2 * besselJ (2 * k + 1) y * t k) (g y)) :
    HasSum (fun k => 2 * T.besselCoeff (2 * k + 1) * (t k : ℂ)) (∫ y, T.ψ y * (g y : ℂ)) := by
  set F : ℕ → ℝ → ℂ := fun k y => T.ψ y * ((2 * besselJ (2 * k + 1) y * t k : ℝ) : ℂ) with hF
  have hFint : ∀ k, Integrable (F k) := fun k => by
    refine ((T.integrable_besselJ_mul_ψ (2 * k + 1)).const_mul (2 * (t k : ℂ))).congr
      (Eventually.of_forall fun y => ?_)
    simp only [F]; push_cast; ring
  have hFnorm : ∀ k, ∫ y, ‖F k y‖ ≤ 2 * T.besselMajor (2 * k + 1) * r ^ (2 * k + 1) *
      ∫ y, ‖T.ψ y‖ := fun k => by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (T.integrable_ψ.norm.const_mul _) (Eventually.of_forall fun y => ?_)
    simp only [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
    by_cases hy : y ∈ Icc T.a T.b
    · have h2 := T.abs_besselJ_le_besselMajor (2 * k + 1) hy
      have hM := T.besselMajor_nonneg (2 * k + 1)
      calc ‖T.ψ y‖ * (2 * |besselJ (2 * k + 1) y| * |t k|)
          ≤ ‖T.ψ y‖ * (2 * T.besselMajor (2 * k + 1) * r ^ (2 * k + 1)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (by linarith) (ht k) (abs_nonneg _) (by linarith))
              (norm_nonneg _)
        _ = _ := by ring
    · simp [T.ψ_eq_zero hy]
  have hsum : Summable fun k => ∫ y, ‖F k y‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) hFnorm ?_
    have := T.summable_besselMajor_mul_pow r
    refine ((this.mul_left 2).mul_right (∫ y, ‖T.ψ y‖)).congr fun k => ?_
    ring
  have hH := hasSum_integral_of_summable_integral_norm hFint hsum
  have hpt : (fun y => ∑' k, F k y) = fun y => T.ψ y * (g y : ℂ) := by
    funext y
    simp only [F]
    rw [tsum_mul_left, ← Complex.ofReal_tsum, (hg y).tsum_eq]
  have hval : (fun k => ∫ y, F k y) = fun k => 2 * T.besselCoeff (2 * k + 1) * (t k : ℂ) := by
    funext k
    have e : (fun y => F k y) =
        fun y => (2 * (t k : ℂ)) * ((besselJ (2 * k + 1) y : ℂ) * T.ψ y) := by
      funext y; simp only [F]; push_cast; ring
    rw [e, integral_const_mul, besselCoeff]; ring
  rw [hpt, hval] at hH
  exact hH

/-- `S(u) = ∫ ψ(y) sin(yu) dy`. -/
def sineTransform (u : ℝ) : ℂ := ∫ y, T.ψ y * (Real.sin (y * u) : ℂ)

/-- **`S(sin θ) = 2 ∑_k φ̃(2k+1) sin((2k+1)θ)`.** -/
theorem hasSum_sineTransform_sin (θ : ℝ) :
    HasSum (fun k : ℕ => 2 * T.besselCoeff (2 * k + 1) * (Real.sin ((2 * k + 1 : ℕ) * θ) : ℂ))
      (T.sineTransform (Real.sin θ)) :=
  T.hasSum_integral_of_besselExpansion (fun k => Real.sin ((2 * k + 1 : ℕ) * θ)) 1
    (fun k => by rw [one_pow]; exact Real.abs_sin_le_one _) _ (fun y => hasSum_real_sin_mul_sin y θ)

/-- **`S(cosh w) = 2 ∑_k (-1)^k φ̃(2k+1) cosh((2k+1)w)`.** -/
theorem hasSum_sineTransform_cosh (w : ℝ) :
    HasSum (fun k : ℕ => 2 * T.besselCoeff (2 * k + 1) *
        (((-1) ^ k * Real.cosh ((2 * k + 1 : ℕ) * w) : ℝ) : ℂ))
      (T.sineTransform (Real.cosh w)) := by
  refine T.hasSum_integral_of_besselExpansion _ (Real.exp |w|) (fun k => ?_) _
    (fun y => hasSum_sin_mul_cosh y w)
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (Real.cosh_pos _),
    ← Real.exp_nat_mul]
  refine (Real.cosh_le_exp_abs' _).trans ?_
  rw [abs_mul, Nat.abs_cast]
where
  Real.cosh_le_exp_abs' (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
    rw [Real.cosh_eq]
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
      linarith [Real.exp_le_exp.2 (show -x ≤ x by linarith)]
    · rw [abs_of_nonpos h]
      linarith [Real.exp_le_exp.2 (show x ≤ -x by linarith)]

/-- `P(x) = ∑_k (-1)^k φ̃(2k+1) x^{2k+1}`. -/
def oddSeries (x : ℝ) : ℂ := ∑' k : ℕ, (-1) ^ k * T.besselCoeff (2 * k + 1) * ((x ^ (2 * k + 1) : ℝ) : ℂ)

theorem summable_oddSeries (x : ℝ) :
    Summable fun k : ℕ => (-1) ^ k * T.besselCoeff (2 * k + 1) * ((x ^ (2 * k + 1) : ℝ) : ℂ) := by
  refine Summable.of_norm_bounded
    ((T.summable_besselMajor_mul_pow |x|).mul_right (∫ y, ‖T.ψ y‖)) fun k => ?_
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_pow]
  calc ‖T.besselCoeff (2 * k + 1)‖ * |x| ^ (2 * k + 1)
      ≤ (T.besselMajor (2 * k + 1) * ∫ y, ‖T.ψ y‖) * |x| ^ (2 * k + 1) := by
        gcongr; exact T.norm_besselCoeff_le _
    _ = _ := by ring

/-- **`S(cosh w) = P(e^w) + P(e^{-w})`.** -/
theorem sineTransform_cosh_eq (w : ℝ) :
    T.sineTransform (Real.cosh w) = T.oddSeries (Real.exp w) + T.oddSeries (Real.exp (-w)) := by
  have h1 := (T.summable_oddSeries (Real.exp w)).hasSum.add (T.summable_oddSeries (Real.exp (-w))).hasSum
  refine (T.hasSum_sineTransform_cosh w).unique (h1.congr_fun fun k => ?_)
  rw [Real.cosh_eq, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
    show ((2 * k + 1 : ℕ) : ℝ) * -w = -(((2 * k + 1 : ℕ) : ℝ) * w) by ring]
  push_cast
  ring

/-! ## The odd extension and sine inversion -/

/-- The odd extension `χ(y) = ψ(y) - ψ(-y)`. -/
def oddExt (y : ℝ) : ℂ := T.ψ y - T.ψ (-y)

theorem contDiff_oddExt : ContDiff ℝ ∞ T.oddExt :=
  T.contDiff_ψ.sub (T.contDiff_ψ.comp contDiff_neg)

theorem hasCompactSupport_oddExt : HasCompactSupport T.oddExt := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -|T.b|) (b := |T.b|)) fun y hy => ?_
  have h1 : y ∉ Icc T.a T.b := fun h => hy ⟨by linarith [h.1, T.pos, abs_nonneg T.b],
    h.2.trans (le_abs_self _)⟩
  have h2 : -y ∉ Icc T.a T.b := fun h => hy ⟨by linarith [h.2, le_abs_self T.b],
    by linarith [h.1, T.pos, abs_nonneg T.b]⟩
  simp [oddExt, T.ψ_eq_zero h1, T.ψ_eq_zero h2]

/-- `χ` as a Schwartz function. -/
def oddExtSchwartz : SchwartzMap ℝ ℂ := T.hasCompactSupport_oddExt.toSchwartzMap T.contDiff_oddExt

theorem oddExtSchwartz_apply (y : ℝ) : T.oddExtSchwartz y = T.oddExt y := rfl

theorem oddExt_of_pos {X : ℝ} (hX : 0 < X) : T.oddExt X = T.ψ X := by
  rw [oddExt, T.ψ_eq_zero_of_nonpos (y := -X) (by linarith), sub_zero]

theorem integrable_oddExt : Integrable T.oddExt :=
  T.contDiff_oddExt.continuous.integrable_of_hasCompactSupport T.hasCompactSupport_oddExt

theorem sineTransform_neg (u : ℝ) : T.sineTransform (-u) = -T.sineTransform u := by
  rw [sineTransform, sineTransform, ← integral_neg]
  congr 1; funext y
  rw [mul_neg, Real.sin_neg]; push_cast; ring

/-- **`𝓕χ(ξ) = -2i S(2πξ)`.** -/
theorem fourier_oddExt (ξ : ℝ) :
    𝓕 T.oddExt ξ = -2 * Complex.I * T.sineTransform (2 * Real.pi * ξ) := by
  set e : ℝ → ℂ := fun v => cexp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) with he
  have hb : ∀ v, ‖e v‖ ≤ 1 := fun v => (Complex.norm_exp_ofReal_mul_I _).le
  have hce : Continuous e := by fun_prop
  have hi1 : Integrable fun v => e v * T.ψ v :=
    T.integrable_ψ.bdd_mul hce.aestronglyMeasurable (Eventually.of_forall hb)
  have hi2 : Integrable fun v => e v * T.ψ (-v) :=
    T.integrable_ψ.comp_neg.bdd_mul hce.aestronglyMeasurable (Eventually.of_forall hb)
  have hrefl : ∫ v, e v * T.ψ (-v) = ∫ v, e (-v) * T.ψ v := by
    have := integral_neg_eq_self (fun v => e (-v) * T.ψ v) volume
    simp only [neg_neg] at this
    exact this
  rw [Real.fourier_real_eq_integral_exp_smul]
  have e1 : (fun v : ℝ => cexp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) • T.oddExt v) =
      fun v => e v * T.ψ v - e v * T.ψ (-v) := by
    funext v; simp only [e, oddExt, smul_eq_mul]; ring
  have hi3 : Integrable fun v => e (-v) * T.ψ v :=
    T.integrable_ψ.bdd_mul (hce.comp continuous_neg).aestronglyMeasurable
      (Eventually.of_forall fun v => hb (-v))
  rw [e1, integral_sub hi1 hi2, hrefl, ← integral_sub hi1 hi3, sineTransform, ← integral_const_mul]
  congr 1; funext v
  have := cexp_neg_mul_I_sub_cexp_mul_I ((2 * Real.pi * v * ξ : ℝ) : ℂ)
  simp only [e]
  rw [show ((-2 * Real.pi * v * ξ : ℝ) : ℂ) = -((2 * Real.pi * v * ξ : ℝ) : ℂ) by push_cast; ring,
    show ((-2 * Real.pi * -v * ξ : ℝ) : ℂ) = ((2 * Real.pi * v * ξ : ℝ) : ℂ) by push_cast; ring,
    ← sub_mul, this, ← Complex.ofReal_sin,
    show 2 * Real.pi * v * ξ = v * (2 * Real.pi * ξ) by ring]
  ring

theorem integrable_fourier_oddExt : Integrable (𝓕 T.oddExt) := by
  have h := (𝓕 T.oddExtSchwartz).integrable (μ := volume)
  rwa [SchwartzMap.fourier_coe] at h

/-- **`S(u) = (i/2) 𝓕χ(u/2π)`.** -/
theorem sineTransform_eq_fourier (u : ℝ) :
    T.sineTransform u = Complex.I / 2 * 𝓕 T.oddExt (u / (2 * Real.pi)) := by
  rw [T.fourier_oddExt, mul_div_cancel₀ _ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
  have : Complex.I / 2 * (-2 * Complex.I) = 1 := by
    field_simp; rw [Complex.I_sq]; ring
  rw [← mul_assoc, this, one_mul]

theorem sineTransform_eq_schwartz (u : ℝ) :
    T.sineTransform u = Complex.I / 2 * (𝓕 T.oddExtSchwartz) (1 / (2 * Real.pi) * u) := by
  have hco : (⇑T.oddExtSchwartz : ℝ → ℂ) = T.oddExt := rfl
  rw [T.sineTransform_eq_fourier, SchwartzMap.fourier_coe, hco,
    show 1 / (2 * Real.pi) * u = u / (2 * Real.pi) by ring]

theorem integrable_sineTransform : Integrable T.sineTransform := by
  refine ((T.integrable_fourier_oddExt.comp_div (by positivity : (2 * Real.pi : ℝ) ≠ 0)).const_mul
    (Complex.I / 2)).congr (Eventually.of_forall fun u => ?_)
  rw [T.sineTransform_eq_fourier]

theorem continuous_sineTransform : Continuous T.sineTransform := by
  have : T.sineTransform = fun u => Complex.I / 2 * (𝓕 T.oddExtSchwartz) (1 / (2 * Real.pi) * u) :=
    funext T.sineTransform_eq_schwartz
  rw [this]
  exact continuous_const.mul ((𝓕 T.oddExtSchwartz).continuous.comp (continuous_const.mul continuous_id))

/-- **Sine inversion on the line**: `∫ S(u) sin(Xu) du = π χ(X)`. -/
theorem integral_sineTransform_mul_sin (X : ℝ) :
    ∫ u, T.sineTransform u * (Real.sin (X * u) : ℂ) = Real.pi * T.oddExt X := by
  have hinv := congrFun (T.contDiff_oddExt.continuous.fourierInv_fourier_eq T.integrable_oddExt
    T.integrable_fourier_oddExt) X
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hinv
  have hS2 : Integrable fun v : ℝ => T.sineTransform (2 * Real.pi * v) :=
    T.integrable_sineTransform.comp_mul_left' (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hcS : Continuous T.sineTransform := T.continuous_sineTransform
  have hcos : Integrable fun v : ℝ =>
      (Real.cos (2 * Real.pi * v * X) : ℂ) * T.sineTransform (2 * Real.pi * v) :=
    hS2.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun v => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hsin : Integrable fun v : ℝ =>
      (Real.sin (2 * Real.pi * v * X) : ℂ) * T.sineTransform (2 * Real.pi * v) :=
    hS2.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun v => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hodd : ∫ v : ℝ, (Real.cos (2 * Real.pi * v * X) : ℂ) * T.sineTransform (2 * Real.pi * v) = 0 := by
    have h := integral_neg_eq_self
      (fun v : ℝ => (Real.cos (2 * Real.pi * v * X) : ℂ) * T.sineTransform (2 * Real.pi * v)) volume
    have e : (fun v : ℝ => (Real.cos (2 * Real.pi * -v * X) : ℂ) * T.sineTransform (2 * Real.pi * -v)) =
        fun v => -((Real.cos (2 * Real.pi * v * X) : ℂ) * T.sineTransform (2 * Real.pi * v)) := by
      funext v
      rw [show 2 * Real.pi * -v * X = -(2 * Real.pi * v * X) by ring, Real.cos_neg,
        show 2 * Real.pi * -v = -(2 * Real.pi * v) by ring, T.sineTransform_neg]
      ring
    simp only [e, integral_neg] at h
    have : (2 : ℂ) * ∫ v : ℝ, (Real.cos (2 * Real.pi * v * X) : ℂ) * T.sineTransform (2 * Real.pi * v) = 0 := by
      linear_combination -h
    simpa using this
  have hpt : ∀ v : ℝ, cexp (((-2 * Real.pi * v * -X : ℝ) : ℂ) * Complex.I) • 𝓕 T.oddExt v =
      -2 * Complex.I * ((Real.cos (2 * Real.pi * v * X) : ℂ) * T.sineTransform (2 * Real.pi * v)) +
        2 * ((Real.sin (2 * Real.pi * v * X) : ℂ) * T.sineTransform (2 * Real.pi * v)) := fun v => by
    rw [T.fourier_oddExt, smul_eq_mul,
      show ((-2 * Real.pi * v * -X : ℝ) : ℂ) = ((2 * Real.pi * v * X : ℝ) : ℂ) by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    linear_combination (-2 * (Real.sin (2 * Real.pi * v * X) : ℂ) * T.sineTransform (2 * Real.pi * v)) *
      Complex.I_sq
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add (hcos.const_mul _) (hsin.const_mul _),
    integral_const_mul, integral_const_mul, hodd] at hinv
  have hsub := MeasureTheory.Measure.integral_comp_mul_left
    (fun u : ℝ => T.sineTransform u * (Real.sin (X * u) : ℂ)) (2 * Real.pi)
  have e2 : (fun v : ℝ => T.sineTransform (2 * Real.pi * v) * (Real.sin (X * (2 * Real.pi * v)) : ℂ)) =
      fun v => (Real.sin (2 * Real.pi * v * X) : ℂ) * T.sineTransform (2 * Real.pi * v) := by
    funext v; rw [show X * (2 * Real.pi * v) = 2 * Real.pi * v * X by ring]; ring
  simp only [e2] at hsub
  rw [abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), Complex.real_smul] at hsub
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsub' : 2 * (Real.pi : ℂ) *
      ∫ v : ℝ, (Real.sin (2 * Real.pi * v * X) : ℂ) * T.sineTransform (2 * Real.pi * v) =
        ∫ u, T.sineTransform u * (Real.sin (X * u) : ℂ) := by
    rw [hsub]; push_cast; field_simp
  linear_combination (Real.pi : ℂ) * hinv - hsub'

/-- **Sine inversion on the half-line**: `∫_0^∞ S(u) sin(Xu) du = (π/2) ψ(X)` for `X > 0`. -/
theorem integral_Ioi_sineTransform_mul_sin {X : ℝ} (hX : 0 < X) :
    ∫ u in Ioi (0 : ℝ), T.sineTransform u * (Real.sin (X * u) : ℂ) = Real.pi / 2 * T.ψ X := by
  have hint : Integrable fun u => T.sineTransform u * (Real.sin (X * u) : ℂ) :=
    T.integrable_sineTransform.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun u => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have he := _root_.HTGeometry.integral_even_eq_two_mul_complex hint fun u => by
    rw [T.sineTransform_neg, mul_neg, Real.sin_neg]; push_cast; ring
  rw [T.integral_sineTransform_mul_sin, T.oddExt_of_pos hX] at he
  linear_combination -he / 2

/-! ## Membership of the profile `cosh · S(cosh)` in `𝒜_{1/2π}` -/

/-- `cosh(w) S(cosh w) = (i/2) cosh(w) 𝓕χ(cosh w/2π)` lies in `𝒜_{1/2π}`. -/
theorem cosh_mul_sineTransform_cosh_mem :
    (fun w : ℝ => (Real.cosh w : ℂ) * T.sineTransform (Real.cosh w)) ∈
      coshSchwartzSpan (1 / (2 * Real.pi)) := by
  have h := Submodule.smul_mem _ (Complex.I / 2)
    (coshSchwartzTerm_mem (1 / (2 * Real.pi)) 1 0 (𝓕 T.oddExtSchwartz))
  convert h using 1
  funext w
  simp only [Pi.smul_apply, smul_eq_mul, coshSchwartzTerm, pow_one, pow_zero, mul_one]
  rw [T.sineTransform_eq_schwartz]
  ring

/-- `sinh(w) S(cosh w)` lies in `𝒜_{1/2π}`. -/
theorem sinh_mul_sineTransform_cosh_mem :
    (fun w : ℝ => (Real.sinh w : ℂ) * T.sineTransform (Real.cosh w)) ∈
      coshSchwartzSpan (1 / (2 * Real.pi)) := by
  have h := Submodule.smul_mem _ (Complex.I / 2)
    (coshSchwartzTerm_mem (1 / (2 * Real.pi)) 0 1 (𝓕 T.oddExtSchwartz))
  convert h using 1
  funext w
  simp only [Pi.smul_apply, smul_eq_mul, coshSchwartzTerm, pow_one, pow_zero, one_mul]
  rw [T.sineTransform_eq_schwartz]
  ring

end BesselTestFunction

end

end GaloisForLFunctions.HTGeometry
