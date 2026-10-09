import GaloisForLFunctions.HTGeometry.WeightedHolder
import Zeta23.Poisson.PaperFT
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Oscillation bound for hyperbolically weighted windows

Let `φ` be a `C¹` window vanishing for `|u| ≥ L/2` and `a, b ≥ 0`.  One integration by parts
against `sin(Δu)`, in the form `(g′)^(Δ) = −iΔ ĝ(Δ)`, gives

  `|Δ|·|∫ φ² cosh(au) sinh(bu) sin(Δu) du|
      ≤ (2‖φ′c_a‖ + (a + b)‖φc_a‖)‖φs_b‖ + b‖φc_a‖‖φ‖`

(`abs_mul_abs_integral_cosh_sinh_sin_le`).  Here `c_a(u) = cosh(au)`, `s_b(u) = sinh(bu)` and
`‖·‖` is the `L²` norm.  The derivative of `g = φ² c_a s_b` is
`2φφ′c_a s_b + aφ² s_a s_b + bφ² c_a c_b`, and `c_b ≤ 1 + |s_b|`; each piece is then bounded by
Cauchy–Schwarz.  Since `|sinh(bu)| ≥ b|u|`, the last term is at most `C_φ‖φc_a‖‖φs_b‖` with
`C_φ = (∫φ²/∫u²φ²)^{1/2}`, which gives the scale-free form
`|Δ|·|∫…| ≤ (2‖φ′c_a‖ + (a + b + C_φ)‖φc_a‖)‖φs_b‖`
(`abs_mul_abs_integral_cosh_sinh_sin_le_of_moment`).
-/

open MeasureTheory Complex
open Zeta23

namespace RHTower.HyperbolicWindow

noncomputable section

/-- Cauchy–Schwarz for continuous real functions with integrable squares. -/
theorem integral_abs_mul_abs_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf2 : Integrable (fun u => f u ^ 2)) (hg2 : Integrable (fun u => g u ^ 2)) :
    ∫ u, |f u| * |g u| ≤ Real.sqrt (∫ u, f u ^ 2) * Real.sqrt (∫ u, g u ^ 2) := by
  have h := GaloisForLFunctions.HTGeometry.integral_mul_le_sqrt_mul_sqrt_measure
    (μ := volume) (g₁ := fun u => (f u : ℂ)) (g₂ := fun u => (g u : ℂ))
    (Complex.continuous_ofReal.comp hf).aestronglyMeasurable
    (Complex.continuous_ofReal.comp hg).aestronglyMeasurable
    (by simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hf2)
    (by simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hg2)
  simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

variable {L : ℝ}

/-- A continuous function vanishing for `|u| > L/2` is integrable. -/
theorem integrable_of_vanish {F : ℝ → ℝ} (hc : Continuous F) (h : ∀ u, L / 2 < |u| → F u = 0) :
    Integrable F :=
  hc.integrable_of_hasCompactSupport (hasCompactSupport_of_support_subset_abs (Λ := L / 2)
    (fun u hu => by by_contra h'; exact hu (h u (not_le.mp h'))))

theorem deriv_eq_zero_of_vanish {φ : ℝ → ℝ} (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) {u : ℝ}
    (hu : L / 2 < |u|) : deriv φ u = 0 := by
  have h : φ =ᶠ[nhds u] fun _ => (0 : ℝ) := by
    have hopen : IsOpen {v : ℝ | L / 2 < |v|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hu] with v hv
    exact hsupp v hv.le
  rw [h.deriv_eq]
  simp

theorem cosh_le_one_add_abs_sinh (x : ℝ) : Real.cosh x ≤ 1 + |Real.sinh x| := by
  nlinarith [sq_abs (Real.sinh x), abs_nonneg (Real.sinh x), Real.cosh_pos x, Real.cosh_sq x]

/-- **Oscillation bound.** -/
theorem abs_mul_abs_integral_cosh_sinh_sin_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (Δ : ℝ) :
    |Δ| * |∫ u, φ u ^ 2 * Real.cosh (a * u) * Real.sinh (b * u) * Real.sin (Δ * u)| ≤
      (2 * Real.sqrt (∫ u, (deriv φ u * Real.cosh (a * u)) ^ 2) +
          (a + b) * Real.sqrt (∫ u, (φ u * Real.cosh (a * u)) ^ 2)) *
          Real.sqrt (∫ u, (φ u * Real.sinh (b * u)) ^ 2) +
        b * Real.sqrt (∫ u, (φ u * Real.cosh (a * u)) ^ 2) * Real.sqrt (∫ u, φ u ^ 2) := by
  have hφc : Continuous φ := hφ.continuous
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hφd : ∀ u, HasDerivAt φ (deriv φ u) u :=
    fun u => (hφ.differentiable (by norm_num) u).hasDerivAt
  have hz : ∀ u, L / 2 < |u| → φ u = 0 := fun u hu => hsupp u hu.le
  have hz' : ∀ u, L / 2 < |u| → deriv φ u = 0 := fun u hu => deriv_eq_zero_of_vanish hsupp hu
  -- the function and its derivative
  set g : ℝ → ℝ := fun u => φ u ^ 2 * Real.cosh (a * u) * Real.sinh (b * u) with hg
  set g' : ℝ → ℝ := fun u => 2 * φ u * deriv φ u * Real.cosh (a * u) * Real.sinh (b * u) +
      φ u ^ 2 * (a * Real.sinh (a * u)) * Real.sinh (b * u) +
      φ u ^ 2 * Real.cosh (a * u) * (b * Real.cosh (b * u)) with hg'
  have hgd : ∀ u, HasDerivAt g (g' u) u := by
    intro u
    have h1 : HasDerivAt (fun u => φ u ^ 2) (2 * φ u * deriv φ u) u :=
      ((hφd u).pow 2).congr_deriv (by norm_num)
    have h2 : HasDerivAt (fun u => Real.cosh (a * u)) (Real.sinh (a * u) * (a * 1)) u :=
      HasDerivAt.cosh ((hasDerivAt_id' u).const_mul a)
    have h3 : HasDerivAt (fun u => Real.sinh (b * u)) (Real.cosh (b * u) * (b * 1)) u :=
      HasDerivAt.sinh ((hasDerivAt_id' u).const_mul b)
    exact ((h1.mul h2).mul h3).congr_deriv (by simp only [hg', Pi.mul_apply]; ring)
  have hg'c : Continuous g' := by simp only [hg']; fun_prop
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hgz : ∀ u, L / 2 < |u| → g u = 0 := fun u hu => by simp [hg, hz u hu]
  have hg'z : ∀ u, L / 2 < |u| → g' u = 0 := fun u hu => by simp [hg', hz u hu]
  -- the complex lift and one integration by parts
  set G : ℝ → ℂ := fun u => (g u : ℂ) with hG
  have hderivG : deriv G = fun u => (g' u : ℂ) := funext fun u => ((hgd u).ofReal_comp).deriv
  have hgC1 : ContDiff ℝ 1 g := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun u => (hgd u).differentiableAt, ?_⟩
    rw [show deriv g = g' from funext fun u => (hgd u).deriv]
    exact hg'c
  have hGC1 : ContDiff ℝ 1 G := Complex.ofRealCLM.contDiff.comp hgC1
  have hGs : ∀ u, G u ≠ 0 → |u| ≤ L / 2 := by
    intro u hu; by_contra h; exact hu (by simp [hG, hgz u (not_le.mp h)])
  have hG's : ∀ u, deriv G u ≠ 0 → |u| ≤ L / 2 := by
    intro u hu; by_contra h; rw [hderivG] at hu; exact hu (by simp [hg'z u (not_le.mp h)])
  have hibp := paperFT_deriv hGC1 (hasCompactSupport_of_support_subset_abs hGs) (Δ : ℂ)
  have hG'int : Integrable (deriv G) := by
    rw [hderivG]
    exact (Complex.continuous_ofReal.comp hg'c).integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs (Λ := L / 2) (fun u hu => by
        by_contra h; exact hu (by simp [hg'z u (not_le.mp h)])))
  have hnorm := norm_paperFT_le hG'int hG's (Δ : ℂ)
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul] at hnorm
  rw [hibp, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs] at hnorm
  -- the sine integral is the imaginary part of the transform
  have hIm : ∫ u, φ u ^ 2 * Real.cosh (a * u) * Real.sinh (b * u) * Real.sin (Δ * u) =
      (paperFT G Δ).im := by
    have hint : Integrable (fun u => G u * cexp (I * (Δ : ℂ) * u)) := by
      refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
      exact (hasCompactSupport_of_support_subset_abs hGs).mul_right
    have h := integral_im hint
    simp only [RCLike.im_to_complex] at h
    unfold paperFT
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hG, hg]
    rw [show I * (Δ : ℂ) * (u : ℂ) = ((Δ * u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hstep1 : |Δ| * |∫ u, φ u ^ 2 * Real.cosh (a * u) * Real.sinh (b * u) * Real.sin (Δ * u)| ≤
      ∫ u, |g' u| := by
    rw [hIm]
    have h1 := Complex.abs_im_le_norm (paperFT G Δ)
    have h2 : ∫ u, ‖deriv G u‖ = ∫ u, |g' u| := by
      rw [hderivG]; simp [Complex.norm_real, Real.norm_eq_abs]
    calc |Δ| * |(paperFT G Δ).im| ≤ |Δ| * ‖paperFT G Δ‖ :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ ∫ u, ‖deriv G u‖ := hnorm
      _ = _ := h2
  -- pointwise bound for the derivative
  have hpt : ∀ u, |g' u| ≤ 2 * (|deriv φ u * Real.cosh (a * u)| * |φ u * Real.sinh (b * u)|) +
      a * (|φ u * Real.sinh (a * u)| * |φ u * Real.sinh (b * u)|) +
      b * (|φ u * Real.cosh (a * u)| * |φ u|) +
      b * (|φ u * Real.cosh (a * u)| * |φ u * Real.sinh (b * u)|) := by
    intro u
    have hcb := cosh_le_one_add_abs_sinh (b * u)
    have e1 : |2 * φ u * deriv φ u * Real.cosh (a * u) * Real.sinh (b * u)| =
        2 * (|deriv φ u * Real.cosh (a * u)| * |φ u * Real.sinh (b * u)|) := by
      simp only [abs_mul, abs_two]; ring
    have e2 : |φ u ^ 2 * (a * Real.sinh (a * u)) * Real.sinh (b * u)| =
        a * (|φ u * Real.sinh (a * u)| * |φ u * Real.sinh (b * u)|) := by
      simp only [abs_mul, abs_pow, abs_of_nonneg ha]; ring
    have e3 : |φ u ^ 2 * Real.cosh (a * u) * (b * Real.cosh (b * u))| =
        b * (|φ u * Real.cosh (a * u)| * |φ u|) * Real.cosh (b * u) := by
      simp only [abs_mul, abs_pow, abs_of_nonneg hb, abs_of_pos (Real.cosh_pos _)]; ring
    have h3 : b * (|φ u * Real.cosh (a * u)| * |φ u|) * Real.cosh (b * u) ≤
        b * (|φ u * Real.cosh (a * u)| * |φ u|) +
          b * (|φ u * Real.cosh (a * u)| * |φ u * Real.sinh (b * u)|) := by
      have hk : 0 ≤ b * (|φ u * Real.cosh (a * u)| * |φ u|) := by positivity
      have h4 := mul_le_mul_of_nonneg_left hcb hk
      have e : b * (|φ u * Real.cosh (a * u)| * |φ u * Real.sinh (b * u)|) =
          b * (|φ u * Real.cosh (a * u)| * |φ u|) * |Real.sinh (b * u)| := by
        simp only [abs_mul]; ring
      rw [e]; linarith
    have htri : |g' u| ≤ |2 * φ u * deriv φ u * Real.cosh (a * u) * Real.sinh (b * u)| +
        |φ u ^ 2 * (a * Real.sinh (a * u)) * Real.sinh (b * u)| +
        |φ u ^ 2 * Real.cosh (a * u) * (b * Real.cosh (b * u))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    rw [e1, e2, e3] at htri
    linarith
  -- integrability
  have hi1 : Integrable (fun u => |deriv φ u * Real.cosh (a * u)| * |φ u * Real.sinh (b * u)|) :=
    integrable_of_vanish (L := L) (by fun_prop) (fun u hu => by simp [hz u hu])
  have hi2 : Integrable (fun u => |φ u * Real.sinh (a * u)| * |φ u * Real.sinh (b * u)|) :=
    integrable_of_vanish (L := L) (by fun_prop) (fun u hu => by simp [hz u hu])
  have hi3 : Integrable (fun u => |φ u * Real.cosh (a * u)| * |φ u|) :=
    integrable_of_vanish (L := L) (by fun_prop) (fun u hu => by simp [hz u hu])
  have hi4 : Integrable (fun u => |φ u * Real.cosh (a * u)| * |φ u * Real.sinh (b * u)|) :=
    integrable_of_vanish (L := L) (by fun_prop) (fun u hu => by simp [hz u hu])
  have hig' : Integrable (fun u => |g' u|) :=
    integrable_of_vanish (L := L) (by fun_prop) (fun u hu => by simp [hg'z u hu])
  have hS := (((hi1.const_mul 2).add (hi2.const_mul a)).add (hi3.const_mul b)).add (hi4.const_mul b)
  have hmono : ∫ u, |g' u| ≤
      ∫ u, (2 * (|deriv φ u * Real.cosh (a * u)| * |φ u * Real.sinh (b * u)|) +
        a * (|φ u * Real.sinh (a * u)| * |φ u * Real.sinh (b * u)|) +
        b * (|φ u * Real.cosh (a * u)| * |φ u|) +
        b * (|φ u * Real.cosh (a * u)| * |φ u * Real.sinh (b * u)|)) :=
    integral_mono hig' hS hpt
  have j1 : Integrable (fun u => 2 * (|deriv φ u * Real.cosh (a * u)| *
      |φ u * Real.sinh (b * u)|)) := hi1.const_mul 2
  have j2 : Integrable (fun u => a * (|φ u * Real.sinh (a * u)| * |φ u * Real.sinh (b * u)|)) :=
    hi2.const_mul a
  have j3 : Integrable (fun u => b * (|φ u * Real.cosh (a * u)| * |φ u|)) := hi3.const_mul b
  have j4 : Integrable (fun u => b * (|φ u * Real.cosh (a * u)| * |φ u * Real.sinh (b * u)|)) :=
    hi4.const_mul b
  have j12 : Integrable (fun u => 2 * (|deriv φ u * Real.cosh (a * u)| *
      |φ u * Real.sinh (b * u)|) + a * (|φ u * Real.sinh (a * u)| * |φ u * Real.sinh (b * u)|)) :=
    j1.add j2
  have j123 : Integrable (fun u => 2 * (|deriv φ u * Real.cosh (a * u)| *
      |φ u * Real.sinh (b * u)|) + a * (|φ u * Real.sinh (a * u)| * |φ u * Real.sinh (b * u)|) +
      b * (|φ u * Real.cosh (a * u)| * |φ u|)) := j12.add j3
  rw [integral_add j123 j4, integral_add j12 j3, integral_add j1 j2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul] at hmono
  -- Cauchy–Schwarz
  have sq1 : Integrable (fun u => (deriv φ u * Real.cosh (a * u)) ^ 2) :=
    integrable_of_vanish (L := L) (by fun_prop) (fun u hu => by simp [hz' u hu])
  have sqs : Integrable (fun u => (φ u * Real.sinh (b * u)) ^ 2) :=
    integrable_of_vanish (L := L) (by fun_prop) (fun u hu => by simp [hz u hu])
  have sqp : Integrable (fun u => (φ u * Real.sinh (a * u)) ^ 2) :=
    integrable_of_vanish (L := L) (by fun_prop) (fun u hu => by simp [hz u hu])
  have sqq : Integrable (fun u => (φ u * Real.cosh (a * u)) ^ 2) :=
    integrable_of_vanish (L := L) (by fun_prop) (fun u hu => by simp [hz u hu])
  have sqφ : Integrable (fun u => φ u ^ 2) :=
    integrable_of_vanish (L := L) (by fun_prop) (fun u hu => by simp [hz u hu])
  have cs1 := integral_abs_mul_abs_le (f := fun u => deriv φ u * Real.cosh (a * u))
    (g := fun u => φ u * Real.sinh (b * u)) (by fun_prop) (by fun_prop) sq1 sqs
  have cs2 := integral_abs_mul_abs_le (f := fun u => φ u * Real.sinh (a * u))
    (g := fun u => φ u * Real.sinh (b * u)) (by fun_prop) (by fun_prop) sqp sqs
  have cs3 := integral_abs_mul_abs_le (f := fun u => φ u * Real.cosh (a * u))
    (g := fun u => φ u) (by fun_prop) (by fun_prop) sqq sqφ
  have cs4 := integral_abs_mul_abs_le (f := fun u => φ u * Real.cosh (a * u))
    (g := fun u => φ u * Real.sinh (b * u)) (by fun_prop) (by fun_prop) sqq sqs
  have hpq : Real.sqrt (∫ u, (φ u * Real.sinh (a * u)) ^ 2) ≤
      Real.sqrt (∫ u, (φ u * Real.cosh (a * u)) ^ 2) := by
    refine Real.sqrt_le_sqrt (integral_mono sqp sqq (fun u => ?_))
    simp only
    rw [mul_pow, mul_pow, Real.cosh_sq]
    nlinarith [sq_nonneg (φ u)]
  set A' := Real.sqrt (∫ u, (deriv φ u * Real.cosh (a * u)) ^ 2)
  set A := Real.sqrt (∫ u, (φ u * Real.cosh (a * u)) ^ 2)
  set B := Real.sqrt (∫ u, (φ u * Real.sinh (b * u)) ^ 2)
  set P := Real.sqrt (∫ u, φ u ^ 2)
  set Ap := Real.sqrt (∫ u, (φ u * Real.sinh (a * u)) ^ 2)
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have t2 : a * ∫ u, |φ u * Real.sinh (a * u)| * |φ u * Real.sinh (b * u)| ≤ a * (A * B) :=
    mul_le_mul_of_nonneg_left (cs2.trans (mul_le_mul_of_nonneg_right hpq hB0)) ha
  have t3 : b * ∫ u, |φ u * Real.cosh (a * u)| * |φ u| ≤ b * (A * P) :=
    mul_le_mul_of_nonneg_left cs3 hb
  have t4 : b * ∫ u, |φ u * Real.cosh (a * u)| * |φ u * Real.sinh (b * u)| ≤ b * (A * B) :=
    mul_le_mul_of_nonneg_left cs4 hb
  have t1 : 2 * ∫ u, |deriv φ u * Real.cosh (a * u)| * |φ u * Real.sinh (b * u)| ≤ 2 * (A' * B) :=
    mul_le_mul_of_nonneg_left cs1 (by norm_num)
  have e : (2 * A' + (a + b) * A) * B + b * A * P =
      2 * (A' * B) + a * (A * B) + b * (A * P) + b * (A * B) := by ring
  rw [e]
  linarith

/-- **Scale-free oscillation bound.**  With `C_φ = (∫φ²/∫u²φ²)^{1/2}`,
`|Δ|·|∫ φ² cosh(au) sinh(bu) sin(Δu)| ≤ (2‖φ′c_a‖ + (a + b + C_φ)‖φc_a‖)‖φs_b‖`. -/
theorem abs_mul_abs_integral_cosh_sinh_sin_le_of_moment {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (Δ : ℝ)
    (hm : 0 < ∫ u, (u * φ u) ^ 2) :
    |Δ| * |∫ u, φ u ^ 2 * Real.cosh (a * u) * Real.sinh (b * u) * Real.sin (Δ * u)| ≤
      (2 * Real.sqrt (∫ u, (deriv φ u * Real.cosh (a * u)) ^ 2) +
          (a + b + Real.sqrt ((∫ u, φ u ^ 2) / ∫ u, (u * φ u) ^ 2)) *
            Real.sqrt (∫ u, (φ u * Real.cosh (a * u)) ^ 2)) *
        Real.sqrt (∫ u, (φ u * Real.sinh (b * u)) ^ 2) := by
  have h := abs_mul_abs_integral_cosh_sinh_sin_le hφ hsupp ha hb Δ
  have hφc : Continuous φ := hφ.continuous
  have hz : ∀ u, L / 2 < |u| → φ u = 0 := fun u hu => hsupp u hu.le
  set A' := Real.sqrt (∫ u, (deriv φ u * Real.cosh (a * u)) ^ 2)
  set A := Real.sqrt (∫ u, (φ u * Real.cosh (a * u)) ^ 2)
  set B := Real.sqrt (∫ u, (φ u * Real.sinh (b * u)) ^ 2)
  set M := ∫ u, (u * φ u) ^ 2
  set P := ∫ u, φ u ^ 2
  have hP : 0 ≤ P := integral_nonneg fun u => sq_nonneg _
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : b * Real.sqrt M ≤ B := by
    have hmono : ∫ u, (b * (u * φ u)) ^ 2 ≤ ∫ u, (φ u * Real.sinh (b * u)) ^ 2 := by
      refine integral_mono
        (integrable_of_vanish (L := L) (by fun_prop) (fun u hu => by simp [hz u hu]))
        (integrable_of_vanish (L := L) (by fun_prop) (fun u hu => by simp [hz u hu]))
        (fun u => ?_)
      have hs : |b * u| ≤ |Real.sinh (b * u)| := by
        rw [Real.abs_sinh]; exact Real.self_le_sinh_iff.mpr (abs_nonneg _)
      have h2 : (b * u) ^ 2 ≤ Real.sinh (b * u) ^ 2 := by
        rw [← sq_abs (b * u), ← sq_abs (Real.sinh (b * u))]
        exact pow_le_pow_left₀ (abs_nonneg _) hs 2
      calc (b * (u * φ u)) ^ 2 = (b * u) ^ 2 * φ u ^ 2 := by ring
        _ ≤ Real.sinh (b * u) ^ 2 * φ u ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = (φ u * Real.sinh (b * u)) ^ 2 := by ring
    have e : ∫ u, (b * (u * φ u)) ^ 2 = b ^ 2 * M := by
      rw [← integral_const_mul]; congr 1; funext u; ring
    rw [e] at hmono
    calc b * Real.sqrt M = Real.sqrt (b ^ 2 * M) := by
          rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb]
      _ ≤ B := Real.sqrt_le_sqrt hmono
  have hC : Real.sqrt (P / M) * Real.sqrt M = Real.sqrt P := by
    rw [← Real.sqrt_mul (div_nonneg hP hm.le), div_mul_cancel₀ P hm.ne']
  have hbP : b * A * Real.sqrt P ≤ Real.sqrt (P / M) * A * B := by
    calc b * A * Real.sqrt P = A * Real.sqrt (P / M) * (b * Real.sqrt M) := by
          rw [← hC]; ring
      _ ≤ A * Real.sqrt (P / M) * B :=
          mul_le_mul_of_nonneg_left hB (mul_nonneg hA (Real.sqrt_nonneg _))
      _ = Real.sqrt (P / M) * A * B := by ring
  have e : (2 * A' + (a + b + Real.sqrt (P / M)) * A) * B =
      (2 * A' + (a + b) * A) * B + Real.sqrt (P / M) * A * B := by ring
  rw [e]
  linarith

end

end RHTower.HyperbolicWindow
