import GaloisForLFunctions.RHTower.XiSliceSaddleArcBoundsEulerRegion
import GaloisForLFunctions.RHTower.XiSliceCoeffQuarterArc

/-!
# Saddle data for the slice around an off-centre point

For a real centre `x₀` let `f(w) = g_t(x₀ + w)` be the slice `g_t(x) = ξ(½+x+it) ξ(½−x+it)` seen
from `x₀` (`xiSliceShift`).  This file sets up the saddle-point analysis of the Taylor coefficients
of `g_t` at `x₀`.

* **Half-circle formula** (`iteratedDeriv_xiSliceProduct_eq_half_circle`).  For `R > 0` with
  `x₀ + R > ½`,

    `g_t^{(n)}(x₀)/n! = (g_t(x₀+R)/(π Rⁿ)) ∫₀^π Re G(θ) dθ`,

  where `G(θ) = f(Re^{iθ}) e^{−inθ}/f(R)` is the normalised arc value.  It follows from Cauchy's
  formula on `|w| = R`, the `2π`-periodicity of `G` and the conjugation symmetry
  `G(−θ) = conj G(θ)` (the slice is real on the real axis).
* **Logarithmic derivative** (`scaledLogDeriv_xiSliceShift`).  On `x₀ + Re w > ½`,
  `w f'(w)/f(w) = w L(x₀ + w)` with `L = ξ'/ξ(½+·+it) + ξ'/ξ(½+·−it)` (`xiSliceLogDeriv`).
* **Saddle radius** (`exists_saddle_radius_shift`).  If `x₀ + a ≥ ½ + η`, `x₀ + b ≤ t/2` and
  `a(log t + 2C_η) ≤ n ≤ b(log(t/2) − 2C_η)`, some `R ∈ [a, b]` has `R L(x₀ + R) = n`.
* **Saddle-arc and slope bounds** (`xiSliceShift_saddleArc_bounds`, `xiSliceShift_saddleSlope_bounds`).
  If `x₀ + R ≥ ½ + 2η`, the generic saddle-arc control (`HTGeometry.saddleArc_bounds`) applies on
  the disc of radius `η` about `R`, with the same disc constant as at the centre `0`
  (`xiSliceDiscConstantEuler η t R`), and the slope `F'(R)` lies within `R(log 4 + π + 4C_η)/η` of
  `L(x₀ + R)`.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- The slice seen from the real point `x₀`: `w ↦ g_t(x₀ + w)`. -/
def xiSliceShift (t x₀ : ℝ) (w : ℂ) : ℂ := xiSliceProduct t ((x₀ : ℂ) + w)

theorem differentiable_xiSliceShift (t x₀ : ℝ) : Differentiable ℂ (xiSliceShift t x₀) :=
  fun w => (differentiable_xiSliceProduct t ((x₀ : ℂ) + w)).comp w
    ((differentiable_const _).add differentiable_id w)

theorem xiSliceShift_ne_zero {t x₀ : ℝ} {w : ℂ} (hw : 1 / 2 < x₀ + w.re) :
    xiSliceShift t x₀ w ≠ 0 :=
  xiSliceProduct_ne_zero_of_re (by simpa using hw)

theorem iteratedDeriv_xiSliceShift_zero (t x₀ : ℝ) (n : ℕ) :
    iteratedDeriv n (xiSliceShift t x₀) 0 = iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ) := by
  have h := congrFun (iteratedDeriv_comp_const_add n (xiSliceProduct t) (x₀ : ℂ)) 0
  show iteratedDeriv n (fun z => xiSliceProduct t ((x₀ : ℂ) + z)) 0 = _
  simpa using h

/-- `w f'(w)/f(w) = w L(x₀ + w)` on `x₀ + Re w > ½`. -/
theorem scaledLogDeriv_xiSliceShift {t x₀ : ℝ} {w : ℂ} (hw : 1 / 2 < x₀ + w.re) :
    HTGeometry.scaledLogDeriv (xiSliceShift t x₀) w = w * xiSliceLogDeriv t ((x₀ : ℂ) + w) := by
  have hz : 1 / 2 < ((x₀ : ℂ) + w).re := by simpa using hw
  have hS := scaledLogDeriv_xiSliceProduct (t := t) hz
  have hne : xiSliceProduct t ((x₀ : ℂ) + w) ≠ 0 := xiSliceProduct_ne_zero_of_re hz
  have hz0 : (x₀ : ℂ) + w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  unfold HTGeometry.scaledLogDeriv at hS ⊢
  have hd : deriv (xiSliceShift t x₀) w = deriv (xiSliceProduct t) ((x₀ : ℂ) + w) :=
    deriv_comp_const_add (xiSliceProduct t) (x₀ : ℂ) w
  rw [hd, show xiSliceShift t x₀ w = xiSliceProduct t ((x₀ : ℂ) + w) from rfl]
  have hL : deriv (xiSliceProduct t) ((x₀ : ℂ) + w) / xiSliceProduct t ((x₀ : ℂ) + w)
      = xiSliceLogDeriv t ((x₀ : ℂ) + w) := by
    field_simp at hS
    field_simp
    linear_combination hS
  rw [mul_div_assoc, hL]

/-- On the real axis the shifted scaled logarithmic derivative is real. -/
theorem im_scaledLogDeriv_xiSliceShift_ofReal {t x₀ x : ℝ} (hx : 1 / 2 < x₀ + x) :
    (HTGeometry.scaledLogDeriv (xiSliceShift t x₀) (x : ℂ)).im = 0 := by
  rw [scaledLogDeriv_xiSliceShift (by simpa using hx)]
  have h0 := im_scaledLogDeriv_xiSliceProduct_ofReal (t := t) hx
  rw [scaledLogDeriv_xiSliceProduct (by simpa using hx)] at h0
  have hL : (xiSliceLogDeriv t ((x₀ + x : ℝ) : ℂ)).im = 0 := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left (by linarith)
  rw [show ((x₀ : ℂ) + (x : ℂ)) = ((x₀ + x : ℝ) : ℂ) by push_cast; ring, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, hL]
  simp

/-- **Saddle radius.** -/
theorem exists_saddle_radius_shift {t η x₀ a b : ℝ} (hη : 0 < η) (ht : 8 ≤ t)
    (ha : 1 / 2 + η ≤ x₀ + a) (ha0 : 0 ≤ a) (hab : a ≤ b) (hbt : x₀ + b ≤ t / 2) {n : ℕ}
    (hlo : a * (Real.log t + 2 * xiEulerConstant η) ≤ n)
    (hhi : (n : ℝ) ≤ b * (Real.log (t / 2) - 2 * xiEulerConstant η)) :
    ∃ R ∈ Set.Icc a b, (HTGeometry.scaledLogDeriv (xiSliceShift t x₀) R).re = n := by
  set φ : ℝ → ℝ := fun R => R * (xiSliceLogDeriv t ((x₀ + R : ℝ) : ℂ)).re with hφ
  have hcont : ContinuousOn φ (Set.Icc a b) := by
    have hL : ContinuousOn (fun R : ℝ => xiSliceLogDeriv t ((x₀ + R : ℝ) : ℂ)) (Set.Icc a b) := by
      refine (differentiableOn_xiSliceLogDeriv t).continuousOn.comp
        (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).continuousOn ?_
      intro R hR
      show 1 / 2 < ((x₀ + R : ℝ) : ℂ).re
      simp
      linarith [hR.1]
    exact continuousOn_id.mul (Complex.continuous_re.comp_continuousOn hL)
  have ha' : φ a ≤ n := by
    obtain ⟨-, -, hhia⟩ := xiSliceLogDeriv_real_bounds_euler (t := t) (R := x₀ + a) hη ht ha
      (by linarith)
    simp only [hφ]
    have := mul_le_mul_of_nonneg_left hhia ha0
    linarith
  have hb' : (n : ℝ) ≤ φ b := by
    obtain ⟨-, hlob, -⟩ := xiSliceLogDeriv_real_bounds_euler (t := t) (R := x₀ + b) hη ht
      (by linarith) hbt
    simp only [hφ]
    have := mul_le_mul_of_nonneg_left hlob (by linarith : (0 : ℝ) ≤ b)
    linarith
  obtain ⟨R, hR, hRn⟩ := intermediate_value_Icc hab hcont ⟨ha', hb'⟩
  refine ⟨R, hR, ?_⟩
  rw [scaledLogDeriv_xiSliceShift (by simp; linarith [hR.1])]
  rw [show ((x₀ : ℂ) + (R : ℂ)) = ((x₀ + R : ℝ) : ℂ) by push_cast; ring, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact hRn

/-- **Saddle-arc control around an off-centre point.** -/
theorem xiSliceShift_saddleArc_bounds {t x₀ R η θ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (ht : 8 ≤ t) (hR0 : 0 < R) (hR : 1 / 2 + 2 * η ≤ x₀ + R) (hRt : x₀ + R ≤ t / 2) (hθ0 : 0 ≤ θ)
    (hθ : R * θ ≤ η / 2) :
    ‖HTGeometry.saddleArc (xiSliceShift t x₀) R
        (HTGeometry.scaledLogDeriv (xiSliceShift t x₀) R).re θ‖
        ≤ Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re * R
            * (1 - Real.cos θ)) + 32 * xiSliceDiscConstantEuler η t R / η ^ 2 * R ^ 2 * θ ^ 3 / 3)
      ∧ (|(deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re| * R * θ ^ 3 / 6
            + 32 * xiSliceDiscConstantEuler η t R / η ^ 2 * R ^ 2 * θ ^ 3 / 3 ≤ Real.pi / 2 →
        Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re * R
            * (1 - Real.cos θ)) - 32 * xiSliceDiscConstantEuler η t R / η ^ 2 * R ^ 2 * θ ^ 3 / 3)
          * Real.cos (|(deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re| * R * θ ^ 3 / 6
            + 32 * xiSliceDiscConstantEuler η t R / η ^ 2 * R ^ 2 * θ ^ 3 / 3)
        ≤ (HTGeometry.saddleArc (xiSliceShift t x₀) R
            (HTGeometry.scaledLogDeriv (xiSliceShift t x₀) R).re θ).re) := by
  set U : Set ℂ := {w : ℂ | 1 / 2 < x₀ + w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_const.add Complex.continuous_re)
  have hball : closedBall (R : ℂ) η ⊆ U := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hw)).1
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    show 1 / 2 < x₀ + w.re
    linarith
  apply HTGeometry.saddleArc_bounds hUo (differentiable_xiSliceShift t x₀).differentiableOn
    (fun w hw => xiSliceShift_ne_zero hw) hR0 hη hball
  · intro w hw
    have hwU : 1 / 2 < x₀ + w.re := hball hw
    have hRU : 1 / 2 < x₀ + (R : ℂ).re := by simp; linarith
    rw [scaledLogDeriv_xiSliceShift hwU, scaledLogDeriv_xiSliceShift hRU]
    have hw' : (x₀ : ℂ) + w ∈ closedBall (((x₀ + R : ℝ)) : ℂ) η := by
      rw [mem_closedBall, dist_eq_norm] at hw ⊢
      rwa [show (x₀ : ℂ) + w - ((x₀ + R : ℝ) : ℂ) = w - R by push_cast; ring]
    obtain ⟨h1, h2⟩ := xiSliceLogDeriv_disc_bounds_euler hη hη1 ht hR hRt hw'
    have hxR : ((x₀ + R : ℝ) : ℂ) = (x₀ : ℂ) + R := by push_cast; ring
    rw [hxR] at h2
    have hwR : ‖w - R‖ ≤ η := by rwa [mem_closedBall, dist_eq_norm] at hw
    have e : w * xiSliceLogDeriv t ((x₀ : ℂ) + w) - R * xiSliceLogDeriv t ((x₀ : ℂ) + R)
        = (w - R) * xiSliceLogDeriv t ((x₀ : ℂ) + w)
          + R * (xiSliceLogDeriv t ((x₀ : ℂ) + w) - xiSliceLogDeriv t ((x₀ : ℂ) + R)) := by ring
    rw [e]
    calc _ ≤ ‖(w - R) * xiSliceLogDeriv t ((x₀ : ℂ) + w)‖
          + ‖(R : ℂ) * (xiSliceLogDeriv t ((x₀ : ℂ) + w) - xiSliceLogDeriv t ((x₀ : ℂ) + R))‖ :=
          norm_add_le _ _
      _ = ‖w - R‖ * ‖xiSliceLogDeriv t ((x₀ : ℂ) + w)‖
          + R * ‖xiSliceLogDeriv t ((x₀ : ℂ) + w) - xiSliceLogDeriv t ((x₀ : ℂ) + R)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
      _ ≤ η * (Real.log (3 * t / 2) + Real.pi / 2 + 2 * xiEulerConstant η)
          + R * (Real.log 4 + Real.pi + 4 * xiEulerConstant η) := by
          gcongr
      _ = xiSliceDiscConstantEuler η t R := by unfold xiSliceDiscConstantEuler; ring
  · intro x hx
    have h : 1 / 2 < x₀ + x := by
      have := hx
      simp only [hU, Set.mem_setOf_eq, Complex.ofReal_re] at this
      exact this
    exact im_scaledLogDeriv_xiSliceShift_ofReal h
  · exact hθ0
  · exact hθ

/-- **The saddle slope around an off-centre point.** -/
theorem xiSliceShift_saddleSlope_bounds {t x₀ R η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (ht : 8 ≤ t) (hR0 : 0 < R) (hR : 1 / 2 + 2 * η ≤ x₀ + R) (hRt : x₀ + R ≤ t / 2) :
    Real.log (t / 2) - 2 * xiEulerConstant η
        - R * (Real.log 4 + Real.pi + 4 * xiEulerConstant η) / η
      ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re
    ∧ (deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re
      ≤ Real.log t + 2 * xiEulerConstant η
        + R * (Real.log 4 + Real.pi + 4 * xiEulerConstant η) / η := by
  set V : Set ℂ := {w : ℂ | 1 / 2 < w.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  set c : ℂ := ((x₀ + R : ℝ) : ℂ) with hc
  have hcV : c ∈ V := by show 1 / 2 < c.re; simp [hc]; linarith
  have hball : closedBall c η ⊆ V := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hw)).1
    simp only [Complex.sub_re, hc, Complex.ofReal_re] at this
    show 1 / 2 < w.re
    linarith
  have hLd := differentiableOn_xiSliceLogDeriv t
  have hev : HTGeometry.scaledLogDeriv (xiSliceShift t x₀) =ᶠ[nhds (R : ℂ)]
      fun w => w * xiSliceLogDeriv t ((x₀ : ℂ) + w) := by
    have hUo : IsOpen {w : ℂ | 1 / 2 < x₀ + w.re} :=
      isOpen_lt continuous_const (continuous_const.add Complex.continuous_re)
    have hRU : (R : ℂ) ∈ {w : ℂ | 1 / 2 < x₀ + w.re} := by
      show 1 / 2 < x₀ + (R : ℂ).re
      simp
      linarith
    filter_upwards [hUo.mem_nhds hRU] with w hw
    exact scaledLogDeriv_xiSliceShift hw
  have hcx : (x₀ : ℂ) + R = c := by rw [hc]; push_cast; ring
  have hLR : HasDerivAt (xiSliceLogDeriv t) (deriv (xiSliceLogDeriv t) c) c :=
    (hLd.differentiableAt (hVo.mem_nhds hcV)).hasDerivAt
  have hderiv : deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R
      = xiSliceLogDeriv t c + R * deriv (xiSliceLogDeriv t) c := by
    rw [hev.deriv_eq]
    have hLR' : HasDerivAt (xiSliceLogDeriv t) (deriv (xiSliceLogDeriv t) c) ((x₀ : ℂ) + R) := by
      rw [hcx]
      exact hLR
    have hshift : HasDerivAt (fun w : ℂ => xiSliceLogDeriv t ((x₀ : ℂ) + w))
        (deriv (xiSliceLogDeriv t) c) (R : ℂ) := by
      have h := hLR'.comp (R : ℂ) ((hasDerivAt_id' (R : ℂ)).const_add (x₀ : ℂ))
      simpa [Function.comp_def] using h
    have := (hasDerivAt_id' (R : ℂ)).mul hshift
    exact this.deriv.trans (by rw [hcx]; ring)
  have hcauchy : ‖deriv (xiSliceLogDeriv t) c‖
      ≤ (Real.log 4 + Real.pi + 4 * xiEulerConstant η) / η :=
    HTGeometry.norm_deriv_le_of_norm_sub_le hLd (c := c) hη hball
      (fun z hz => (xiSliceLogDeriv_disc_bounds_euler hη hη1 ht hR hRt
        (sphere_subset_closedBall hz)).2)
  obtain ⟨-, hlo, hhi⟩ := xiSliceLogDeriv_real_bounds_euler hη ht (by linarith) hRt
  have hRd : |(R * deriv (xiSliceLogDeriv t) c : ℂ).re|
      ≤ R * (Real.log 4 + Real.pi + 4 * xiEulerConstant η) / η := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    calc R * ‖deriv (xiSliceLogDeriv t) c‖
        ≤ R * ((Real.log 4 + Real.pi + 4 * xiEulerConstant η) / η) := by gcongr
      _ = R * (Real.log 4 + Real.pi + 4 * xiEulerConstant η) / η := by ring
  rw [hderiv, Complex.add_re]
  have := abs_le.mp hRd
  constructor <;> linarith [this.1, this.2]

/-- **Cauchy's formula on the circle `|w| = R` about `x₀`.** -/
theorem iteratedDeriv_xiSliceProduct_eq_circle (t x₀ : ℝ) (n : ℕ) {R : ℝ} (hR : 0 < R) :
    ((n.factorial : ℂ))⁻¹ * iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)
      = ((2 * Real.pi * R ^ n : ℝ) : ℂ)⁻¹
        * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(((n : ℝ) * θ : ℝ) : ℂ) * I)
            * xiSliceShift t x₀ ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
  have hg := differentiable_xiSliceShift t x₀
  rw [← iteratedDeriv_xiSliceShift_zero]
  rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_eq_circleIntegral hR n hg.continuous.continuousOn
    (fun ζ _ => hg ζ)]
  unfold circleIntegral
  have hpt : ∀ θ : ℝ, deriv (circleMap 0 R) θ
      • ((1 / (circleMap 0 R θ - 0) ^ (n + 1)) • xiSliceShift t x₀ (circleMap 0 R θ))
      = (I / (R : ℂ) ^ n) * (Complex.exp (-(((n : ℝ) * θ : ℝ) : ℂ) * I)
          * xiSliceShift t x₀ ((R : ℂ) * Complex.exp ((θ : ℂ) * I))) := by
    intro θ
    rw [deriv_circleMap]
    simp only [circleMap, zero_add, sub_zero, smul_eq_mul]
    have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    have hE : Complex.exp ((θ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
    have key : Complex.exp (-(((n : ℝ) * θ : ℝ) : ℂ) * I) * Complex.exp ((θ : ℂ) * I) ^ n = 1 := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      convert Complex.exp_zero using 2
      push_cast
      ring
    have hEinv : Complex.exp (-(((n : ℝ) * θ : ℝ) : ℂ) * I) = (Complex.exp ((θ : ℂ) * I) ^ n)⁻¹ :=
      eq_inv_of_mul_eq_one_left key
    rw [hEinv]
    field_simp
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, smul_eq_mul]
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfac : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  push_cast
  field_simp

/-- The arc value at `−θ` is the conjugate of the arc value at `θ`. -/
theorem saddleArc_xiSliceShift_neg (t x₀ R θ : ℝ) (n : ℕ) :
    HTGeometry.saddleArc (xiSliceShift t x₀) R n (-θ)
      = (starRingEnd ℂ) (HTGeometry.saddleArc (xiSliceShift t x₀) R n θ) := by
  unfold HTGeometry.saddleArc xiSliceShift
  have h1 : (x₀ : ℂ) + (R : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * I)
      = (starRingEnd ℂ) ((x₀ : ℂ) + (R : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
  have h2 : Complex.exp (-((((n : ℝ) * (-θ) : ℝ)) : ℂ) * I)
      = (starRingEnd ℂ) (Complex.exp (-((((n : ℝ) * θ : ℝ)) : ℂ) * I)) := by
    rw [← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
  have h3 : xiSliceProduct t ((x₀ : ℂ) + (R : ℂ))
      = (starRingEnd ℂ) (xiSliceProduct t ((x₀ : ℂ) + (R : ℂ))) := by
    rw [← xiSliceProduct_conj, map_add, Complex.conj_ofReal, Complex.conj_ofReal]
  rw [h1, h2, xiSliceProduct_conj, map_div₀, map_mul, ← h3]

theorem saddleArc_xiSliceShift_add_two_pi (t x₀ R θ : ℝ) (n : ℕ) :
    HTGeometry.saddleArc (xiSliceShift t x₀) R n (θ + 2 * Real.pi)
      = HTGeometry.saddleArc (xiSliceShift t x₀) R n θ := by
  unfold HTGeometry.saddleArc
  have h1 : Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * I) = Complex.exp ((θ : ℂ) * I) := by
    rw [show (((θ + 2 * Real.pi : ℝ) : ℂ) * I) = (θ : ℂ) * I + 2 * Real.pi * I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have h2 : Complex.exp (-((((n : ℝ) * (θ + 2 * Real.pi) : ℝ)) : ℂ) * I)
      = Complex.exp (-((((n : ℝ) * θ : ℝ)) : ℂ) * I) := by
    have hk : Complex.exp ((((-(n : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * I)) = 1 :=
      Complex.exp_int_mul_two_pi_mul_I _
    rw [show (-((((n : ℝ) * (θ + 2 * Real.pi) : ℝ)) : ℂ) * I)
        = -((((n : ℝ) * θ : ℝ)) : ℂ) * I + (((-(n : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, hk, mul_one]
  rw [h1, h2]

/-- **Half-circle formula.**  For `R > 0` with `x₀ + R > ½`,
`g_t^{(n)}(x₀)/n! = (|ξ(½+x₀+R+it)|²/(π Rⁿ)) ∫₀^π Re G(θ) dθ`. -/
theorem iteratedDeriv_xiSliceProduct_eq_half_circle (t x₀ : ℝ) (n : ℕ) {R : ℝ} (hR : 0 < R)
    (hxR : 1 / 2 < x₀ + R) :
    ((n.factorial : ℂ))⁻¹ * iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)
      = ((‖xi (((1 / 2 + (x₀ + R) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 / (Real.pi * R ^ n)
          * ∫ θ in (0 : ℝ)..Real.pi,
            (HTGeometry.saddleArc (xiSliceShift t x₀) R n θ).re : ℝ) : ℂ) := by
  rw [iteratedDeriv_xiSliceProduct_eq_circle t x₀ n hR]
  have hne : xiSliceShift t x₀ (R : ℂ) ≠ 0 := xiSliceShift_ne_zero (by simpa using hxR)
  have harc : ∀ θ : ℝ, Complex.exp (-(((n : ℝ) * θ : ℝ) : ℂ) * I)
      * xiSliceShift t x₀ ((R : ℂ) * Complex.exp ((θ : ℂ) * I))
      = xiSliceShift t x₀ (R : ℂ) * HTGeometry.saddleArc (xiSliceShift t x₀) R n θ := by
    intro θ
    unfold HTGeometry.saddleArc
    field_simp
  simp_rw [harc]
  set S : ℝ → ℂ := fun θ => HTGeometry.saddleArc (xiSliceShift t x₀) R n θ with hSdef
  have hSc : Continuous S := by
    have hg := differentiable_xiSliceShift t x₀
    simp only [hSdef, HTGeometry.saddleArc]
    have : Continuous fun θ : ℝ => xiSliceShift t x₀ ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      hg.continuous.comp (by fun_prop)
    fun_prop
  rw [intervalIntegral.integral_const_mul]
  have hi : ∀ a b : ℝ, IntervalIntegrable S MeasureTheory.volume a b := fun a b =>
    hSc.intervalIntegrable a b
  -- `∫₀^{2π} S = ∫₀^π (S + conj S) = 2 ∫₀^π Re S`
  have hsecond : ∫ θ in Real.pi..(2 * Real.pi), S θ
      = ∫ θ in (0 : ℝ)..Real.pi, (starRingEnd ℂ) (S θ) := by
    have h1 := intervalIntegral.integral_comp_add_right S (2 * Real.pi) (a := -Real.pi) (b := 0)
    simp only [hSdef, saddleArc_xiSliceShift_add_two_pi] at h1
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at h1
    rw [← h1]
    have h2 := intervalIntegral.integral_comp_neg (fun θ => S θ) (a := 0) (b := Real.pi)
    simp only [neg_zero] at h2
    rw [← h2]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hSdef]
    rw [saddleArc_xiSliceShift_neg]
  have hsplit : ∫ θ in (0 : ℝ)..(2 * Real.pi), S θ
      = ((2 * ∫ θ in (0 : ℝ)..Real.pi, (S θ).re : ℝ) : ℂ) := by
    have hic : IntervalIntegrable (fun θ => (starRingEnd ℂ) (S θ)) MeasureTheory.volume 0 Real.pi :=
      (Complex.continuous_conj.comp hSc).intervalIntegrable 0 Real.pi
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 Real.pi) (hi Real.pi (2 * Real.pi)),
      hsecond, ← intervalIntegral.integral_add (hi 0 Real.pi) hic]
    have e : ∀ θ, S θ + (starRingEnd ℂ) (S θ) = ((2 * (S θ).re : ℝ) : ℂ) := by
      intro θ
      rw [Complex.add_conj]
    simp_rw [e]
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
  rw [hsplit]
  have hval : xiSliceShift t x₀ (R : ℂ)
      = ((‖xi (((1 / 2 + (x₀ + R) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) := by
    unfold xiSliceShift
    rw [show (x₀ : ℂ) + (R : ℂ) = ((x₀ + R : ℝ) : ℂ) by push_cast; ring, xiSliceProduct_ofReal_eq]
  rw [hval]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hRn : R ^ n ≠ 0 := pow_ne_zero _ hR.ne'
  push_cast
  field_simp
  ring

end

end RHTower
