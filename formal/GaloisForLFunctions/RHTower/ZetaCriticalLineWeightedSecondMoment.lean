import GaloisForLFunctions.RHTower.FractionalPartSquareIntegral
import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments
import GaloisForLFunctions.RHTower.ZetaMollifiedCriticalLineJensen

/-!
# The weighted second moment of `ζ` on the critical line

`(1/2π) ∫_ℝ |ζ(½ + it)|² dt/(¼ + t²) = log 2π - γ`.

For `0 < Re s < 1`, `-ζ(s)/s = ∫_0^∞ {x} x^{-s-1} dx`, the Mellin transform of `y ↦ {1/y}`.  On
`Re s = ½` this is the Fourier transform of `φ(u) = e^{-u/2} {e^u}` at `t/2π`, and
`|φ(u)| ≤ e^{-|u|/2}`, so `φ` is integrable and square integrable.  Plancherel gives
`(1/2π) ∫ |ζ(½+it)|²/|½+it|² dt = ∫ |φ|² = ∫_0^∞ {x}²/x² dx = log 2π - γ`.

With the mollified Balazard–Saias–Yor inequality at `M = 1` this yields the unconditional bound
`Σ_{Re ρ > ½} log (|ρ|/|1 - ρ|) ≤ ½ log (log 2π - γ)` over every finite set of zeros.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

/-- `φ(u) = e^{-u/2} {e^u}`. -/
def fractLogPull (u : ℝ) : ℂ := ((Real.exp (-(u / 2)) * Int.fract (Real.exp u) : ℝ) : ℂ)

theorem norm_fractLogPull (u : ℝ) :
    ‖fractLogPull u‖ = Real.exp (-(u / 2)) * Int.fract (Real.exp u) := by
  rw [fractLogPull, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _))]

theorem norm_fractLogPull_le (u : ℝ) : ‖fractLogPull u‖ ≤ Real.exp (-(1 / 2) * |u|) := by
  rw [norm_fractLogPull]
  have h0 := Int.fract_nonneg (Real.exp u)
  have h1 := (Int.fract_lt_one (Real.exp u)).le
  have h2 : Int.fract (Real.exp u) ≤ Real.exp u := by
    have := Int.floor_nonneg.mpr (Real.exp_pos u).le
    unfold Int.fract
    have : (0 : ℝ) ≤ (⌊Real.exp u⌋ : ℝ) := by exact_mod_cast this
    linarith
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    calc Real.exp (-(u / 2)) * Int.fract (Real.exp u) ≤ Real.exp (-(u / 2)) * 1 :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (-(1 / 2) * u) := by ring_nf
  · rw [abs_of_neg hu]
    calc Real.exp (-(u / 2)) * Int.fract (Real.exp u)
        ≤ Real.exp (-(u / 2)) * Real.exp u := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = Real.exp (-(1 / 2) * -u) := by rw [← Real.exp_add]; ring_nf

theorem measurable_fractLogPull : Measurable fractLogPull :=
  Complex.measurable_ofReal.comp
    ((Real.measurable_exp.comp (measurable_id.div_const 2).neg).mul
      (measurable_fract.comp Real.measurable_exp))

theorem integrable_fractLogPull : Integrable fractLogPull := by
  have h := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0
    (r := 1 / 2) (by norm_num)
  have h' : Integrable (fun u : ℝ => Real.exp (-(1 / 2) * |u|)) :=
    h.congr (Filter.Eventually.of_forall fun u => by simp)
  exact Integrable.mono' h' measurable_fractLogPull.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => norm_fractLogPull_le u)

theorem memLp_two_fractLogPull : MemLp fractLogPull 2 := by
  rw [memLp_two_iff_integrable_sq_norm measurable_fractLogPull.aestronglyMeasurable]
  refine Integrable.mono' integrable_fractLogPull.norm
    (measurable_fractLogPull.norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  have h1 : ‖fractLogPull u‖ ≤ 1 := by
    rw [norm_fractLogPull]
    have := Int.fract_lt_one (Real.exp u)
    have h0 := Int.fract_nonneg (Real.exp u)
    have he : Real.exp (-(u / 2)) * Int.fract (Real.exp u) ≤ Real.exp (-(u / 2)) * 1 :=
      mul_le_mul_of_nonneg_left this.le (Real.exp_pos _).le
    calc Real.exp (-(u / 2)) * Int.fract (Real.exp u) ≤ ‖fractLogPull u‖ := by
          rw [norm_fractLogPull]
      _ ≤ 1 := by
          have := norm_fractLogPull_le u
          have h2 : Real.exp (-(1 / 2) * |u|) ≤ 1 := Real.exp_le_one_iff.mpr (by
            have := abs_nonneg u; nlinarith)
          linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [norm_nonneg (fractLogPull u)]

/-- **The Fourier transform of `φ` is `-ζ(s)/s` on the critical line.** -/
theorem fourier_fractLogPull (t : ℝ) :
    𝓕 fractLogPull (t / (2 * π))
      = -(riemannZeta (1 / 2 + t * I) / (1 / 2 + t * I)) := by
  set s : ℂ := 1 / 2 + t * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have him : s.im = t := by simp [hs]
  have h := mellin_eq_fourier (fun y : ℝ => ((Int.fract y⁻¹ : ℝ) : ℂ)) (s := s)
  rw [hre, him] at h
  have hfun : (fun u : ℝ => Real.exp (-(1 / 2) * u) • ((Int.fract (Real.exp (-u))⁻¹ : ℝ) : ℂ))
      = fractLogPull := by
    funext u
    rw [fractLogPull, Complex.real_smul, ← Real.exp_neg, neg_neg]
    push_cast
    ring_nf
  rw [hfun] at h
  rw [← h]
  have hm := mellin_comp_inv (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) s
  rw [hm, mellin]
  rw [← integral_Ioi_zero_fract_cpow (w := s) (by rw [hre]; norm_num) (by rw [hre]; norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [smul_eq_mul]
  rw [show (-s - 1 : ℂ) = -(s + 1) by ring, mul_comm]

/-- `∫ |φ|² = ∫_0^∞ {x}²/x² dx`. -/
theorem integral_norm_sq_fractLogPull :
    ∫ u : ℝ, ‖fractLogPull u‖ ^ 2 = Real.log (2 * π) - eulerMascheroniConstant := by
  rw [← integral_fractSqDiv_Ioi]
  have h1 : ∫ u : ℝ, ‖fractLogPull u‖ ^ 2
      = ∫ u : ℝ, Real.exp u * Int.fract (Real.exp (-u)) ^ 2 := by
    rw [← integral_neg_eq_self (fun u : ℝ => ‖fractLogPull u‖ ^ 2) volume]
    congr 1
    funext u
    rw [norm_fractLogPull, mul_pow, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring_nf
  rw [h1, ← GaloisForLFunctions.HTGeometry.integral_Ioi_comp_neg_log_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  rw [neg_neg, Real.exp_log hx0, Real.exp_neg, Real.exp_log hx0, fractSqDiv]
  field_simp

theorem log_two_pi_sub_eulerMascheroni_pos : 0 < Real.log (2 * π) - eulerMascheroniConstant := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have he : Real.exp 1 < 2 * π := by
    have := Real.exp_one_lt_d9; have := Real.pi_gt_three; linarith
  have hlog : 1 < Real.log (2 * π) := by
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) he
  linarith

/-- **The weighted second moment of `ζ` on the critical line.**
`(1/2π) ∫ |ζ(½ + it)|² dt/(¼ + t²) = log 2π - γ`, with integrable integrand. -/
theorem integrable_and_integral_norm_sq_zeta_criticalLine :
    Integrable (fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)) ∧
      (2 * π)⁻¹ * ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)
        = Real.log (2 * π) - eulerMascheroniConstant := by
  have hπ : 0 < 2 * π := by positivity
  have hP := GaloisForLFunctions.HTGeometry.integral_norm_sq_fourier integrable_fractLogPull
    memLp_two_fractLogPull
  rw [integral_norm_sq_fractLogPull] at hP
  have hFint : Integrable (fun ξ : ℝ => ‖𝓕 fractLogPull ξ‖ ^ 2) := by
    by_contra hni
    rw [integral_undef hni] at hP
    exact (log_two_pi_sub_eulerMascheroni_pos).ne' hP.symm
  have hpt : ∀ t : ℝ, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)
      = ‖𝓕 fractLogPull (t / (2 * π))‖ ^ 2 := by
    intro t
    rw [fourier_fractLogPull, norm_neg, norm_div, div_pow, norm_half_add_mul_I,
      Real.sq_sqrt (by positivity)]
  simp_rw [hpt]
  refine ⟨hFint.comp_div hπ.ne', ?_⟩
  rw [Measure.integral_comp_div (fun ξ : ℝ => ‖𝓕 fractLogPull ξ‖ ^ 2) (2 * π), hP,
    abs_of_pos hπ, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hπ.ne', one_mul]

/-- **An unconditional bound on the zeros off the critical line.**  For every finite set `Z` of
zeros of `ζ` with `Re ρ > ½`, `Σ log (|ρ|/|1 - ρ|) ≤ ½ log (log 2π - γ)`. -/
theorem sum_log_norm_div_le_half_log_log_two_pi_sub_eulerMascheroni {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re) :
    ∑ ρ ∈ Z, Real.log (‖ρ‖ / ‖1 - ρ‖)
      ≤ 1 / 2 * Real.log (Real.log (2 * π) - eulerMascheroniConstant) := by
  obtain ⟨hint, hval⟩ := integrable_and_integral_norm_sq_zeta_criticalLine
  have h := sum_log_le_half_log_meanSquare_zeta_mul (M := fun _ => (1 : ℂ))
    (differentiable_const 1) ⟨1, fun s _ => by simp⟩ one_ne_zero (by simpa using hint) hZ
  simp only [mul_one, norm_one, Real.log_one, sub_zero] at h
  rwa [hval] at h


/-- `log (|ρ|/|1 - ρ|) ≥ (Re ρ - ½)/|ρ|²` for `Re ρ > ½`. -/
theorem re_sub_half_div_normSq_le_log_norm_div {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1' : ρ ≠ 1) :
    (ρ.re - 1 / 2) / ‖ρ‖ ^ 2 ≤ Real.log (‖ρ‖ / ‖1 - ρ‖) := by
  have hρ0 : ρ ≠ 0 := by rintro rfl; simp at hρ; linarith
  have hρ1 : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1')
  have hn0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hn1 : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hρ1
  have hdiff : ‖ρ‖ ^ 2 - ‖1 - ρ‖ ^ 2 = 2 * ρ.re - 1 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  have hlog : Real.log (‖ρ‖ / ‖1 - ρ‖) = Real.log (‖ρ‖ ^ 2 / ‖1 - ρ‖ ^ 2) / 2 := by
    rw [Real.log_div (pow_ne_zero 2 hn0.ne') (pow_ne_zero 2 hn1.ne'), Real.log_pow, Real.log_pow,
      Real.log_div hn0.ne' hn1.ne']
    push_cast
    ring
  have hkey := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < ‖ρ‖ ^ 2 / ‖1 - ρ‖ ^ 2)
  rw [inv_div] at hkey
  have h1 : 1 - ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 2 = (2 * ρ.re - 1) / ‖ρ‖ ^ 2 := by
    field_simp; linarith
  rw [h1] at hkey
  rw [hlog]
  have : (ρ.re - 1 / 2) / ‖ρ‖ ^ 2 = (2 * ρ.re - 1) / ‖ρ‖ ^ 2 / 2 := by ring
  rw [this]
  linarith

/-- **An unconditional off-line zero energy bound.**  For every finite set `Z` of zeros of `ζ` with
`Re ρ > ½`, `Σ (Re ρ - ½)/|ρ|² ≤ ½ log (log 2π - γ)`. -/
theorem sum_re_sub_half_div_normSq_le {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re) :
    ∑ ρ ∈ Z, (ρ.re - 1 / 2) / ‖ρ‖ ^ 2
      ≤ 1 / 2 * Real.log (Real.log (2 * π) - eulerMascheroniConstant) :=
  (Finset.sum_le_sum fun ρ hρ => re_sub_half_div_normSq_le_log_norm_div (hZ ρ hρ).2 (by
    rintro rfl; exact riemannZeta_ne_zero_of_one_le_re (by simp) (hZ 1 hρ).1)).trans
    (sum_log_norm_div_le_half_log_log_two_pi_sub_eulerMascheroni hZ)


/-- **Two-sided bound for the Balazard–Saias–Yor integral.**
`0 ≤ (1/2π) ∫ log |ζ(½ + it)| dt/(¼ + t²) ≤ ½ log (log 2π - γ)`; the integral vanishes under the
Riemann hypothesis and is positive otherwise. -/
theorem integral_log_norm_zeta_criticalLine_mem_Icc :
    0 ≤ (2 * π)⁻¹ * ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) ∧
      (2 * π)⁻¹ * ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)
        ≤ 1 / 2 * Real.log (Real.log (2 * π) - eulerMascheroniConstant) := by
  refine ⟨mul_nonneg (by positivity) integral_log_norm_zeta_criticalLine_nonneg, ?_⟩
  obtain ⟨hint2, hval⟩ := integrable_and_integral_norm_sq_zeta_criticalLine
  have hlog := (integrable_and_sum_log_le_integral_log_norm_zeta (Z := ∅) (by simp)).1
  have hF0 : ∀ᵐ t : ℝ, riemannZeta (1 / 2 + t * I) ≠ 0 := by
    have h := ae_riemannZeta_mul_ne_zero (M := fun _ => (1 : ℂ)) (differentiable_const 1)
      one_ne_zero
    simpa using h
  have h := integral_log_norm_le_half_log_integral_sq
    (F := fun t : ℝ => riemannZeta (1 / 2 + t * I)) hF0 hlog hint2
  rwa [hval] at h

end

end RHTower
