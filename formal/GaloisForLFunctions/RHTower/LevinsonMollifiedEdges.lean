import GaloisForLFunctions.RHTower.LevinsonWeightedHorizontalEdge
import GaloisForLFunctions.RHTower.EntireDirichletPolynomialHorizontalEdge

/-!
# The boundary edges of the mollified entire detector

The logarithmic derivative of `G♯·Ψ = (s−1)²(ζ + λζ′)·Ψ` splits into three pieces,

```text
logDeriv (G♯·Ψ) = 2/(s−1) + logDeriv G + logDeriv Ψ,
```

and each is estimated separately on a horizontal edge: the pole gauge by the trivial `2/T` bound,
the detector by the widened Backlund/Jensen count of `LevinsonWeightedHorizontalEdge`, and the
mollifier by the Dirichlet-polynomial count of `EntireDirichletPolynomialHorizontalEdge`.
-/

open Complex MeasureTheory Set intervalIntegral
open scoped Interval

noncomputable section

namespace RHTower

/-- The pole gauge contributes at most `2/T` pointwise on a horizontal edge at height `T`. -/
theorem abs_im_two_div_sub_one_le {x T : ℝ} (hT : 0 < T) :
    |(2 / ((x : ℂ) + (T : ℂ) * I - 1)).im| ≤ 2 / T := by
  set w : ℂ := (x : ℂ) + (T : ℂ) * I - 1 with hw
  have hwim : w.im = T := by rw [hw]; simp
  have hnorm : T ≤ ‖w‖ := by
    have h := Complex.abs_im_le_norm w
    rw [hwim, abs_of_pos hT] at h
    exact h
  have hwne : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    linarith
  have hle : |(2 / w).im| ≤ ‖(2 / w : ℂ)‖ := Complex.abs_im_le_norm _
  have hval : ‖(2 / w : ℂ)‖ = 2 / ‖w‖ := by
    rw [norm_div]
    norm_num
  rw [hval] at hle
  refine le_trans hle ?_
  exact div_le_div_of_nonneg_left (by norm_num) hT hnorm

/-- The weighted pole-gauge edge is `O(1/T)`. -/
theorem abs_integral_weighted_im_pole_le {c T : ℝ} (hc4 : c ≤ 4) (hT : 0 < T) :
    |∫ x in c..(4 : ℝ), (x - c) * (2 / ((x : ℂ) + (T : ℂ) * I - 1)).im|
      ≤ (4 - c) ^ 2 * (2 / T) := by
  have hcont : Continuous fun x : ℝ => (x - c) * (2 / ((x : ℂ) + (T : ℂ) * I - 1)).im := by
    have hden : ∀ x : ℝ, ((x : ℂ) + (T : ℂ) * I - 1) ≠ 0 := by
      intro x h0
      have him := congrArg Complex.im h0
      simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, Complex.one_im, Complex.zero_im,
        mul_one, mul_zero, add_zero, zero_add, sub_zero] at him
      linarith
    have h1 : Continuous fun x : ℝ => ((x : ℂ) + (T : ℂ) * I - 1) := by fun_prop
    exact (continuous_id.sub continuous_const).mul
      (Complex.continuous_im.comp ((continuous_const.div h1 hden)))
  have habs := intervalIntegral.abs_integral_le_integral_abs (f :=
    fun x : ℝ => (x - c) * (2 / ((x : ℂ) + (T : ℂ) * I - 1)).im)
    (μ := (volume : Measure ℝ)) hc4
  refine le_trans habs ?_
  have hmono : (∫ x in c..(4 : ℝ), |(x - c) * (2 / ((x : ℂ) + (T : ℂ) * I - 1)).im|)
      ≤ ∫ _x in c..(4 : ℝ), (4 - c) * (2 / T) := by
    refine intervalIntegral.integral_mono_on hc4 (hcont.abs.intervalIntegrable c 4)
      intervalIntegrable_const ?_
    intro x hx
    rw [abs_mul, abs_of_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x - c)]
    refine mul_le_mul (by linarith [hx.2]) (abs_im_two_div_sub_one_le hT)
      (abs_nonneg _) (by linarith [hx.1, hx.2])
  refine le_trans hmono ?_
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  have : (4 : ℝ) - c ≥ 0 := by linarith
  nlinarith [this]

/-- The logarithmic derivative of the mollified entire detector splits into pole gauge, detector and
mollifier. -/
theorem logDeriv_levinsonGEntire_mul (lam : ℂ) {Ψ : ℂ → ℂ} (hΨd : Differentiable ℂ Ψ)
    {s : ℂ} (hs : s ≠ 1) (hG : levinsonG lam s ≠ 0) (hΨ : Ψ s ≠ 0) :
    logDeriv (fun z => levinsonGEntire lam z * Ψ z) s
      = 2 / (s - 1) + logDeriv (levinsonG lam) s + logDeriv Ψ s := by
  have hGe : levinsonGEntire lam s ≠ 0 := by
    rw [Ne, levinsonGEntire_eq_zero_iff lam hs]
    exact hG
  rw [logDeriv_mul s hGe hΨ (differentiable_levinsonGEntire lam s) (hΨd s),
    logDeriv_levinsonGEntire lam hs hG]

end RHTower

end
