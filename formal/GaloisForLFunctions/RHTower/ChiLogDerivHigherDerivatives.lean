import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDerivative
import GaloisForLFunctions.HTGeometry.PolygammaVerticalDecay
import GaloisForLFunctions.HTGeometry.AffineFluxTaylorCoeff
import GaloisForLFunctions.HTGeometry.DigammaGammaFactorialBlowUp

/-!
# Higher derivatives of the logarithmic derivative of `χ`

Off the real axis the closed form `χ'/χ(z) = −ψ(z/2)/2 − ψ((1−z)/2)/2 + log π` holds on a whole
neighbourhood, so every derivative of `χ'/χ` is a combination of two half-argument polygammas:

  `(χ'/χ)^{(n)}(z) = −2^{-(n+1)} ψ^{(n)}(z/2) − ½ (−½)^n ψ^{(n)}((1−z)/2)`.

With the explicit polygamma decay this gives, for `−2 < Re z < 3` and `|Im z| ≥ 2`,

  `‖(χ'/χ)^{(n)}(z)‖ ≤ 5 n! / |Im z|^n`   (`n ≥ 1`),

the all-order height-derivative input for the archimedean weights of the product AFE.
-/

noncomputable section

namespace RHTower

open Complex GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The closed form of `χ'/χ`. -/
def chiLogDerivClosed (z : ℂ) : ℂ :=
  -(Complex.digamma (z / 2) / 2) - Complex.digamma ((1 - z) / 2) / 2 + (Real.log Real.pi : ℂ)

theorem half_ne_neg_nat_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) (m : ℕ) : z / 2 ≠ -(m : ℂ) := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hz this

theorem reflect_half_ne_neg_nat_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) (m : ℕ) :
    (1 - z) / 2 ≠ -(m : ℂ) := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hz this

theorem isOpen_im_ne_zero : IsOpen {w : ℂ | w.im ≠ 0} :=
  isOpen_ne.preimage Complex.continuous_im

theorem logDeriv_zetaChi_eventuallyEq {z : ℂ} (hz : z.im ≠ 0) :
    logDeriv zetaChi =ᶠ[nhds z] chiLogDerivClosed := by
  filter_upwards [isOpen_im_ne_zero.mem_nhds hz] with w hw
  exact logDeriv_zetaChi_off_poles (half_ne_neg_nat_of_im_ne_zero hw)
    (reflect_half_ne_neg_nat_of_im_ne_zero hw)

/-- Half-argument digamma. -/
def halfDigamma (u : ℂ) : ℂ := Complex.digamma (u / 2)

/-- Shifted half-argument digamma `y ↦ ψ((1+y)/2)`. -/
def shiftHalfDigamma (y : ℂ) : ℂ := halfDigamma (1 + y)

/-- Half-argument jets: `(d/dz)^n ψ(z/2) = 2^{-n} ψ^{(n)}(z/2)`, with no smoothness hypothesis. -/
theorem iteratedDeriv_halfDigamma (n : ℕ) (z : ℂ) :
    iteratedDeriv n halfDigamma z = (1 / 2 : ℂ) ^ n * iteratedDeriv n Complex.digamma (z / 2) := by
  have h := iteratedDeriv_comp_const_mul_of_ne Complex.digamma n (μ := (1 / 2 : ℂ)) (by norm_num) z
  have hfun : halfDigamma = fun w => Complex.digamma ((1 / 2 : ℂ) * w) := by
    funext w
    unfold halfDigamma
    congr 1
    ring
  rw [hfun, h, show (1 / 2 : ℂ) * z = z / 2 by ring]

/-- Reflected half-argument jets: `(d/dz)^n ψ((1−z)/2) = (−½)^n ψ^{(n)}((1−z)/2)`. -/
theorem iteratedDeriv_digamma_reflectHalf (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w => Complex.digamma ((1 - w) / 2)) z =
      (-1 / 2 : ℂ) ^ n * iteratedDeriv n Complex.digamma ((1 - z) / 2) := by
  have hfun : (fun w : ℂ => Complex.digamma ((1 - w) / 2)) = fun w => shiftHalfDigamma (-w) := by
    funext w
    unfold shiftHalfDigamma halfDigamma
    congr 1
  have hshift : iteratedDeriv n shiftHalfDigamma (-z) = iteratedDeriv n halfDigamma (1 + -z) :=
    congrFun (iteratedDeriv_comp_const_add n halfDigamma 1) (-z)
  simp only [hfun, iteratedDeriv_comp_neg, hshift, iteratedDeriv_halfDigamma, smul_eq_mul,
    show (1 : ℂ) + -z = 1 - z by ring, ← mul_assoc, ← mul_pow]
  norm_num

theorem analyticAt_halfDigamma {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ (fun w => Complex.digamma (w / 2)) z := by
  have h := analyticAt_digamma_of_offPoles (half_ne_neg_nat_of_im_ne_zero hz)
  have hf : AnalyticAt ℂ (fun w : ℂ => w / 2) z :=
    analyticAt_id.div analyticAt_const (by norm_num)
  exact AnalyticAt.comp (g := Complex.digamma) (f := fun w : ℂ => w / 2) h hf

theorem analyticAt_digamma_reflectHalf {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ (fun w => Complex.digamma ((1 - w) / 2)) z := by
  have h := analyticAt_digamma_of_offPoles (reflect_half_ne_neg_nat_of_im_ne_zero hz)
  have hf : AnalyticAt ℂ (fun w : ℂ => (1 - w) / 2) z :=
    (analyticAt_const.sub analyticAt_id).div analyticAt_const (by norm_num)
  exact AnalyticAt.comp (g := Complex.digamma) (f := fun w : ℂ => (1 - w) / 2) h hf

/-- **Higher derivatives of `χ'/χ` off the real axis.** -/
theorem iteratedDeriv_logDeriv_zetaChi_eq {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z.im ≠ 0) :
    iteratedDeriv n (logDeriv zetaChi) z =
      -((1 / 2 : ℂ) ^ (n + 1) * iteratedDeriv n Complex.digamma (z / 2))
        - (1 / 2 : ℂ) * (-1 / 2 : ℂ) ^ n * iteratedDeriv n Complex.digamma ((1 - z) / 2) := by
  rw [(logDeriv_zetaChi_eventuallyEq hz).iteratedDeriv_eq]
  have h1 : ContDiffAt ℂ n (fun w => Complex.digamma (w / 2)) z :=
    (analyticAt_halfDigamma hz).contDiffAt
  have h2 : ContDiffAt ℂ n (fun w => Complex.digamma ((1 - w) / 2)) z :=
    (analyticAt_digamma_reflectHalf hz).contDiffAt
  have hf1 : ContDiffAt ℂ n (fun w => (-(1 / 2 : ℂ)) * Complex.digamma (w / 2)) z :=
    contDiffAt_const.mul h1
  have hf2 : ContDiffAt ℂ n (fun w => (-(1 / 2 : ℂ)) * Complex.digamma ((1 - w) / 2)) z :=
    contDiffAt_const.mul h2
  have hsum : ContDiffAt ℂ n ((fun w => (-(1 / 2 : ℂ)) * Complex.digamma (w / 2)) +
      fun w => (-(1 / 2 : ℂ)) * Complex.digamma ((1 - w) / 2)) z := hf1.add hf2
  have hfun : chiLogDerivClosed =
      ((fun w => (-(1 / 2 : ℂ)) * Complex.digamma (w / 2)) +
        fun w => (-(1 / 2 : ℂ)) * Complex.digamma ((1 - w) / 2)) +
        fun _ => (Real.log Real.pi : ℂ) := by
    funext w
    simp only [chiLogDerivClosed, Pi.add_apply]
    ring
  have e1 : iteratedDeriv n (fun w => (-(1 / 2 : ℂ)) * Complex.digamma (w / 2)) z
      = (-(1 / 2 : ℂ)) * iteratedDeriv n (fun w => Complex.digamma (w / 2)) z :=
    iteratedDeriv_const_mul (-(1 / 2 : ℂ)) h1
  have e2 : iteratedDeriv n (fun w => (-(1 / 2 : ℂ)) * Complex.digamma ((1 - w) / 2)) z
      = (-(1 / 2 : ℂ)) * iteratedDeriv n (fun w => Complex.digamma ((1 - w) / 2)) z :=
    iteratedDeriv_const_mul (-(1 / 2 : ℂ)) h2
  rw [hfun, iteratedDeriv_add hsum contDiffAt_const, iteratedDeriv_const, if_neg (by omega),
    add_zero, iteratedDeriv_add hf1 hf2, e1, e2]
  have hhalf : iteratedDeriv n (fun w => Complex.digamma (w / 2)) z
      = (1 / 2 : ℂ) ^ n * iteratedDeriv n Complex.digamma (z / 2) := by
    have := iteratedDeriv_halfDigamma n z
    unfold halfDigamma at this
    exact this
  rw [hhalf, iteratedDeriv_digamma_reflectHalf]
  ring

/-- **All-order bound for `χ'/χ`**: `‖(χ'/χ)^{(n)}(z)‖ ≤ 5 n!/|Im z|^n` for `n ≥ 1`,
`−2 < Re z < 3`, `|Im z| ≥ 2`. -/
theorem norm_iteratedDeriv_logDeriv_zetaChi_le {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hre₁ : -2 < z.re) (hre₂ : z.re < 3) (him : 2 ≤ |z.im|) :
    ‖iteratedDeriv n (logDeriv zetaChi) z‖ ≤ 5 * n.factorial / |z.im| ^ n := by
  cases n with
  | zero => omega
  | succ m =>
  have hz : z.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at him
    linarith
  have hT : (0 : ℝ) < |z.im| := by linarith
  rw [iteratedDeriv_logDeriv_zetaChi_eq hn hz]
  have hAre : (z / 2).re = z.re / 2 := by simp
  have hAim : (z / 2).im = z.im / 2 := by simp
  have hBre : ((1 - z) / 2).re = (1 - z.re) / 2 := by simp
  have hBim : ((1 - z) / 2).im = -z.im / 2 := by simp
  have hA : -1 < (z / 2).re := by rw [hAre]; linarith
  have hA' : 1 ≤ |(z / 2).im| := by
    rw [hAim, abs_div, abs_two]; linarith
  have hB : -1 < ((1 - z) / 2).re := by rw [hBre]; linarith
  have hB' : 1 ≤ |((1 - z) / 2).im| := by
    rw [hBim, abs_div, abs_neg, abs_two]; linarith
  have h1 := norm_iteratedDeriv_digamma_le (m := m) hA hA'
  have h2 := norm_iteratedDeriv_digamma_le (m := m) hB hB'
  rw [hAim, abs_div, abs_two] at h1
  rw [hBim, abs_div, abs_neg, abs_two] at h2
  have hpow : (|z.im| / 2) ^ (m + 1) = |z.im| ^ (m + 1) / 2 ^ (m + 1) := by
    rw [div_pow]
  rw [hpow] at h1 h2
  have hcoef1 : ‖-((1 / 2 : ℂ) ^ (m + 1 + 1) * iteratedDeriv (m + 1) Complex.digamma (z / 2))‖
      = (1 / 2 : ℝ) ^ (m + 2) * ‖iteratedDeriv (m + 1) Complex.digamma (z / 2)‖ := by
    rw [norm_neg, norm_mul, norm_pow]
    congr 2
    norm_num
  have hcoef2 : ‖(1 / 2 : ℂ) * (-1 / 2 : ℂ) ^ (m + 1) * iteratedDeriv (m + 1) Complex.digamma ((1 - z) / 2)‖
      = (1 / 2 : ℝ) ^ (m + 2) * ‖iteratedDeriv (m + 1) Complex.digamma ((1 - z) / 2)‖ := by
    rw [norm_mul, norm_mul, norm_pow]
    have : ‖(-1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    ring
  refine (norm_sub_le _ _).trans ?_
  rw [hcoef1, hcoef2]
  have hfac : (0 : ℝ) ≤ (m + 1).factorial := by positivity
  have h2m : (1 / 2 : ℝ) ^ (m + 1) * 2 ^ (m + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have hkey : (1 / 2 : ℝ) ^ (m + 2) * (5 * (m + 1).factorial / (|z.im| ^ (m + 1) / 2 ^ (m + 1)))
      = ((1 / 2 : ℝ) ^ (m + 1) * 2 ^ (m + 1)) * ((5 * (m + 1).factorial / |z.im| ^ (m + 1)) / 2) := by
    field_simp
    ring
  rw [h2m, one_mul] at hkey
  calc (1 / 2 : ℝ) ^ (m + 2) * ‖iteratedDeriv (m + 1) Complex.digamma (z / 2)‖
        + (1 / 2 : ℝ) ^ (m + 2) * ‖iteratedDeriv (m + 1) Complex.digamma ((1 - z) / 2)‖
      ≤ (1 / 2 : ℝ) ^ (m + 2) * (5 * (m + 1).factorial / (|z.im| ^ (m + 1) / 2 ^ (m + 1)))
        + (1 / 2 : ℝ) ^ (m + 2) * (5 * (m + 1).factorial / (|z.im| ^ (m + 1) / 2 ^ (m + 1))) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = 5 * (m + 1).factorial / |z.im| ^ (m + 1) := by rw [hkey]; ring

end RHTower

end
