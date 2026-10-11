import GaloisForLFunctions.RHTower.JointAncestryLogWeightExpansion
import GaloisForLFunctions.RHTower.JointAncestryDressingTwoExistence

/-!
# Phase bookkeeping for the log-weight amplification

Write a test value as `V(s) = w_s exp(τE(s) + R)`, `w_s = 1/(s(1−s))`.  At the target `ξ` the twist
`φ` is chosen so that `arg w_ξ + τ Im E(ξ) = π` up to the remainder, so `w_ξ e^{iy₀} = −|w_ξ|`
(`mul_cexp_eq_neg_norm`).  Every other point is measured against this normalisation:

`Re(w_s e^z) = −|w_ξ| Re((w_s/w_ξ) e^{z − i y₀})`.

* If `|arg(w_s/w_ξ)| + |Im z − y₀ − 2πk| ≤ π/2` for some integer `k`, then `Re(w_s e^z) ≤ 0`
  (`re_mul_cexp_nonpos_of_aligned`): an aligned point never cancels the target.
* At the target itself `Re(w_ξ e^z) ≤ −|w_ξ| e^{Re z}/2` once `|Im z − y₀| ≤ 1`
  (`re_mul_cexp_le_neg_half`).
* `|arg(w_s/w_ξ)| ≤ 2|w_s/w_ξ − 1|` whenever the quotient is within `1/2` of `1`
  (`abs_arg_le_two_mul_norm_sub_one`).
-/

open Complex
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-- `Re(c e^z) = |c| e^{Re z} cos(arg c + Im z)`. -/
theorem re_mul_cexp_eq (c z : ℂ) :
    (c * cexp z).re = ‖c‖ * Real.exp z.re * Real.cos (c.arg + z.im) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I c]
  rw [mul_assoc, ← Complex.exp_add, Complex.re_ofReal_mul, Complex.exp_re]
  have hre : ((c.arg : ℂ) * I + z).re = z.re := by simp
  have him : ((c.arg : ℂ) * I + z).im = c.arg + z.im := by simp
  rw [hre, him]
  ring

/-- **Aligned points do not cancel.** -/
theorem re_mul_cexp_nonneg_of_aligned {c z : ℂ} {k : ℤ}
    (h : |c.arg + z.im - 2 * Real.pi * k| ≤ Real.pi / 2) : 0 ≤ (c * cexp z).re := by
  rw [re_mul_cexp_eq]
  have hcos : Real.cos (c.arg + z.im) = Real.cos (c.arg + z.im - k * (2 * Real.pi)) :=
    (Real.cos_sub_int_mul_two_pi _ k).symm
  have hmem : c.arg + z.im - k * (2 * Real.pi) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [abs_le] at h
    constructor <;> linarith
  rw [hcos]
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) (Real.cos_nonneg_of_mem_Icc hmem)

/-- The target normalisation: `arg w + y₀ = π` gives `w e^{i y₀} = −|w|`. -/
theorem mul_cexp_eq_neg_norm {w : ℂ} {y₀ : ℝ} (h : w.arg + y₀ = Real.pi) :
    w * cexp ((y₀ : ℂ) * I) = -((‖w‖ : ℝ) : ℂ) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
  rw [mul_assoc, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, h, Complex.exp_pi_mul_I]
  ring

/-- `Re(w_s e^z) = −|w_ξ| Re((w_s/w_ξ) e^{z − i y₀})` under the target normalisation. -/
theorem re_mul_cexp_eq_neg_norm_mul {wξ ws z : ℂ} {y₀ : ℝ} (hwξ : wξ ≠ 0)
    (h : wξ.arg + y₀ = Real.pi) :
    (ws * cexp z).re = -‖wξ‖ * ((ws / wξ) * cexp (z - (y₀ : ℂ) * I)).re := by
  have hid : ws * cexp z = (wξ * cexp ((y₀ : ℂ) * I)) * ((ws / wξ) * cexp (z - (y₀ : ℂ) * I)) := by
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    field_simp
    ring_nf
  rw [hid, mul_cexp_eq_neg_norm h, neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
  ring

/-- **Aligned points contribute non-positively.** -/
theorem re_mul_cexp_nonpos_of_aligned {wξ ws z : ℂ} {y₀ : ℝ} (hwξ : wξ ≠ 0)
    (h : wξ.arg + y₀ = Real.pi) {k : ℤ}
    (halign : |(ws / wξ).arg + (z.im - y₀) - 2 * Real.pi * k| ≤ Real.pi / 2) :
    (ws * cexp z).re ≤ 0 := by
  rw [re_mul_cexp_eq_neg_norm_mul hwξ h]
  have him : (z - (y₀ : ℂ) * I).im = z.im - y₀ := by simp
  have := re_mul_cexp_nonneg_of_aligned (c := ws / wξ) (z := z - (y₀ : ℂ) * I) (k := k)
    (by rw [him]; exact halign)
  nlinarith [norm_nonneg wξ]

/-- **The target is strictly negative.** -/
theorem re_mul_cexp_le_neg_half {wξ z : ℂ} {y₀ : ℝ} (hwξ : wξ ≠ 0)
    (h : wξ.arg + y₀ = Real.pi) (hz : |z.im - y₀| ≤ 1) :
    (wξ * cexp z).re ≤ -(‖wξ‖ * Real.exp z.re) / 2 := by
  rw [re_mul_cexp_eq_neg_norm_mul hwξ h, div_self hwξ, one_mul, Complex.exp_re]
  have hre : (z - (y₀ : ℂ) * I).re = z.re := by simp
  have him : (z - (y₀ : ℂ) * I).im = z.im - y₀ := by simp
  rw [hre, him]
  have hcos : 1 / 2 ≤ Real.cos (z.im - y₀) := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := z.im - y₀)
    have h2 : (z.im - y₀) ^ 2 ≤ 1 := by
      have := abs_le.mp hz
      nlinarith
    linarith
  have hE := Real.exp_pos z.re
  have := mul_nonneg (mul_nonneg (norm_nonneg wξ) hE.le) (sub_nonneg.mpr hcos)
  nlinarith [norm_nonneg wξ]

/-- `|arg c| ≤ 2|c − 1|` whenever `|c − 1| ≤ 1/2`. -/
theorem abs_arg_le_two_mul_norm_sub_one {c : ℂ} (hc : ‖c - 1‖ ≤ 1 / 2) :
    |c.arg| ≤ 2 * ‖c - 1‖ := by
  have hre : 1 / 2 ≤ c.re := by
    have := Complex.abs_re_le_norm (c - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    have := abs_le.mp (this.trans hc)
    linarith [this.1]
  have him : |c.im| ≤ ‖c - 1‖ := by
    have := Complex.abs_im_le_norm (c - 1)
    rwa [Complex.sub_im, Complex.one_im, sub_zero] at this
  refine (abs_arg_le_abs_im_div_re (by linarith)).trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (c - 1)]

/-- The ratio of the weights `w_s/w_ξ = ξ(1−ξ)/(s(1−s))` is within `|ξ − s||1 − ξ − s|/|s(1−s)|`
of `1`. -/
theorem norm_div_weights_sub_one (ξ s : ℂ) (hs : s * (1 - s) ≠ 0) :
    ‖(1 / (s * (1 - s))) / (1 / (ξ * (1 - ξ))) - 1‖ =
      ‖ξ - s‖ * ‖1 - ξ - s‖ / ‖s * (1 - s)‖ := by
  have h0 : (1 / (s * (1 - s))) / (1 / (ξ * (1 - ξ))) = ξ * (1 - ξ) / (s * (1 - s)) := by
    rw [div_div_eq_mul_div, div_one, one_div_mul_eq_div]
  have h : (1 / (s * (1 - s))) / (1 / (ξ * (1 - ξ))) - 1 = (ξ - s) * (1 - ξ - s) / (s * (1 - s)) := by
    rw [h0, div_sub_one hs]
    congr 1
    ring
  rw [h, norm_div, norm_mul]

end

end RHTower
