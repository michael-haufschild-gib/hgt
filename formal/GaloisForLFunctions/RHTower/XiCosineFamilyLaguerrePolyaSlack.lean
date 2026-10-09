import GaloisForLFunctions.RHTower.RiemannKernelSineSymbolLaguerrePolya
import GaloisForLFunctions.RHTower.XiCosineShiftLaguerrePolya
import GaloisForLFunctions.RHTower.XiSecondOrderLaguerrePolyaPreimage

/-!
# The cosine family of `Ξ` has first-order Laguerre–Pólya slack away from `h = 0`

Let `A_h = cos(hD)Ξ`, i.e. `A_h(z) = (Ξ(z + ih) + Ξ(z − ih))/2`, the transform of `Φ(u)cosh(hu)`
(`cosineShift_eq_paperFT`).

**Triple-angle identity.** `cosh 3x = cosh x·(2cosh 2x − 1)` and
`2cos 2w − 1 = (1 − 6w/π)·φ₃(w)`, `φ₃(w) = (2π/3) sin(w + π/6)·sin(w − π/6)/(w − π/6)`. On kernels,
with `w = isu`, this reads `cosh(su)·σ_s(u)·(1 − i(6s/π)u) = cosh(3su)`
(`coshMult_mul_sineSym_mul`). Hence `A_{3s} = (1 − (6s/π)D)ψ` with `ψ = φ₃(sD)A_s`.

**Slack** (`exists_laguerrePolya_firstOrder_preimage_cosineShift`). If `A_s` is Laguerre–Pólya,
then `ψ` is Laguerre–Pólya (`laguerrePolya_paperFT_mul_sineSym`), so `A_{3s}` has a first-order
Laguerre–Pólya preimage. Since `A_s` is Laguerre–Pólya for `s ≥ ½` (`laguerrePolya_cosineShiftXi`),
this holds unconditionally for every `h ≥ 3/2` with `a = π/(2h)`
(`exists_laguerrePolya_firstOrder_preimage_cosineShift_of_le`), and under RH for every `h > 0`
(`exists_laguerrePolya_firstOrder_preimage_cosineShift_of_rh`).

At `h = 0` there is no such preimage for any `a ≠ 0`
(`KernelStrip.not_exists_laguerrePolya_firstOrder_preimage_XiC`).
-/

open Complex MeasureTheory Filter Topology Set
open Zeta23

namespace RHTower.KernelStrip

noncomputable section

/-- The multiplier `cosh(hu)`. -/
def coshMult (h u : ℝ) : ℂ := Complex.cosh ((h : ℂ) * u)

theorem expGrowth_cexp_mul (a : ℝ) : ExpGrowth fun u : ℝ => cexp ((a : ℂ) * u) := by
  refine ⟨by fun_prop, 1, |a|, fun u => ?_⟩
  rw [Complex.norm_exp, one_mul]
  refine Real.exp_le_exp.mpr ?_
  have : ((a : ℂ) * (u : ℂ)).re = a * u := by simp
  rw [this, ← abs_mul]
  exact le_abs_self _

theorem coshMult_eq (h u : ℝ) :
    coshMult h u = (cexp ((h : ℂ) * u) + cexp (((-h : ℝ) : ℂ) * u)) / 2 := by
  rw [coshMult, Complex.cosh]
  push_cast
  ring_nf

theorem expGrowth_coshMult (h : ℝ) : ExpGrowth (coshMult h) := by
  obtain ⟨c1, A1, k1, h1⟩ := expGrowth_cexp_mul h
  obtain ⟨c2, A2, k2, h2⟩ := expGrowth_cexp_mul (-h)
  refine ⟨by unfold coshMult; fun_prop, 1, |h|, fun u => ?_⟩
  rw [coshMult_eq, norm_div, Complex.norm_two]
  have e1 : ‖cexp ((h : ℂ) * u)‖ ≤ Real.exp (|h| * |u|) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have : ((h : ℂ) * (u : ℂ)).re = h * u := by simp
    rw [this, ← abs_mul]; exact le_abs_self _
  have e2 : ‖cexp (((-h : ℝ) : ℂ) * u)‖ ≤ Real.exp (|h| * |u|) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have : (((-h : ℝ) : ℂ) * (u : ℂ)).re = -h * u := by simp
    rw [this, ← abs_neg h, ← abs_mul]; exact le_abs_self _
  have := norm_add_le (cexp ((h : ℂ) * u)) (cexp (((-h : ℝ) : ℂ) * u))
  rw [one_mul, div_le_iff₀ two_pos]
  linarith

/-- `paperFT Φ (z + ia) = ∫ Φ(u) e^{−au} e^{izu} du`. -/
theorem paperFT_kernel_shift (a : ℝ) (z : ℂ) :
    paperFT riemannPhiKernel (z + a * I) =
      paperFT (fun u => riemannPhiKernel u * cexp (((-a : ℝ) : ℂ) * u)) z := by
  unfold paperFT
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show riemannPhiKernel u * cexp (I * (z + a * I) * u) =
    riemannPhiKernel u * cexp (((-a : ℝ) : ℂ) * u) * cexp (I * z * u)
  rw [mul_assoc (riemannPhiKernel u), ← Complex.exp_add]
  congr 2
  push_cast
  linear_combination ((a : ℂ) * u) * I_sq

/-- **Bridge.** `(Ξ(z + ih) + Ξ(z − ih))/2 = ∫ Φ(u)cosh(hu)e^{izu}du`. -/
theorem cosineShift_eq_paperFT (h : ℝ) (z : ℂ) :
    (XiC (z + h * I) + XiC (z - h * I)) / 2 =
      paperFT (fun u => riemannPhiKernel u * coshMult h u) z := by
  rw [← Littlewood.paperFT_riemannPhiKernel_eq_XiC, ← Littlewood.paperFT_riemannPhiKernel_eq_XiC,
    show z - (h : ℂ) * I = z + ((-h : ℝ) : ℂ) * I by push_cast; ring,
    paperFT_kernel_shift, paperFT_kernel_shift, neg_neg]
  obtain ⟨C₁, -, hC₁⟩ := integrable_kernel_mul_cexp (expGrowth_cexp_mul (-h)) |z.im|
  obtain ⟨C₂, -, hC₂⟩ := integrable_kernel_mul_cexp (expGrowth_cexp_mul h) |z.im|
  have i1 : Integrable fun u : ℝ =>
      riemannPhiKernel u * cexp (((-h : ℝ) : ℂ) * u) * cexp (I * z * u) :=
    ((RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul C₁).mono'
      ((continuous_riemannPhiKernel.mul (expGrowth_cexp_mul (-h)).1).mul
        (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => (hC₁ z le_rfl u).1)
  have i2 : Integrable fun u : ℝ =>
      riemannPhiKernel u * cexp ((h : ℂ) * u) * cexp (I * z * u) :=
    ((RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul C₂).mono'
      ((continuous_riemannPhiKernel.mul (expGrowth_cexp_mul h).1).mul
        (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => (hC₂ z le_rfl u).1)
  unfold paperFT
  rw [← integral_add i1 i2, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [coshMult_eq]
  push_cast
  ring

/-- **The triple-angle kernel identity.** `cosh(su)·σ_s(u)·(1 − i(6s/π)u) = cosh(3su)`. -/
theorem coshMult_mul_sineSym_mul (s u : ℝ) :
    coshMult s u * sineSym s u * (1 - I * ((6 * s / Real.pi : ℝ) : ℂ) * u) =
      coshMult (3 * s) u := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set w : ℂ := I * s * u with hw
  have hy := sineArgMinus_ne_zero s u
  have hx : sineArgPlus s u = w + ((Real.pi / 6 : ℝ) : ℂ) := by rw [sineArgPlus, hw]; ring
  have hy' : sineArgMinus s u = w - ((Real.pi / 6 : ℝ) : ℂ) := by
    rw [sineArgMinus, hw]; push_cast; ring
  -- `σ_s · (1 − 6w/π) = −4 sin(w + π/6) sin(w − π/6)`
  have hlin : (1 - I * ((6 * s / Real.pi : ℝ) : ℂ) * u) =
      -(6 / (Real.pi : ℂ)) * sineArgMinus s u := by
    rw [hy', hw]; push_cast; field_simp; ring
  have h1 : sineSym s u * (1 - I * ((6 * s / Real.pi : ℝ) : ℂ) * u) =
      -4 * (Complex.sin (sineArgPlus s u) * Complex.sin (sineArgMinus s u)) := by
    rw [hlin, sineSym]
    push_cast
    field_simp
    ring
  -- `−4 sin(w + b) sin(w − b) = 2cos 2w − 1` with `b = π/6`
  have hs : Complex.sin ((Real.pi / 6 : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_sin, Real.sin_pi_div_six]; push_cast; ring
  have hc : Complex.cos ((Real.pi / 6 : ℝ) : ℂ) ^ 2 = 3 / 4 := by
    rw [← Complex.ofReal_cos, Real.cos_pi_div_six, ← Complex.ofReal_pow, div_pow,
      Real.sq_sqrt (by norm_num)]
    push_cast; ring
  have h2 : -4 * (Complex.sin (sineArgPlus s u) * Complex.sin (sineArgMinus s u)) =
      2 * Complex.cos (2 * w) - 1 := by
    rw [hx, hy', Complex.sin_add, Complex.sin_sub, Complex.cos_two_mul]
    have hsc := Complex.sin_sq_add_cos_sq w
    have e : (Complex.sin w * Complex.cos ((Real.pi / 6 : ℝ) : ℂ) +
        Complex.cos w * Complex.sin ((Real.pi / 6 : ℝ) : ℂ)) *
        (Complex.sin w * Complex.cos ((Real.pi / 6 : ℝ) : ℂ) -
        Complex.cos w * Complex.sin ((Real.pi / 6 : ℝ) : ℂ)) =
        Complex.sin w ^ 2 * Complex.cos ((Real.pi / 6 : ℝ) : ℂ) ^ 2 -
        Complex.cos w ^ 2 * Complex.sin ((Real.pi / 6 : ℝ) : ℂ) ^ 2 := by ring
    rw [e, hc, hs]
    linear_combination (-3 : ℂ) * hsc
  -- `cos(2isu) = cosh(2su)` and `cosh x (2cosh 2x − 1) = cosh 3x`
  have h3 : Complex.cos (2 * w) = Complex.cosh (2 * ((s : ℂ) * u)) := by
    rw [hw, show 2 * (I * (s : ℂ) * u) = (2 * ((s : ℂ) * u)) * I by ring, Complex.cos_mul_I]
  rw [mul_assoc, h1, h2, h3, coshMult, coshMult]
  push_cast
  rw [show (3 : ℂ) * s * u = 3 * ((s : ℂ) * u) by ring, Complex.cosh_three_mul,
    Complex.cosh_two_mul]
  have hcs := Complex.cosh_sq_sub_sinh_sq ((s : ℂ) * u)
  linear_combination (-2 * Complex.cosh ((s : ℂ) * u)) * hcs

theorem expGrowth_coshMult_mul_sineSym (s : ℝ) :
    ExpGrowth fun u => coshMult s u * sineSym s u :=
  (expGrowth_coshMult s).mul (expGrowth_sineSym s)

/-- **First-order slack from one cosine step.** If `A_s` is Laguerre–Pólya, then `A_{3s}` has a
Laguerre–Pólya preimage under `1 − (6s/π)D`. -/
theorem exists_laguerrePolya_firstOrder_preimage_cosineShift {s : ℝ}
    (hA : GaloisForLFunctions.HTGeometry.LaguerrePolya
      (fun z => (XiC (z + s * I) + XiC (z - s * I)) / 2)) :
    ∃ ψ : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya ψ ∧
      ∀ z, ψ z - ((6 * s / Real.pi : ℝ) : ℂ) * deriv ψ z =
        (XiC (z + ((3 * s : ℝ) : ℂ) * I) + XiC (z - ((3 * s : ℝ) : ℂ) * I)) / 2 := by
  have hA' : GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * coshMult s u) z := by
    have e : (fun z : ℂ => paperFT (fun u => riemannPhiKernel u * coshMult s u) z) =
        fun z => (XiC (z + s * I) + XiC (z - s * I)) / 2 :=
      funext fun z => (cosineShift_eq_paperFT s z).symm
    rw [e]; exact hA
  refine ⟨fun z => paperFT (fun u => riemannPhiKernel u * (coshMult s u * sineSym s u)) z,
    laguerrePolya_paperFT_mul_sineSym (expGrowth_coshMult s) s hA', fun z => ?_⟩
  rw [paperFT_kernel_sub_smul_deriv (expGrowth_coshMult_mul_sineSym s), cosineShift_eq_paperFT]
  congr 1
  funext u
  rw [coshMult_mul_sineSym_mul]

/-- **Unconditional slack for `h ≥ 3/2`.** `A_h = (1 − (2h/π)D)ψ` with `ψ` Laguerre–Pólya. -/
theorem exists_laguerrePolya_firstOrder_preimage_cosineShift_of_le {h : ℝ} (hh : 3 / 2 ≤ h) :
    ∃ ψ : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya ψ ∧
      ∀ z, ψ z - ((2 * h / Real.pi : ℝ) : ℂ) * deriv ψ z =
        (XiC (z + h * I) + XiC (z - h * I)) / 2 := by
  obtain ⟨ψ, hψ, hid⟩ := exists_laguerrePolya_firstOrder_preimage_cosineShift
    (laguerrePolya_cosineShiftXi (h := h / 3) (by linarith))
  refine ⟨ψ, hψ, fun z => ?_⟩
  have h1 := hid z
  rw [show 6 * (h / 3) / Real.pi = 2 * h / Real.pi by ring,
    show 3 * (h / 3) = h by ring] at h1
  exact h1

/-- **Slack for every `h > 0` under RH.** -/
theorem exists_laguerrePolya_firstOrder_preimage_cosineShift_of_rh (hRH : RiemannHypothesis)
    {h : ℝ} (hh : 0 < h) :
    ∃ ψ : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya ψ ∧
      ∀ z, ψ z - ((2 * h / Real.pi : ℝ) : ℂ) * deriv ψ z =
        (XiC (z + h * I) + XiC (z - h * I)) / 2 := by
  obtain ⟨ψ, hψ, hid⟩ := exists_laguerrePolya_firstOrder_preimage_cosineShift
    (laguerrePolya_cosineShiftXi_of_rh hRH (h := h / 3) (by linarith))
  refine ⟨ψ, hψ, fun z => ?_⟩
  have h1 := hid z
  rw [show 6 * (h / 3) / Real.pi = 2 * h / Real.pi by ring,
    show 3 * (h / 3) = h by ring] at h1
  exact h1

end

end RHTower.KernelStrip
