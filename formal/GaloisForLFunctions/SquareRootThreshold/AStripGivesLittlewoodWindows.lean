import GaloisForLFunctions.RHTower.LittlewoodShortWindowZeroCount
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection

/-!
# The Littlewood windows off the critical line

The Littlewood window count (`LittlewoodShortWindowZeroCount`) uses the Riemann hypothesis only to
make the explicit-formula summand of a zero `ρ` equal to `m ψ_k(Im ρ − T)`.  For a zero
`ρ = ½ + η + iγ` the summand is `m F_k(x − iη) conj F_k(x + iη)`, `x = γ − T`, `F_k = (Φ_ℓ^{(k)})^`.

**Perturbation** (`norm_wsummand_window_sub_le`).  For `|η| ≤ 1`,

  `|summand − m ψ_k(x)| ≤ m |η| e^{2ℓ|η|} K_k(ℓ)/(1 + |x|)⁴`,

from the decay `|F_k(x + iy)| ≤ e^{ℓ|y|} K/(1 + |x|)²` (`norm_paperFT_le_decay`) and the shift bound
`|F_k(x + iy) − F_k(x)| ≤ |y| e^{ℓ|y|} K/(1 + |x|)²` (`norm_paperFT_cb_shift_sub_le`).  The shift bound
is `|e^{−yu} − 1| ≤ |y| ℓ e^{ℓ|y|}` under the integral near `x = 0`, and `F_k = −F_{k+2}/z²` away from
it.
-/

open Complex MeasureTheory Set Filter Topology
open Zeta23

namespace RHTower.Littlewood

noncomputable section

/-- `|e^w − 1| ≤ |w| e^{|w|}`. -/
theorem abs_exp_sub_one_le_mul_exp (w : ℝ) : |Real.exp w - 1| ≤ |w| * Real.exp |w| := by
  rcases le_or_gt 0 w with hw | hw
  · rw [abs_of_nonneg hw, abs_of_nonneg (by linarith [Real.add_one_le_exp w])]
    -- `e^w (1 − w) ≤ 1`
    have h := Real.add_one_le_exp (-w)
    have he := Real.exp_pos w
    have : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  · rw [abs_of_neg hw, abs_of_nonpos (by linarith [Real.exp_lt_one.mpr hw])]
    have h := Real.add_one_le_exp w
    have h1 : 1 ≤ Real.exp (-w) := Real.one_le_exp (by linarith)
    nlinarith

/-- **Vertical shift of a compactly supported transform.**  If `f` is integrable and supported in
`[−a, a]`, then `‖f̂(x + iy) − f̂(x)‖ ≤ |y| a e^{a|y|} ∫‖f‖`. -/
theorem norm_paperFT_shift_sub_le {f : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (hf : Integrable f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) (x y : ℝ) :
    ‖paperFT f ((x : ℂ) + (y : ℂ) * I) - paperFT f x‖ ≤ |y| * a * Real.exp (a * |y|) * ∫ u, ‖f u‖ := by
  set K := |y| * a * Real.exp (a * |y|) with hK
  have hK0 : 0 ≤ K := by positivity
  -- integrability of `f(u) e^{izu}` for `|Im z| ≤ |y|`
  have hint : ∀ z : ℂ, |z.im| ≤ |y| →
      Integrable (fun u : ℝ => f u * Complex.exp (I * z * (u : ℂ))) := by
    intro z hz
    refine (hf.norm.mul_const (Real.exp (a * |y|))).mono'
      (hf.aestronglyMeasurable.mul (by fun_prop : Continuous fun u : ℝ =>
        Complex.exp (I * z * (u : ℂ))).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
    rw [norm_mul, Complex.norm_exp]
    by_cases hu : f u = 0
    · simp [hu]
    have hua := hsupp u hu
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have : (I * z * (u : ℂ)).re = -(z.im * u) := by simp
    rw [this]
    have h1 : -(z.im * u) ≤ |z.im| * |u| := by
      rw [← abs_mul]; exact neg_le_abs _
    nlinarith [abs_nonneg z.im, abs_nonneg u]
  have h1 := hint ((x : ℂ) + (y : ℂ) * I) (by simp)
  have h0 := hint (x : ℂ) (by simp)
  have hdiff : paperFT f ((x : ℂ) + (y : ℂ) * I) - paperFT f x =
      ∫ u, (f u * Complex.exp (I * ((x : ℂ) + (y : ℂ) * I) * (u : ℂ)) -
        f u * Complex.exp (I * (x : ℂ) * (u : ℂ))) := by
    simp only [paperFT]
    rw [integral_sub h1 h0]
  rw [hdiff]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    (hf.norm.const_mul K) (Eventually.of_forall fun u => ?_)
  simp only
  by_cases hu : f u = 0
  · simp [hu]
  have hua := hsupp u hu
  -- `e^{i(x+iy)u} − e^{ixu} = e^{ixu}(e^{−yu} − 1)`
  have hfac : f u * Complex.exp (I * ((x : ℂ) + (y : ℂ) * I) * (u : ℂ)) -
      f u * Complex.exp (I * (x : ℂ) * (u : ℂ)) =
      f u * Complex.exp (I * (x : ℂ) * (u : ℂ)) * ((Real.exp (-(y * u)) : ℂ) - 1) := by
    rw [Complex.ofReal_exp, mul_sub, mul_one, mul_assoc, ← Complex.exp_add]
    congr 3
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [hfac, norm_mul, norm_mul, Complex.norm_exp]
  have hre : (I * (x : ℂ) * (u : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero, mul_one]
  have hnorm : ‖((Real.exp (-(y * u)) : ℝ) : ℂ) - 1‖ = |Real.exp (-(y * u)) - 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, mul_comm K]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (abs_exp_sub_one_le_mul_exp _).trans ?_
  have hyu : |-(y * u)| ≤ |y| * a := by
    rw [abs_neg, abs_mul]; exact mul_le_mul_of_nonneg_left hua (abs_nonneg y)
  rw [hK]
  calc |-(y * u)| * Real.exp |-(y * u)| ≤ |y| * a * Real.exp (|y| * a) :=
        mul_le_mul hyu (Real.exp_le_exp.mpr hyu) (Real.exp_pos _).le (by positivity)
    _ = |y| * a * Real.exp (a * |y|) := by rw [mul_comm a]

/-- `F_{k+2}(z) = −z² F_k(z)`. -/
theorem paperFT_cb_add_two {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (z : ℂ) :
    paperFT (cb ℓ (k + 2)) z = -(z ^ 2) * paperFT (cb ℓ k) z := by
  rw [paperFT_cb_succ hℓ (k + 1), paperFT_cb_succ hℓ k]
  ring_nf
  rw [I_sq]
  ring

/-- The window constant `K_k(ℓ) = 4(ℓ + 3)(∫‖Φ_ℓ^{(k)}‖ + ∫‖Φ_ℓ^{(k+2)}‖)`. -/
def shiftConst (ℓ : ℝ) (k : ℕ) : ℝ :=
  4 * (ℓ + 3) * ((∫ u, ‖cb ℓ k u‖) + ∫ u, ‖cb ℓ (k + 2) u‖)

theorem shiftConst_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) : 0 ≤ shiftConst ℓ k := by
  unfold shiftConst
  have := integral_nonneg fun u => norm_nonneg (cb ℓ k u)
  have := integral_nonneg fun u => norm_nonneg (cb ℓ (k + 2) u)
  positivity

/-- **The shift bound with decay.**  For `|y| ≤ 1`,
`‖F_k(x + iy) − F_k(x)‖ ≤ |y| e^{ℓ|y|} K_k(ℓ)/(1 + |x|)²`. -/
theorem norm_paperFT_cb_shift_sub_le {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (x : ℝ) {y : ℝ}
    (hy : |y| ≤ 1) :
    ‖paperFT (cb ℓ k) ((x : ℂ) + (y : ℂ) * I) - paperFT (cb ℓ k) x‖ ≤
      |y| * Real.exp (ℓ * |y|) * shiftConst ℓ k / (1 + |x|) ^ 2 := by
  have hI0 := integral_nonneg fun u => norm_nonneg (cb ℓ k u)
  have hI2 := integral_nonneg fun u => norm_nonneg (cb ℓ (k + 2) u)
  have hE := Real.exp_pos (ℓ * |y|)
  have hx1 : 0 < (1 + |x|) ^ 2 := by positivity
  rw [le_div_iff₀ hx1]
  rcases le_or_gt |x| 1 with hx | hx
  · -- near the origin: the direct bound
    have h := norm_paperFT_shift_sub_le hℓ.le (integrable_cb hℓ k) (cb_support hℓ k) x y
    have hsq : (1 + |x|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg x]
    have hL : ℓ ≤ ℓ + 3 := by linarith
    calc ‖paperFT (cb ℓ k) ((x : ℂ) + (y : ℂ) * I) - paperFT (cb ℓ k) x‖ * (1 + |x|) ^ 2
        ≤ (|y| * ℓ * Real.exp (ℓ * |y|) * ∫ u, ‖cb ℓ k u‖) * 4 :=
          mul_le_mul h hsq hx1.le (by positivity)
      _ ≤ |y| * Real.exp (ℓ * |y|) * shiftConst ℓ k := by
          unfold shiftConst
          have : 0 ≤ |y| * Real.exp (ℓ * |y|) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hL (mul_nonneg this hI0)]
  · -- away from the origin: `F_k = −F_{k+2}/z²`
    set z : ℂ := (x : ℂ) + (y : ℂ) * I with hz
    have hx0 : (x : ℂ) ≠ 0 := by
      intro h; rw [Complex.ofReal_eq_zero] at h; rw [h, abs_zero] at hx; linarith
    have hz0 : z ≠ 0 := by
      intro h; apply hx0; have := congrArg Complex.re h; simp [hz] at this; simp [this]
    have hkz : paperFT (cb ℓ k) z = -paperFT (cb ℓ (k + 2)) z / z ^ 2 := by
      rw [paperFT_cb_add_two hℓ k z]; field_simp
    have hkx : paperFT (cb ℓ k) x = -paperFT (cb ℓ (k + 2)) x / (x : ℂ) ^ 2 := by
      rw [paperFT_cb_add_two hℓ k x]; field_simp
    have hsplit : paperFT (cb ℓ k) z - paperFT (cb ℓ k) x =
        -(paperFT (cb ℓ (k + 2)) z - paperFT (cb ℓ (k + 2)) x) / z ^ 2 +
          paperFT (cb ℓ (k + 2)) x * ((z ^ 2 - (x : ℂ) ^ 2) / (z ^ 2 * (x : ℂ) ^ 2)) := by
      rw [hkz, hkx]; field_simp; ring
    have hnz : (x : ℝ) ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [hz, Complex.sq_norm, Complex.normSq_add_mul_I]; nlinarith [sq_nonneg y]
    have hxsq : 1 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    have hd := norm_paperFT_shift_sub_le hℓ.le (integrable_cb hℓ (k + 2)) (cb_support hℓ (k + 2)) x y
    have hF2 : ‖paperFT (cb ℓ (k + 2)) x‖ ≤ ∫ u, ‖cb ℓ (k + 2) u‖ := by
      have := norm_paperFT_le (integrable_cb hℓ (k + 2)) (cb_support hℓ (k + 2)) (x : ℂ)
      simpa using this
    -- `|z² − x²| = |2ixy − y²| ≤ 3|x||y|`
    have hnum : ‖z ^ 2 - (x : ℂ) ^ 2‖ ≤ 3 * |x| * |y| := by
      have e : z ^ 2 - (x : ℂ) ^ 2 = (((-(y ^ 2)) : ℝ) : ℂ) + ((2 * x * y : ℝ) : ℂ) * I := by
        rw [hz]; push_cast; ring_nf; rw [I_sq]; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg y), abs_mul, abs_mul,
        abs_two]
      have : y ^ 2 ≤ |x| * |y| := by
        rw [← sq_abs]; nlinarith [abs_nonneg y]
      linarith
    -- assemble: `(1+|x|)² ≤ 4x²`
    have h4 : (1 + |x|) ^ 2 ≤ 4 * x ^ 2 := by nlinarith [sq_abs x]
    have hzn : 0 < ‖z‖ ^ 2 := by positivity
    have hterm1 : ‖-(paperFT (cb ℓ (k + 2)) z - paperFT (cb ℓ (k + 2)) x) / z ^ 2‖ * (1 + |x|) ^ 2
        ≤ 4 * (|y| * ℓ * Real.exp (ℓ * |y|) * ∫ u, ‖cb ℓ (k + 2) u‖) := by
      rw [norm_div, norm_neg, norm_pow, div_mul_eq_mul_div, div_le_iff₀ hzn]
      have hd' : ‖paperFT (cb ℓ (k + 2)) z - paperFT (cb ℓ (k + 2)) x‖ ≤
          |y| * ℓ * Real.exp (ℓ * |y|) * ∫ u, ‖cb ℓ (k + 2) u‖ := by
        rw [hz, mul_comm ℓ |y|]; convert hd using 2; ring_nf
      have hP : 0 ≤ |y| * ℓ * Real.exp (ℓ * |y|) * ∫ u, ‖cb ℓ (k + 2) u‖ := by positivity
      calc ‖paperFT (cb ℓ (k + 2)) z - paperFT (cb ℓ (k + 2)) x‖ * (1 + |x|) ^ 2
          ≤ (|y| * ℓ * Real.exp (ℓ * |y|) * ∫ u, ‖cb ℓ (k + 2) u‖) * (4 * x ^ 2) :=
            mul_le_mul hd' h4 (by positivity) hP
        _ ≤ 4 * (|y| * ℓ * Real.exp (ℓ * |y|) * ∫ u, ‖cb ℓ (k + 2) u‖) * ‖z‖ ^ 2 := by
            nlinarith
    have hterm2 : ‖paperFT (cb ℓ (k + 2)) x * ((z ^ 2 - (x : ℂ) ^ 2) / (z ^ 2 * (x : ℂ) ^ 2))‖ *
        (1 + |x|) ^ 2 ≤ 12 * |y| * ∫ u, ‖cb ℓ (k + 2) u‖ := by
      rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have hden : x ^ 2 * x ^ 2 ≤ ‖z‖ ^ 2 * |x| ^ 2 := by
        rw [sq_abs]; exact mul_le_mul_of_nonneg_right hnz (sq_nonneg x)
      have hx2 : 0 < |x| ^ 2 := by positivity
      have hq : ‖z ^ 2 - (x : ℂ) ^ 2‖ / (‖z‖ ^ 2 * |x| ^ 2) ≤ 3 * |y| / (|x| * x ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hxa : |x| ^ 2 = x ^ 2 := sq_abs x
        calc ‖z ^ 2 - (x : ℂ) ^ 2‖ * (|x| * x ^ 2) ≤ 3 * |x| * |y| * (|x| * x ^ 2) :=
              mul_le_mul_of_nonneg_right hnum (by positivity)
          _ = 3 * |y| * (x ^ 2 * x ^ 2) := by rw [← hxa]; ring
          _ ≤ 3 * |y| * (‖z‖ ^ 2 * |x| ^ 2) := mul_le_mul_of_nonneg_left hden (by positivity)
      have hq2 : 3 * |y| / (|x| * x ^ 2) * (1 + |x|) ^ 2 ≤ 12 * |y| := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have : (1 + |x|) ^ 2 ≤ 4 * x ^ 2 := h4
        have hx1' : 1 ≤ |x| := hx.le
        nlinarith [abs_nonneg y, mul_le_mul_of_nonneg_left this (abs_nonneg y)]
      have hFq := mul_le_mul hF2 hq (by positivity) (integral_nonneg fun u => norm_nonneg _)
      calc ‖paperFT (cb ℓ (k + 2)) x‖ * (‖z ^ 2 - (x : ℂ) ^ 2‖ / (‖z‖ ^ 2 * |x| ^ 2)) *
            (1 + |x|) ^ 2
          ≤ (∫ u, ‖cb ℓ (k + 2) u‖) * (3 * |y| / (|x| * x ^ 2)) * (1 + |x|) ^ 2 :=
            mul_le_mul_of_nonneg_right hFq (by positivity)
        _ = (∫ u, ‖cb ℓ (k + 2) u‖) * (3 * |y| / (|x| * x ^ 2) * (1 + |x|) ^ 2) := by ring
        _ ≤ (∫ u, ‖cb ℓ (k + 2) u‖) * (12 * |y|) := mul_le_mul_of_nonneg_left hq2 hI2
        _ = 12 * |y| * ∫ u, ‖cb ℓ (k + 2) u‖ := by ring
    rw [hsplit]
    have htri := norm_add_le (-(paperFT (cb ℓ (k + 2)) z - paperFT (cb ℓ (k + 2)) x) / z ^ 2)
      (paperFT (cb ℓ (k + 2)) x * ((z ^ 2 - (x : ℂ) ^ 2) / (z ^ 2 * (x : ℂ) ^ 2)))
    have h1E : 1 ≤ Real.exp (ℓ * |y|) := Real.one_le_exp (by positivity)
    unfold shiftConst
    have hyE : |y| ≤ |y| * Real.exp (ℓ * |y|) := le_mul_of_one_le_right (abs_nonneg y) h1E
    nlinarith [mul_le_mul_of_nonneg_right htri hx1.le, mul_le_mul_of_nonneg_right hyE hI2,
      mul_nonneg (mul_nonneg (abs_nonneg y) hE.le) hI0, abs_nonneg y]

end

end RHTower.Littlewood
