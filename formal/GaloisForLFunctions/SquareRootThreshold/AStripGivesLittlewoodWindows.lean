import GaloisForLFunctions.RHTower.LittlewoodShortWindowZeroCount
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.RHTower.XiLocalZeroDensity
import GaloisForLFunctions.SquareRootThreshold.ZetaUniformTwinRadiusOfNearTopZeros

/-!
# Littlewood windows under a zero-free strip

The Littlewood window count (`LittlewoodShortWindowZeroCount`) uses the Riemann hypothesis only to
make the explicit-formula summand of a zero `ρ` equal to `m ψ_k(Im ρ − T)`.  For
`ρ = ½ + η + iγ` the summand is `m F_k(x − iη) conj F_k(x + iη)`, `x = γ − T`,
`F_k = (Φ_ℓ^{(k)})^`, and (`norm_wsummand_window_sub_le`)

  `|summand − m ψ_k(x)| ≤ m c_k(ℓ) |η| e^{2ℓ|η|}/(1 + |x|)⁴`,

from the decay `|F_k(x + iy)| ≤ e^{ℓ|y|} B/(1 + |x|)²` and the shift bound
`|F_k(x + iy) − F_k(x)| ≤ |y| e^{ℓ|y|} (ℓ + 3)B/(1 + |x|)²` (`norm_paperFT_cb_shift_sub_le`: the
bound `|e^{−yu} − 1| ≤ |y|ℓe^{ℓ|y|}` under the integral near `x = 0`, and `F_k = −F_{k+2}/z²` away
from it).

**Strip window count** (`exists_strip_window_count_bound`).  If every zero of height `≥ T₀` has
`|Re ρ − ½| ≤ d`, the errors sum to `c_k(ℓ)(d e^{2ℓd} C log T + O_{ℓ,T₀}(1))` by the weighted density
`Σ m/(1 + (T − γ)²) ≤ C log T`, and Littlewood's argument gives, for large `T`,

  `ℓA² N(T − D/ℓ, T + D/ℓ) ≥ (E/2 − d e^{2ℓd} s(ℓ) C) log T − M`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open Zeta23

namespace RHTower.Littlewood

noncomputable section

/-! ## Vertical shifts of the window transforms -/

/-- `|e^w − 1| ≤ |w| e^{|w|}`. -/
theorem abs_exp_sub_one_le_mul_exp (w : ℝ) : |Real.exp w - 1| ≤ |w| * Real.exp |w| := by
  rcases le_or_gt 0 w with hw | hw
  · rw [abs_of_nonneg hw, abs_of_nonneg (by linarith [Real.add_one_le_exp w])]
    -- `e^w (1 − w) ≤ e^w e^{−w} = 1`
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-w)) (Real.exp_pos w).le
    have h1 : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  · have hlt : Real.exp w < 1 := by simpa using Real.exp_lt_exp.mpr hw
    rw [abs_of_neg hw, abs_of_neg (by linarith)]
    have h := Real.add_one_le_exp w
    have h1 : 1 ≤ Real.exp (-w) := Real.one_le_exp (by linarith)
    nlinarith [mul_nonneg (neg_nonneg.mpr hw.le) (sub_nonneg.mpr h1)]

/-- **Vertical shift of a compactly supported transform.**  If `f` is integrable and supported in
`[−a, a]`, then `‖f̂(x + iy) − f̂(x)‖ ≤ |y| a e^{a|y|} ∫‖f‖`. -/
theorem norm_paperFT_shift_sub_le {f : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (hf : Integrable f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) (x y : ℝ) :
    ‖paperFT f ((x : ℂ) + (y : ℂ) * I) - paperFT f x‖ ≤
      |y| * a * Real.exp (a * |y|) * ∫ u, ‖f u‖ := by
  set K := |y| * a * Real.exp (a * |y|) with hK
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
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hre : (I * z * (u : ℂ)).re = -(z.im * u) := by
      simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]; ring
    have h1 : -(z.im * u) ≤ |z.im| * |u| := by rw [← abs_mul]; exact neg_le_abs _
    have h2 : |z.im| * |u| ≤ |y| * a :=
      mul_le_mul hz (hsupp u hu) (abs_nonneg _) (abs_nonneg _)
    rw [hre]; linarith
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
  beta_reduce
  by_cases hu : f u = 0
  · simp [hu]
  have hua := hsupp u hu
  -- `e^{i(x+iy)u} − e^{ixu} = e^{ixu}(e^{−yu} − 1)`
  have hexp : I * ((x : ℂ) + (y : ℂ) * I) * (u : ℂ) =
      I * (x : ℂ) * (u : ℂ) + ((-(y * u) : ℝ) : ℂ) := by
    push_cast; linear_combination (y : ℂ) * (u : ℂ) * I_sq
  have hfac : f u * Complex.exp (I * ((x : ℂ) + (y : ℂ) * I) * (u : ℂ)) -
      f u * Complex.exp (I * (x : ℂ) * (u : ℂ)) =
      f u * Complex.exp (I * (x : ℂ) * (u : ℂ)) * (((Real.exp (-(y * u)) - 1 : ℝ)) : ℂ) := by
    rw [hexp, Complex.exp_add, Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_one]
    ring
  rw [hfac, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have hre : (I * (x : ℂ) * (u : ℂ)).re = 0 := by
    simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]; ring
  rw [hre, Real.exp_zero, mul_one, mul_comm K]
  refine mul_le_mul_of_nonneg_left ((abs_exp_sub_one_le_mul_exp _).trans ?_) (norm_nonneg _)
  have hyu : |-(y * u)| ≤ |y| * a := by
    rw [abs_neg, abs_mul]; exact mul_le_mul_of_nonneg_left hua (abs_nonneg y)
  calc |-(y * u)| * Real.exp |-(y * u)| ≤ |y| * a * Real.exp (|y| * a) :=
        mul_le_mul hyu (Real.exp_le_exp.mpr hyu) (Real.exp_pos _).le (by positivity)
    _ = K := by rw [hK, mul_comm a |y|]

/-- `F_{k+2}(z) = −z² F_k(z)`. -/
theorem paperFT_cb_add_two {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (z : ℂ) :
    paperFT (cb ℓ (k + 2)) z = -(z ^ 2) * paperFT (cb ℓ k) z := by
  show paperFT (cb ℓ (k + 1 + 1)) z = _
  rw [paperFT_cb_succ hℓ (k + 1), paperFT_cb_succ hℓ k]
  linear_combination (z ^ 2 * paperFT (cb ℓ k) z) * I_sq

/-- The decay constant `B_k(ℓ) = 4(∫‖Φ_ℓ^{(k)}‖ + ∫‖Φ_ℓ^{(k+2)}‖)`. -/
def decayConst (ℓ : ℝ) (k : ℕ) : ℝ := 4 * ((∫ u, ‖cb ℓ k u‖) + ∫ u, ‖cb ℓ (k + 2) u‖)

theorem decayConst_nonneg (ℓ : ℝ) (k : ℕ) : 0 ≤ decayConst ℓ k := by
  have h0 : 0 ≤ ∫ u, ‖cb ℓ k u‖ := integral_nonneg fun u => norm_nonneg _
  have h2 : 0 ≤ ∫ u, ‖cb ℓ (k + 2) u‖ := integral_nonneg fun u => norm_nonneg _
  unfold decayConst; positivity

/-- `‖F_k(z)‖ ≤ e^{ℓ|Im z|} B_k(ℓ)/(1 + |Re z|)²`. -/
theorem norm_paperFT_cb_le_decay {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (z : ℂ) :
    ‖paperFT (cb ℓ k) z‖ ≤ Real.exp (ℓ * |z.im|) * decayConst ℓ k / (1 + |z.re|) ^ 2 := by
  have h := norm_paperFT_le_decay (contDiff_cb ℓ k) (cb_support hℓ k) z
  rw [deriv_cb, deriv_cb] at h
  rw [decayConst, mul_comm ℓ]
  exact h

/-- The shift constant `(ℓ + 3) B_k(ℓ)`. -/
def shiftConst (ℓ : ℝ) (k : ℕ) : ℝ := (ℓ + 3) * decayConst ℓ k

theorem shiftConst_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) : 0 ≤ shiftConst ℓ k :=
  mul_nonneg (by linarith) (decayConst_nonneg ℓ k)

private theorem re_add_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).re = x := by simp

private theorem im_add_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).im = y := by simp

/-- **The shift bound with decay.**  For `|y| ≤ 1`,
`‖F_k(x + iy) − F_k(x)‖ ≤ |y| e^{ℓ|y|} (ℓ + 3)B_k(ℓ)/(1 + |x|)²`. -/
theorem norm_paperFT_cb_shift_sub_le {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (x : ℝ) {y : ℝ}
    (hy : |y| ≤ 1) :
    ‖paperFT (cb ℓ k) ((x : ℂ) + (y : ℂ) * I) - paperFT (cb ℓ k) x‖ ≤
      |y| * Real.exp (ℓ * |y|) * shiftConst ℓ k / (1 + |x|) ^ 2 := by
  have hI0 : 0 ≤ ∫ u, ‖cb ℓ k u‖ := integral_nonneg fun u => norm_nonneg _
  have hI2 : 0 ≤ ∫ u, ‖cb ℓ (k + 2) u‖ := integral_nonneg fun u => norm_nonneg _
  have hE := Real.exp_pos (ℓ * |y|)
  have hy0 := abs_nonneg y
  have hx1 : 0 < (1 + |x|) ^ 2 := by positivity
  rw [le_div_iff₀ hx1]
  rcases le_or_gt |x| 1 with hx | hx
  · -- near the origin: the direct bound
    have h := norm_paperFT_shift_sub_le hℓ.le (integrable_cb hℓ k) (cb_support hℓ k) x y
    have hsq : (1 + |x|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg x]
    calc ‖paperFT (cb ℓ k) ((x : ℂ) + (y : ℂ) * I) - paperFT (cb ℓ k) x‖ * (1 + |x|) ^ 2
        ≤ (|y| * ℓ * Real.exp (ℓ * |y|) * ∫ u, ‖cb ℓ k u‖) * 4 :=
          mul_le_mul h hsq hx1.le (by positivity)
      _ ≤ |y| * Real.exp (ℓ * |y|) * shiftConst ℓ k := by
          unfold shiftConst decayConst
          nlinarith [mul_nonneg (mul_nonneg hy0 hE.le) hI0,
            mul_nonneg (mul_nonneg (mul_nonneg hy0 hE.le) (by linarith : (0 : ℝ) ≤ ℓ + 3)) hI2]
  · -- away from the origin: `F_k = −F_{k+2}/z²`
    set z : ℂ := (x : ℂ) + (y : ℂ) * I with hz
    have hx0 : (x : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; intro h; rw [h, abs_zero] at hx; linarith
    have hzre : z.re = x := re_add_mul_I x y
    have hz0 : z ≠ 0 := by
      intro h; rw [h, Complex.zero_re] at hzre; exact hx0 (by rw [← hzre]; simp)
    have hkz : paperFT (cb ℓ k) z = -paperFT (cb ℓ (k + 2)) z / z ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hz0), paperFT_cb_add_two hℓ k z]; ring
    have hkx : paperFT (cb ℓ k) x = -paperFT (cb ℓ (k + 2)) x / (x : ℂ) ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hx0), paperFT_cb_add_two hℓ k x]; ring
    have hsplit : paperFT (cb ℓ k) z - paperFT (cb ℓ k) x =
        -(paperFT (cb ℓ (k + 2)) z - paperFT (cb ℓ (k + 2)) x) / z ^ 2 +
          paperFT (cb ℓ (k + 2)) x * ((z ^ 2 - (x : ℂ) ^ 2) / (z ^ 2 * (x : ℂ) ^ 2)) := by
      rw [hkz, hkx]; field_simp; ring
    have hnz : x ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [hz, Complex.sq_norm, Complex.normSq_add_mul_I]; nlinarith [sq_nonneg y]
    have hxsq : 1 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    have hzn : 0 < ‖z‖ ^ 2 := lt_of_lt_of_le (by linarith) hnz
    have hd := norm_paperFT_shift_sub_le hℓ.le (integrable_cb hℓ (k + 2))
      (cb_support hℓ (k + 2)) x y
    have hF2 : ‖paperFT (cb ℓ (k + 2)) x‖ ≤ ∫ u, ‖cb ℓ (k + 2) u‖ := by
      have h := norm_paperFT_le (integrable_cb hℓ (k + 2)) (cb_support hℓ (k + 2)) (x : ℂ)
      simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul] at h
      exact h
    -- `|z² − x²| = |2ixy − y²| ≤ 3|x||y|`
    have hnum : ‖z ^ 2 - (x : ℂ) ^ 2‖ ≤ 3 * |x| * |y| := by
      have e : z ^ 2 - (x : ℂ) ^ 2 = (((-(y ^ 2)) : ℝ) : ℂ) + ((2 * x * y : ℝ) : ℂ) * I := by
        rw [hz]; push_cast; linear_combination (y : ℂ) ^ 2 * I_sq
      rw [e]
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_two, abs_pow]
      have : |y| ^ 2 ≤ |x| * |y| := by nlinarith [abs_nonneg y]
      linarith
    have h4 : (1 + |x|) ^ 2 ≤ 4 * x ^ 2 := by
      nlinarith [sq_abs x, mul_nonneg (sub_nonneg.mpr hx.le) (by positivity : (0 : ℝ) ≤ 3 * |x| + 1)]
    have hterm1 : ‖-(paperFT (cb ℓ (k + 2)) z - paperFT (cb ℓ (k + 2)) x) / z ^ 2‖ *
        (1 + |x|) ^ 2 ≤ 4 * (|y| * ℓ * Real.exp (ℓ * |y|) * ∫ u, ‖cb ℓ (k + 2) u‖) := by
      rw [norm_div, norm_neg, norm_pow, div_mul_eq_mul_div, div_le_iff₀ hzn]
      have hP : 0 ≤ |y| * ℓ * Real.exp (ℓ * |y|) * ∫ u, ‖cb ℓ (k + 2) u‖ := by positivity
      have hm := mul_le_mul_of_nonneg_left hnz hP
      calc ‖paperFT (cb ℓ (k + 2)) z - paperFT (cb ℓ (k + 2)) x‖ * (1 + |x|) ^ 2
          ≤ (|y| * ℓ * Real.exp (ℓ * |y|) * ∫ u, ‖cb ℓ (k + 2) u‖) * (4 * x ^ 2) :=
            mul_le_mul hd h4 (by positivity) hP
        _ ≤ 4 * (|y| * ℓ * Real.exp (ℓ * |y|) * ∫ u, ‖cb ℓ (k + 2) u‖) * ‖z‖ ^ 2 := by
            linarith
    have hterm2 : ‖paperFT (cb ℓ (k + 2)) x * ((z ^ 2 - (x : ℂ) ^ 2) / (z ^ 2 * (x : ℂ) ^ 2))‖ *
        (1 + |x|) ^ 2 ≤ 12 * |y| * ∫ u, ‖cb ℓ (k + 2) u‖ := by
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have hx2 : 0 < |x| ^ 2 := by rw [sq_abs]; linarith
      have hxa : |x| ^ 2 = x ^ 2 := sq_abs x
      have hden : x ^ 2 * x ^ 2 ≤ ‖z‖ ^ 2 * |x| ^ 2 := by
        rw [hxa]; exact mul_le_mul_of_nonneg_right hnz (sq_nonneg x)
      have hq : ‖z ^ 2 - (x : ℂ) ^ 2‖ / (‖z‖ ^ 2 * |x| ^ 2) ≤ 3 * |y| / (|x| * x ^ 2) := by
        rw [div_le_div_iff₀ (mul_pos hzn hx2) (mul_pos (by linarith) (by linarith))]
        calc ‖z ^ 2 - (x : ℂ) ^ 2‖ * (|x| * x ^ 2) ≤ 3 * |x| * |y| * (|x| * x ^ 2) :=
              mul_le_mul_of_nonneg_right hnum (by positivity)
          _ = 3 * |y| * (x ^ 2 * x ^ 2) := by rw [← hxa]; ring
          _ ≤ 3 * |y| * (‖z‖ ^ 2 * |x| ^ 2) := mul_le_mul_of_nonneg_left hden (by positivity)
      have hq2 : 3 * |y| / (|x| * x ^ 2) * (1 + |x|) ^ 2 ≤ 12 * |y| := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos (by linarith) (by linarith))]
        nlinarith [mul_le_mul_of_nonneg_left h4 hy0,
          mul_le_mul_of_nonneg_left hx.le (mul_nonneg hy0 (sq_nonneg x))]
      have hFq := mul_le_mul hF2 hq (by positivity) hI2
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
    calc _ ≤ (‖-(paperFT (cb ℓ (k + 2)) z - paperFT (cb ℓ (k + 2)) x) / z ^ 2‖ +
          ‖paperFT (cb ℓ (k + 2)) x * ((z ^ 2 - (x : ℂ) ^ 2) / (z ^ 2 * (x : ℂ) ^ 2))‖) *
            (1 + |x|) ^ 2 := mul_le_mul_of_nonneg_right htri hx1.le
      _ ≤ 4 * (|y| * ℓ * Real.exp (ℓ * |y|) * ∫ u, ‖cb ℓ (k + 2) u‖) +
          12 * |y| * ∫ u, ‖cb ℓ (k + 2) u‖ := by rw [add_mul]; exact add_le_add hterm1 hterm2
      _ ≤ |y| * Real.exp (ℓ * |y|) * shiftConst ℓ k := by
          unfold shiftConst decayConst
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hy0 hE.le) hℓ.le) hI0,
            mul_nonneg (mul_nonneg hy0 hE.le) hI0,
            mul_nonneg (mul_nonneg hy0 hI2) (sub_nonneg.mpr h1E)]

/-! ## The summand of an off-line zero -/

/-- `γ_ρ − T = x − iη` and `conj γ_ρ − T = x + iη` for `x = Im ρ − T`, `η = Re ρ − ½`. -/
theorem gammaOf_sub_eq (ρ : ℂ) (T : ℝ) :
    gammaOf ρ - T = ((ρ.im - T : ℝ) : ℂ) + ((-(ρ.re - 1 / 2) : ℝ) : ℂ) * I ∧
      conj (gammaOf ρ) - T = ((ρ.im - T : ℝ) : ℂ) + ((ρ.re - 1 / 2 : ℝ) : ℂ) * I := by
  constructor <;> apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im]

/-- The summand constant `c_k(ℓ) = 2(ℓ + 3)B_k(ℓ)²`. -/
def errConst (ℓ : ℝ) (k : ℕ) : ℝ := 2 * shiftConst ℓ k * decayConst ℓ k

theorem errConst_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) : 0 ≤ errConst ℓ k :=
  mul_nonneg (mul_nonneg zero_le_two (shiftConst_nonneg hℓ k)) (decayConst_nonneg ℓ k)

/-- **The summand of an off-line zero.**  For `|Re ρ − ½| ≤ 1`, the explicit-formula summand of the
window differs from `m ψ_k(Im ρ − T)` by at most `m c_k(ℓ)|η|e^{2ℓ|η|}/(1 + |Im ρ − T|)⁴`. -/
theorem norm_wsummand_window_sub_le {ℓ : ℝ} (hℓ : 0 < ℓ) (T : ℝ) (k : ℕ) {ρ : ℂ}
    (hρ : |ρ.re - 1 / 2| ≤ 1) :
    ‖zetaZeroConfig.Wsummand (window ℓ T k) (window ℓ T k) ρ -
        (((zetaZeroConfig.mult ρ : ℝ) * psi ℓ k (ρ.im - T) : ℝ) : ℂ)‖ ≤
      (zetaZeroConfig.mult ρ : ℝ) * (errConst ℓ k *
        (|ρ.re - 1 / 2| * Real.exp (2 * ℓ * |ρ.re - 1 / 2|)) / (1 + |ρ.im - T|) ^ 4) := by
  obtain ⟨ha, hb⟩ := gammaOf_sub_eq ρ T
  set x := ρ.im - T with hx
  set η := ρ.re - 1 / 2 with hη
  have hW : zetaZeroConfig.Wsummand (window ℓ T k) (window ℓ T k) ρ =
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (cb ℓ k) ((x : ℂ) + ((-η : ℝ) : ℂ) * I) *
        conj (paperFT (cb ℓ k) ((x : ℂ) + (η : ℂ) * I)) := by
    rw [ZeroConfig.Wsummand, paperFT_window, paperFT_window, ha, hb]
  have hψ : ((((zetaZeroConfig.mult ρ : ℝ) * psi ℓ k x : ℝ)) : ℂ) =
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (cb ℓ k) x * conj (paperFT (cb ℓ k) x) := by
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [psi]
    push_cast
    ring
  rw [hW, hψ]
  set A := paperFT (cb ℓ k) ((x : ℂ) + ((-η : ℝ) : ℂ) * I)
  set B := paperFT (cb ℓ k) ((x : ℂ) + (η : ℂ) * I)
  set C := paperFT (cb ℓ k) (x : ℂ)
  have hfac : (zetaZeroConfig.mult ρ : ℂ) * A * conj B -
      (zetaZeroConfig.mult ρ : ℂ) * C * conj C =
      (zetaZeroConfig.mult ρ : ℂ) * ((A - C) * conj B + C * conj (B - C)) := by
    rw [map_sub]; ring
  rw [hfac, norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have hAC : ‖A - C‖ ≤ |η| * Real.exp (ℓ * |η|) * shiftConst ℓ k / (1 + |x|) ^ 2 := by
    have h := norm_paperFT_cb_shift_sub_le hℓ k x (y := -η) (by rwa [abs_neg])
    rwa [abs_neg] at h
  have hBC : ‖B - C‖ ≤ |η| * Real.exp (ℓ * |η|) * shiftConst ℓ k / (1 + |x|) ^ 2 :=
    norm_paperFT_cb_shift_sub_le hℓ k x hρ
  have hB : ‖B‖ ≤ Real.exp (ℓ * |η|) * decayConst ℓ k / (1 + |x|) ^ 2 := by
    have h := norm_paperFT_cb_le_decay hℓ k ((x : ℂ) + (η : ℂ) * I)
    rwa [re_add_mul_I, im_add_mul_I] at h
  have hC : ‖C‖ ≤ decayConst ℓ k / (1 + |x|) ^ 2 := by
    have h := norm_paperFT_cb_le_decay hℓ k (x : ℂ)
    rwa [Complex.ofReal_re, Complex.ofReal_im, abs_zero, mul_zero, Real.exp_zero, one_mul] at h
  have hu : 0 < (1 + |x|) ^ 2 := by positivity
  have hE1 : 1 ≤ Real.exp (ℓ * |η|) := Real.one_le_exp (by positivity)
  have hS := shiftConst_nonneg hℓ k
  have hD := decayConst_nonneg ℓ k
  have hE2 : Real.exp (2 * ℓ * |η|) = Real.exp (ℓ * |η|) * Real.exp (ℓ * |η|) := by
    rw [← Real.exp_add]; ring_nf
  have h4 : (1 + |x|) ^ 4 = (1 + |x|) ^ 2 * (1 + |x|) ^ 2 := by ring
  rw [hE2, h4]
  set E := Real.exp (ℓ * |η|)
  set u := (1 + |x|) ^ 2
  have h1 := mul_le_mul hAC hB (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul hC hBC (norm_nonneg _) (by positivity)
  have h3 : decayConst ℓ k / u * (|η| * E * shiftConst ℓ k / u) ≤
      |η| * E * shiftConst ℓ k / u * (E * decayConst ℓ k / u) := by
    rw [mul_comm (decayConst ℓ k / u)]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (le_mul_of_one_le_left hD hE1) hu.le) (by positivity)
  calc ‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - C‖
      ≤ |η| * E * shiftConst ℓ k / u * (E * decayConst ℓ k / u) +
          |η| * E * shiftConst ℓ k / u * (E * decayConst ℓ k / u) := add_le_add h1 (h2.trans h3)
    _ = errConst ℓ k * (|η| * (E * E)) / (u * u) := by unfold errConst; ring

/-! ## Comparison with the explicit formula -/

/-- If the summands of the window are within `e ρ` of `m ψ_k(γ − T)`, the zero sum
`Σ m ψ_k(γ − T)` converges and is within `Σ e` of the explicit-formula integral. -/
theorem abs_tsum_psi_sub_integral_le {ℓ : ℝ} (hℓ : 0 < ℓ) (T : ℝ) (k : ℕ)
    {e : zetaZeroConfig.carrier → ℝ} (he : Summable e)
    (hle : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand (window ℓ T k) (window ℓ T k) ρ -
        (((zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T) : ℝ) : ℂ)‖ ≤ e ρ) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
        (zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T)) ∧
      Integrable (fun τ : ℝ => psi ℓ k (τ - T) * nuX (Real.exp (2 * ℓ)) τ) ∧
      |∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T) -
        ∫ τ : ℝ, psi ℓ k (τ - T) * nuX (Real.exp (2 * ℓ)) τ| ≤ ∑' ρ, e ρ := by
  obtain ⟨hs, hi, hEF⟩ := paperInputs_zeta.EF (2 * ℓ) (by positivity) (window ℓ T k)
    (window ℓ T k) (contDiff_window ℓ T k) (contDiff_window ℓ T k) (tsupport_window hℓ T k)
    (tsupport_window hℓ T k)
  have hdn : Summable (fun ρ : zetaZeroConfig.carrier =>
      ‖(((zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T) : ℝ) : ℂ) -
        zetaZeroConfig.Wsummand (window ℓ T k) (window ℓ T k) ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun ρ => by rw [norm_sub_rev]; exact hle ρ) he
  have hd := hdn.of_norm
  have ha : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T)) := by
    refine Complex.summable_ofReal.mp ?_
    simpa using hd.add hs
  have hint : (fun τ : ℝ => paperFT (window ℓ T k) τ *
      (starRingEnd ℂ) (paperFT (window ℓ T k) τ) * (nuX (Real.exp (2 * ℓ)) τ : ℂ)) =
      fun τ => ((psi ℓ k (τ - T) * nuX (Real.exp (2 * ℓ)) τ : ℝ) : ℂ) := by
    funext τ; exact integrand_window ℓ T _ k τ
  rw [hint] at hi hEF
  refine ⟨ha, hi.re, ?_⟩
  rw [ZeroConfig.W, integral_complex_ofReal] at hEF
  have key : ((∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T) -
        ∫ τ : ℝ, psi ℓ k (τ - T) * nuX (Real.exp (2 * ℓ)) τ : ℝ) : ℂ) =
      ∑' ρ : zetaZeroConfig.carrier,
        ((((zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T) : ℝ) : ℂ) -
          zetaZeroConfig.Wsummand (window ℓ T k) (window ℓ T k) ρ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_tsum, ← hEF,
      (Complex.summable_ofReal.mpr ha).tsum_sub hs]
  have hn : |∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T) -
        ∫ τ : ℝ, psi ℓ k (τ - T) * nuX (Real.exp (2 * ℓ)) τ| =
      ‖∑' ρ : zetaZeroConfig.carrier,
        ((((zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T) : ℝ) : ℂ) -
          zetaZeroConfig.Wsummand (window ℓ T k) (window ℓ T k) ρ)‖ := by
    rw [← key, Complex.norm_real, Real.norm_eq_abs]
  rw [hn]
  refine (norm_tsum_le_tsum_norm hdn).trans ?_
  exact hdn.tsum_le_tsum (fun ρ => by rw [norm_sub_rev]; exact hle ρ) he

/-! ## Counting and the analytic lower bound -/

/-- **Counting inequality** (`tsum_psi_zero_le` without RH): for summable zero sums and `δ > 0`,
`Σ m ψ₀(γ − T) ≤ (ℓA)² N(T − δ, T + δ) + δ⁻² Σ m ψ₁(γ − T)`. -/
theorem tsum_psi_zero_le_of_summable {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (T : ℝ)
    (hs0 : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T))
    (hs1 : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 1 ((ρ : ℂ).im - T)) :
    ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) ≤
      (ℓ * bumpMass) ^ 2 * (zetaZeroConfig.N (T - δ) (T + δ) : ℝ) +
        (∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 1 ((ρ : ℂ).im - T)) / δ ^ 2 := by
  classical
  set g : zetaZeroConfig.carrier → ℝ := fun ρ =>
    (if T - δ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T + δ then (zetaZeroConfig.mult ρ : ℝ) else 0) with hg
  have hgs : Summable g := by
    have hfin := zetaZeroConfig.finite_window (T - δ) (T + δ)
    refine summable_of_hasFiniteSupport ((hfin.preimage Subtype.val_injective.injOn).subset ?_)
    intro b hb
    simp only [Function.mem_support, hg, ne_eq, ite_eq_right_iff, not_forall] at hb
    obtain ⟨h, -⟩ := hb
    exact ⟨b.2, h⟩
  have hpt : ∀ ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) ≤
        (ℓ * bumpMass) ^ 2 * g ρ +
          (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 1 ((ρ : ℂ).im - T) / δ ^ 2 := by
    intro ρ
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have h := mul_le_mul_of_nonneg_left (psi_zero_le_window hℓ hδ ((ρ : ℂ).im - T)) hm
    have hiff : (-δ < (ρ : ℂ).im - T ∧ (ρ : ℂ).im - T ≤ δ) ↔
        (T - δ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T + δ) := by
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    simp only [hg]
    by_cases hw : T - δ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T + δ
    · rw [if_pos (hiff.mpr hw)] at h; rw [if_pos hw]
      calc (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T)
          ≤ (zetaZeroConfig.mult ρ : ℝ) * ((ℓ * bumpMass) ^ 2 * 1 +
              psi ℓ 1 ((ρ : ℂ).im - T) / δ ^ 2) := h
        _ = _ := by ring
    · rw [if_neg (fun h' => hw (hiff.mp h'))] at h; rw [if_neg hw]
      calc (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T)
          ≤ (zetaZeroConfig.mult ρ : ℝ) * ((ℓ * bumpMass) ^ 2 * 0 +
              psi ℓ 1 ((ρ : ℂ).im - T) / δ ^ 2) := h
        _ = _ := by ring
  have hR : Summable fun ρ : zetaZeroConfig.carrier => (ℓ * bumpMass) ^ 2 * g ρ +
      (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 1 ((ρ : ℂ).im - T) / δ ^ 2 :=
    (hgs.mul_left _).add (hs1.div_const _)
  refine (Summable.tsum_le_tsum hpt hs0 hR).trans (le_of_eq ?_)
  rw [hgs.mul_left _ |>.tsum_add (hs1.div_const _), tsum_mul_left, tsum_div_const,
    tsum_window_mult]

/-- **The analytic side of Littlewood's argument.**  Whenever
`∫ψ₀(τ−T)ν_X ≤ Y + δ⁻² ∫ψ₁(τ−T)ν_X` with `δ = D/ℓ`,

  `Y/ℓ ≥ (E/2) log T − M − 3πE(1 + 3e^{4ℓ})`.

This is `exists_window_count_bound` with the zero count `(ℓA)²N` replaced by an arbitrary `Y`. -/
theorem exists_analytic_window_bound :
    ∃ M : ℝ, ∀ ℓ T Y : ℝ, 1 ≤ ℓ → 2 ≤ T →
      ∫ τ, psi ℓ 0 (τ - T) * nuX (Real.exp (2 * ℓ)) τ ≤
        Y + (∫ τ, psi ℓ 1 (τ - T) * nuX (Real.exp (2 * ℓ)) τ) / (windowD / ℓ) ^ 2 →
      Integrable (fun τ => psi ℓ 0 (τ - T) * nuX (Real.exp (2 * ℓ)) τ) →
      Integrable (fun τ => psi ℓ 1 (τ - T) * nuX (Real.exp (2 * ℓ)) τ) →
      energy 0 / 2 * Real.log T - M - 3 * Real.pi * energy 0 * (1 + 3 * Real.exp (2 * ℓ) ^ 2) ≤
        Y / ℓ := by
  obtain ⟨C, hC0, hC⟩ := exists_stirling
  refine ⟨energy 0 / 2 * Real.log (12 * Real.pi) + 4 * Real.pi * energy 0 * C +
    8 * Real.pi * energy 1 * (C + 2) + 8 * Real.pi * (1 / (2 * Real.pi) + C) * energy 2,
    fun ℓ T Y hℓ hT hcount hi0 hi1 => ?_⟩
  have hℓ0 : 0 < ℓ := by linarith
  have hT0 : 0 < T := by linarith
  have hπ := Real.pi_pos
  have hE0 := energy_zero_pos
  have hE1 := energy_nonneg 1
  have hE2 := energy_nonneg 2
  have hD := one_le_windowD
  have hD2 := windowD_sq
  have hDpos : 0 < windowD := by linarith
  have hlow := integral_psi_zero_nuX_ge hℓ0 hT0 hi0
  have hup := integral_psi_one_nuX_le hC0 hC hℓ0 (by linarith) hi1
  set D := windowD
  set K := 1 + 3 * Real.exp (2 * ℓ) ^ 2 with hK
  have hK1 : 1 ≤ K := by have := sq_nonneg (Real.exp (2 * ℓ)); linarith
  set m₁ := mu (T / 2)
  set m₃ := mu (3 * T / 2)
  set c := 1 / (2 * Real.pi) + C with hc
  have hc0 : 0 ≤ c := by positivity
  set S₀ := ∫ τ, psi ℓ 0 (τ - T) * nuX (Real.exp (2 * ℓ)) τ
  set S₁ := ∫ τ, psi ℓ 1 (τ - T) * nuX (Real.exp (2 * ℓ)) τ
  set Q := 2 * Real.pi * (m₁ - K) * energy 0 -
    (m₁ + 1) * (8 * Real.pi * energy 1) / (T ^ 2 * ℓ ^ 2) -
    2 * Real.pi * (m₃ + K) * energy 1 / D ^ 2 -
    8 * Real.pi * c * energy 2 / (D ^ 2 * T ^ 2 * ℓ ^ 2) with hQ
  have hdiv : S₁ / (D / ℓ) ^ 2 ≤ ((m₃ + K) * (2 * Real.pi * energy 1 / ℓ) +
      c * (4 / T ^ 2) * (2 * Real.pi * energy 2 / ℓ ^ 3)) / (D / ℓ) ^ 2 :=
    div_le_div_of_nonneg_right hup (by positivity)
  have hℓne : ℓ ≠ 0 := hℓ0.ne'
  have hTne : T ≠ 0 := hT0.ne'
  have hDne : D ≠ 0 := hDpos.ne'
  have hid : (m₁ - K) * (2 * Real.pi * ℓ * energy 0) -
      (m₁ + 1) * (4 / T ^ 2) * (2 * Real.pi * energy 1 / ℓ) -
      ((m₃ + K) * (2 * Real.pi * energy 1 / ℓ) +
        c * (4 / T ^ 2) * (2 * Real.pi * energy 2 / ℓ ^ 3)) / (D / ℓ) ^ 2 = ℓ * Q := by
    rw [hQ]; field_simp; ring
  have hsq : Y = ℓ * (Y / ℓ) := by field_simp
  have hkey : ℓ * Q ≤ ℓ * (Y / ℓ) := by linarith
  have hQle : Q ≤ Y / ℓ := le_of_mul_le_mul_left hkey hℓ0
  have hm3K : 0 ≤ m₃ + K := by linarith [neg_one_lt_mu (3 * T / 2)]
  have hb1 : 2 * Real.pi * (m₃ + K) * energy 1 / D ^ 2 ≤ Real.pi * (m₃ + K) * energy 0 := by
    rw [div_le_iff₀ (by positivity), hD2]
    have h : energy 1 ≤ energy 0 / 2 * (2 * energy 1 / energy 0 + 1) := by
      have e : energy 0 / 2 * (2 * energy 1 / energy 0 + 1) = energy 1 + energy 0 / 2 := by
        field_simp
      rw [e]; linarith
    calc 2 * Real.pi * (m₃ + K) * energy 1
        ≤ 2 * Real.pi * (m₃ + K) * (energy 0 / 2 * (2 * energy 1 / energy 0 + 1)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = Real.pi * (m₃ + K) * energy 0 * (2 * energy 1 / energy 0 + 1) := by ring
  have hm1 : m₁ + 1 ≤ (C + 2) * (T ^ 2 * ℓ ^ 2) := by
    have h := mu_half_le hC0 hC hT
    have hT2 : T ≤ T ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hT0.le (by linarith)
    have hl2 : 1 ≤ ℓ ^ 2 := one_le_pow₀ hℓ
    have hT1 : 1 ≤ T ^ 2 := one_le_pow₀ (by linarith)
    have h3 : (C + 2) * T ^ 2 ≤ (C + 2) * (T ^ 2 * ℓ ^ 2) := by
      have := mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ (C + 2) * T ^ 2)
      linarith
    have h4 : C + 1 ≤ (C + 1) * T ^ 2 := le_mul_of_one_le_right (by linarith) hT1
    linarith
  have hb2 : (m₁ + 1) * (8 * Real.pi * energy 1) / (T ^ 2 * ℓ ^ 2) ≤
      8 * Real.pi * energy 1 * (C + 2) := by
    rw [div_le_iff₀ (by positivity)]
    calc (m₁ + 1) * (8 * Real.pi * energy 1)
        ≤ (C + 2) * (T ^ 2 * ℓ ^ 2) * (8 * Real.pi * energy 1) :=
          mul_le_mul_of_nonneg_right hm1 (by positivity)
      _ = 8 * Real.pi * energy 1 * (C + 2) * (T ^ 2 * ℓ ^ 2) := by ring
  have hb3 : 8 * Real.pi * c * energy 2 / (D ^ 2 * T ^ 2 * ℓ ^ 2) ≤ 8 * Real.pi * c * energy 2 := by
    apply div_le_self (by positivity)
    have h1 : 1 ≤ D ^ 2 := one_le_pow₀ hD
    have h2 : 1 ≤ T ^ 2 := one_le_pow₀ (by linarith)
    have h3 : 1 ≤ ℓ ^ 2 := one_le_pow₀ hℓ
    have h4 : 1 ≤ D ^ 2 * T ^ 2 := one_le_mul_of_one_le_of_one_le h1 h2
    exact one_le_mul_of_one_le_of_one_le h4 h3
  have hst := mu_half_sub_ge hC0 hC hT
  have hst2 : energy 0 / 2 * (Real.log T - Real.log (12 * Real.pi)) - 4 * Real.pi * energy 0 * C ≤
      2 * Real.pi * energy 0 * (m₁ - m₃ / 2) := by
    have h := mul_le_mul_of_nonneg_left hst (by positivity : (0 : ℝ) ≤ 2 * Real.pi * energy 0)
    have e : 2 * Real.pi * energy 0 *
        ((Real.log T - Real.log (12 * Real.pi)) / (4 * Real.pi) - 2 * C) =
        energy 0 / 2 * (Real.log T - Real.log (12 * Real.pi)) - 4 * Real.pi * energy 0 * C := by
      field_simp; ring
    linarith
  have hQ2 : Q = 2 * Real.pi * energy 0 * (m₁ - m₃ / 2) - 3 * Real.pi * energy 0 * K -
      (m₁ + 1) * (8 * Real.pi * energy 1) / (T ^ 2 * ℓ ^ 2) -
      (2 * Real.pi * (m₃ + K) * energy 1 / D ^ 2 - Real.pi * (m₃ + K) * energy 0) -
      8 * Real.pi * c * energy 2 / (D ^ 2 * T ^ 2 * ℓ ^ 2) := by
    rw [hQ]; ring
  linarith

/-! ## The strip -/

/-- Every zero of height at least `T₀` lies within `d` of the critical line. -/
def ZeroFreeStrip (d T₀ : ℝ) : Prop :=
  ∀ ρ ∈ zetaZeroConfig.carrier, T₀ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ d

/-- The weighted density on the zeros: `Σ_ρ m/(1 + (T − γ)²) ≤ C log T` for large `T`. -/
theorem exists_tsum_carrier_density_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      Summable (fun ρ : zetaZeroConfig.carrier =>
        (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (T - (ρ : ℂ).im) ^ 2))) ∧
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (T - (ρ : ℂ).im) ^ 2)) ≤ C * Real.log T := by
  obtain ⟨C, hC0, hC⟩ := exists_tsum_weighted_density_le
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hC] with T hT
  obtain ⟨hsum, hle⟩ := hT
  have hpart : ∀ s : Finset zetaZeroConfig.carrier,
      ∑ ρ ∈ s, (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (T - (ρ : ℂ).im) ^ 2)) ≤
        C * Real.log T := by
    intro s
    have h := GaloisForLFunctions.SquareRootThreshold.sum_mult_le_tsum_copies
      (fun z : ℂ => 1 / (1 + (T - z.im) ^ 2)) (fun q => by positivity) hsum
      (s.map (Function.Embedding.subtype _)) (by
        intro ρ hρ
        obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp hρ
        exact b.2)
    rw [Finset.sum_map] at h
    exact h.trans hle
  have hnn : ∀ ρ : zetaZeroConfig.carrier,
      0 ≤ (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (T - (ρ : ℂ).im) ^ 2)) :=
    fun ρ => by positivity
  have hs := summable_of_sum_le hnn hpart
  exact ⟨hs, hs.tsum_le_of_sum_le hpart⟩

/-- **The summand weight under the strip.**  Zeros of height `≥ T₀` contribute
`d e^{2ℓd}/(1 + (T − γ)²)`, the finitely many lower ones at most `e^{2ℓ}`. -/
theorem stripWeight_le {ℓ d T₀ : ℝ} (T : ℝ) (hℓ : 0 < ℓ) (hd : 0 ≤ d) (hS : ZeroFreeStrip d T₀)
    (ρ : zetaZeroConfig.carrier) :
    |(ρ : ℂ).re - 1 / 2| * Real.exp (2 * ℓ * |(ρ : ℂ).re - 1 / 2|) / (1 + |(ρ : ℂ).im - T|) ^ 4 ≤
      d * Real.exp (2 * ℓ * d) * (1 / (1 + (T - (ρ : ℂ).im) ^ 2)) +
        Real.exp (2 * ℓ) * (if -T₀ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T₀ then 1 else 0) := by
  have hstrip := zetaZeroConfig.strip ρ ρ.2
  set η := |(ρ : ℂ).re - 1 / 2| with hη
  have hη0 : 0 ≤ η := abs_nonneg _
  have hη1 : η ≤ 1 := by rw [hη, abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
  set x := (ρ : ℂ).im - T with hx
  have hx1 : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
  have h4 : 1 + (T - (ρ : ℂ).im) ^ 2 ≤ (1 + |x|) ^ 4 := by
    have e : (T - (ρ : ℂ).im) ^ 2 = |x| ^ 2 := by rw [sq_abs, hx]; ring
    have h2 : (1 + |x|) ^ 2 ≤ (1 + |x|) ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
    rw [e]; nlinarith [abs_nonneg x]
  have hind : 0 ≤ Real.exp (2 * ℓ) *
      (if -T₀ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T₀ then (1 : ℝ) else 0) := by
    split_ifs <;> positivity
  by_cases hγ : T₀ ≤ |(ρ : ℂ).im|
  · have hηd : η ≤ d := hS ρ ρ.2 hγ
    have hnum : η * Real.exp (2 * ℓ * η) ≤ d * Real.exp (2 * ℓ * d) :=
      mul_le_mul hηd (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le hd
    have h1 : η * Real.exp (2 * ℓ * η) / (1 + |x|) ^ 4 ≤
        d * Real.exp (2 * ℓ * d) * (1 / (1 + (T - (ρ : ℂ).im) ^ 2)) := by
      rw [mul_one_div]
      exact div_le_div₀ (by positivity) hnum (by positivity) h4
    linarith
  · push Not at hγ
    have hin : -T₀ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T₀ := by
      have := abs_lt.mp hγ; exact ⟨this.1, this.2.le⟩
    rw [if_pos hin, mul_one]
    have hnum : η * Real.exp (2 * ℓ * η) ≤ Real.exp (2 * ℓ) := by
      calc η * Real.exp (2 * ℓ * η) ≤ 1 * Real.exp (2 * ℓ) :=
            mul_le_mul hη1 (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le zero_le_one
        _ = _ := one_mul _
    have h1 : η * Real.exp (2 * ℓ * η) / (1 + |x|) ^ 4 ≤ η * Real.exp (2 * ℓ * η) :=
      div_le_self (by positivity) (one_le_pow₀ hx1)
    have h2 : 0 ≤ d * Real.exp (2 * ℓ * d) * (1 / (1 + (T - (ρ : ℂ).im) ^ 2)) := by positivity
    linarith

/-- The strip constant `s(ℓ) = (c₀(ℓ) + c₁(ℓ)/(D/ℓ)²)/ℓ`. -/
def stripConst (ℓ : ℝ) : ℝ := (errConst ℓ 0 + errConst ℓ 1 / (windowD / ℓ) ^ 2) / ℓ

/-- **Littlewood windows under a zero-free strip.**  There is `C > 0` such that, if every zero of
height `≥ T₀` lies within `d` of the critical line, then for every `ℓ ≥ 1` and all large `T`,

  `ℓA² N(T − D/ℓ, T + D/ℓ) ≥ (E/2) log T − M − d e^{2ℓd} s(ℓ) C log T`. -/
theorem exists_strip_window_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ d T₀ : ℝ, 1 ≤ ℓ → 0 ≤ d → ZeroFreeStrip d T₀ →
      ∃ M : ℝ, ∀ᶠ T : ℝ in atTop,
        energy 0 / 2 * Real.log T - M -
            d * Real.exp (2 * ℓ * d) * stripConst ℓ * C * Real.log T ≤
          ℓ * bumpMass ^ 2 * (zetaZeroConfig.N (T - windowD / ℓ) (T + windowD / ℓ) : ℝ) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_tsum_carrier_density_le
  obtain ⟨M₀, hM₀⟩ := exists_analytic_window_bound
  refine ⟨C, hC0, fun ℓ d T₀ hℓ hd hS => ?_⟩
  have hℓ0 : 0 < ℓ := by linarith
  set N₀ : ℝ := (zetaZeroConfig.N (-T₀) T₀ : ℝ) with hN₀
  refine ⟨M₀ + 3 * Real.pi * energy 0 * (1 + 3 * Real.exp (2 * ℓ) ^ 2) +
    stripConst ℓ * (Real.exp (2 * ℓ) * N₀), ?_⟩
  filter_upwards [hC, eventually_ge_atTop (2 : ℝ)] with T hT hT2
  obtain ⟨hsum, hdens⟩ := hT
  set δ := windowD / ℓ with hδ
  have hδ0 : 0 < δ := div_pos (by linarith [one_le_windowD]) hℓ0
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hde : 0 ≤ d * Real.exp (2 * ℓ * d) := by positivity
  -- the low zeros
  have hgs : Summable (fun ρ : zetaZeroConfig.carrier =>
      if -T₀ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T₀ then (zetaZeroConfig.mult ρ : ℝ) else 0) := by
    have hfin := zetaZeroConfig.finite_window (-T₀) T₀
    refine summable_of_hasFiniteSupport ((hfin.preimage Subtype.val_injective.injOn).subset ?_)
    intro b hb
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hb
    obtain ⟨h, -⟩ := hb
    exact ⟨b.2, h⟩
  set B : ℝ := d * Real.exp (2 * ℓ * d) * (C * Real.log T) + Real.exp (2 * ℓ) * N₀ with hB
  -- the summand errors and their sums
  have herr : ∀ k : ℕ, ∃ e : zetaZeroConfig.carrier → ℝ, Summable e ∧
      (∑' ρ, e ρ ≤ errConst ℓ k * B) ∧
      ∀ ρ : zetaZeroConfig.carrier,
        ‖zetaZeroConfig.Wsummand (window ℓ T k) (window ℓ T k) ρ -
          (((zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T) : ℝ) : ℂ)‖ ≤ e ρ := by
    intro k
    have hc := errConst_nonneg hℓ0 k
    refine ⟨fun ρ => errConst ℓ k * (d * Real.exp (2 * ℓ * d) *
        ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (T - (ρ : ℂ).im) ^ 2))) +
      Real.exp (2 * ℓ) *
        (if -T₀ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T₀ then (zetaZeroConfig.mult ρ : ℝ) else 0)),
      ((hsum.mul_left _).add (hgs.mul_left _)).mul_left _, ?_, ?_⟩
    · rw [tsum_mul_left, (hsum.mul_left _).tsum_add (hgs.mul_left _), tsum_mul_left,
        tsum_mul_left, tsum_window_mult]
      refine mul_le_mul_of_nonneg_left ?_ hc
      have := mul_le_mul_of_nonneg_left hdens hde
      linarith
    · intro ρ
      have hstrip := zetaZeroConfig.strip ρ ρ.2
      have hρ1 : |(ρ : ℂ).re - 1 / 2| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
      refine (norm_wsummand_window_sub_le hℓ0 T k hρ1).trans ?_
      have hq := stripWeight_le T hℓ0 hd hS ρ
      have hm : (0 : ℝ) ≤ zetaZeroConfig.mult (ρ : ℂ) := Nat.cast_nonneg _
      have hind : (zetaZeroConfig.mult (ρ : ℂ) : ℝ) *
          (if -T₀ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T₀ then 1 else 0) =
          if -T₀ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T₀ then (zetaZeroConfig.mult (ρ : ℂ) : ℝ) else 0 := by
        split_ifs <;> simp
      calc (zetaZeroConfig.mult (ρ : ℂ) : ℝ) * (errConst ℓ k *
            (|(ρ : ℂ).re - 1 / 2| * Real.exp (2 * ℓ * |(ρ : ℂ).re - 1 / 2|)) /
              (1 + |(ρ : ℂ).im - T|) ^ 4)
          = errConst ℓ k * ((zetaZeroConfig.mult (ρ : ℂ) : ℝ) *
            (|(ρ : ℂ).re - 1 / 2| * Real.exp (2 * ℓ * |(ρ : ℂ).re - 1 / 2|) /
              (1 + |(ρ : ℂ).im - T|) ^ 4)) := by ring
        _ ≤ errConst ℓ k * ((zetaZeroConfig.mult (ρ : ℂ) : ℝ) *
            (d * Real.exp (2 * ℓ * d) * (1 / (1 + (T - (ρ : ℂ).im) ^ 2)) +
              Real.exp (2 * ℓ) * (if -T₀ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T₀ then 1 else 0))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hm) hc
        _ = _ := by beta_reduce; rw [mul_add, ← hind]; ring
  obtain ⟨e₀, he₀s, he₀t, he₀⟩ := herr 0
  obtain ⟨e₁, he₁s, he₁t, he₁⟩ := herr 1
  obtain ⟨hs₀, hi₀, hd₀⟩ := abs_tsum_psi_sub_integral_le hℓ0 T 0 he₀s he₀
  obtain ⟨hs₁, hi₁, hd₁⟩ := abs_tsum_psi_sub_integral_le hℓ0 T 1 he₁s he₁
  have hcount := tsum_psi_zero_le_of_summable hℓ0 hδ0 T hs₀ hs₁
  have h0 := (abs_le.mp hd₀).1
  have h1 := (abs_le.mp hd₁).2
  set N : ℝ := (zetaZeroConfig.N (T - δ) (T + δ) : ℝ)
  set Z₀ := ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T)
  set Z₁ := ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 1 ((ρ : ℂ).im - T)
  set S₀ := ∫ τ : ℝ, psi ℓ 0 (τ - T) * nuX (Real.exp (2 * ℓ)) τ
  set S₁ := ∫ τ : ℝ, psi ℓ 1 (τ - T) * nuX (Real.exp (2 * ℓ)) τ
  set E₀ := ∑' ρ, e₀ ρ
  set E₁ := ∑' ρ, e₁ ρ
  have hZ₁ : Z₁ / δ ^ 2 ≤ S₁ / δ ^ 2 + E₁ / δ ^ 2 := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hδ2.le
  have hY : S₀ ≤ ((ℓ * bumpMass) ^ 2 * N + E₀ + E₁ / δ ^ 2) + S₁ / δ ^ 2 := by linarith
  have hA := hM₀ ℓ T _ hℓ hT2 hY hi₀ hi₁
  have hsplit : ((ℓ * bumpMass) ^ 2 * N + E₀ + E₁ / δ ^ 2) / ℓ =
      ℓ * bumpMass ^ 2 * N + (E₀ + E₁ / δ ^ 2) / ℓ := by
    field_simp; ring
  have h3 : E₀ + E₁ / δ ^ 2 ≤ (errConst ℓ 0 + errConst ℓ 1 / δ ^ 2) * B := by
    have := div_le_div_of_nonneg_right he₁t hδ2.le
    have e : (errConst ℓ 0 + errConst ℓ 1 / δ ^ 2) * B = errConst ℓ 0 * B +
        errConst ℓ 1 * B / δ ^ 2 := by ring
    rw [e]; linarith
  have hbound : (E₀ + E₁ / δ ^ 2) / ℓ ≤ stripConst ℓ * B := by
    calc (E₀ + E₁ / δ ^ 2) / ℓ ≤ (errConst ℓ 0 + errConst ℓ 1 / δ ^ 2) * B / ℓ :=
          div_le_div_of_nonneg_right h3 hℓ0.le
      _ = stripConst ℓ * B := by unfold stripConst; rw [← hδ]; ring
  have hB' : stripConst ℓ * B = d * Real.exp (2 * ℓ * d) * stripConst ℓ * C * Real.log T +
      stripConst ℓ * (Real.exp (2 * ℓ) * N₀) := by rw [hB]; ring
  linarith

end

end RHTower.Littlewood
