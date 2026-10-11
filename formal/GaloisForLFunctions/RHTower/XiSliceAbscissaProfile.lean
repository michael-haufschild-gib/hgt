import GaloisForLFunctions.RHTower.XiSliceHeatTransferPositivity
import GaloisForLFunctions.RHTower.ZeroFreeRegionFromFour
import GaloisForLFunctions.RHTower.PrimeArchLogHeightDefectOrderTwentyThreeThresholdAdvance
import GaloisForLFunctions.RHTower.GaussianCentralGapZeroFreeRegionBudget

/-!
# The absolute-monotonicity abscissa of the slice, height by height

`XiHorizontalAbsMono x₀ t` says that every Taylor coefficient at `x₀` of the slice
`x ↦ ξ(½+x+it) ξ(½−x+it)` is nonnegative, so `σ ↦ |ξ(σ + it)|²` is absolutely monotone on
`σ ≥ ½ + x₀`.  The strip criterion gives `x₀ = ½` at every height unconditionally, and RH is
`x₀ = 0` at every height.

**Hyperbola criterion for `Ξ`** (`xiHorizontalAbsMono_of_hyperbola`).  If every zero `ρ = β + iγ`
satisfies `(β − ½)² ≤ (γ − t)² + x₀²`, the slice at height `t` is absolutely monotone from `x₀`.
Only zeros within horizontal distance `|β − ½|` of the height can obstruct.

**Height profile.**
* `xiHorizontalAbsMono_zero_free`: for `t ≥ 9/2` the slice is absolutely monotone from
  `½ − 1/(100 log(t + ½))`.  The zeros within height `½` of `t` lie in the zero-free region of
  width `1/(100 log γ)` (`xiZeroCopy_zero_free_from_four`) on both sides of the critical line, and
  all other zeros are harmless because `(β − ½)² < ¼`.
* `xiHorizontalAbsMono_zero_of_band`: for `(|t| + ½)² ≤ 431/2` (`|t| ≤ 14.18…`) the slice has
  nonnegative Taylor coefficients at the centre, since every zero below squared height `431/2` is
  on the critical line (`xiZeroCopy_re_eq_half_of_im_sq_lt_fourHundredThirtyOne_halves`).

* `exists_xiHorizontalAbsMono_vinogradovKorobov`: for all large `t` the slice is absolutely
  monotone from `½ − w(t + ½)`, `w(T) = (log T)^{−2/3}(log log T)^{−5/3}/10⁸`, the
  Vinogradov–Korobov width (`exists_xiZero_re_le_vinogradovKorobov`).

So the unconditional abscissa `x₀(t)` is `0` on the band and at most `½ − w(t + ½)` for large `t`;
RH is `x₀ ≡ 0`.
-/

open Complex
open RHTower.XiAtlasFinitePart

namespace RHTower.DeBruijn

noncomputable section

/-- **Hyperbola criterion for the slice of `Ξ`.** -/
theorem xiHorizontalAbsMono_of_hyperbola {t x₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (h : ∀ q : XiZeroCopy, ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ ((q.1 : ℂ).im - t) ^ 2 + x₀ ^ 2) :
    XiHorizontalAbsMono x₀ t := by
  obtain ⟨C, hC, hbound⟩ := (riemannKernel_superExp.mul_exp_sq (le_refl (0 : ℝ))).exists_envelope
  have hX : XiC = riemannHeat 0 := by
    funext z; rw [riemannHeat_zero, XiC, mul_comm I z]
  have hNT := nonnegTaylorAtZero_slice_shift_of_hyperbola hC (riemannHeat_analytic le_rfl)
    (riemannHeat_zero_ne le_rfl) (riemannHeat_neg le_rfl) (riemannHeat_conj le_rfl) hbound
    (t := t) hx₀ fun ζ hζ => by
      rw [← hX] at hζ
      obtain ⟨q, rfl⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy ζ).mp hζ
      rw [xiSpectralPoint_eq_re_im]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, Complex.add_im, Complex.mul_im,
        mul_one, zero_add, add_zero]
      have := h q
      nlinarith [this]
  intro n
  have hS : xiSliceProduct t = fun x => riemannHeat 0 ((t : ℂ) - I * x) *
      riemannHeat 0 ((t : ℂ) + I * x) := by
    funext x; rw [xiSliceProduct_eq_XiC, hX]
  have hd := congrFun (iteratedDeriv_comp_const_add n
    (fun x => riemannHeat 0 ((t : ℂ) - I * x) * riemannHeat 0 ((t : ℂ) + I * x)) (x₀ : ℂ)) 0
  simp only [add_zero] at hd
  rw [hS, ← hd]
  exact hNT.2 n

/-- **Absolute monotonicity from the zero-free region.**  For `t ≥ 9/2` the slice at height `t`
is absolutely monotone from `½ − 1/(100 log(t + ½))`. -/
theorem xiHorizontalAbsMono_zero_free {t : ℝ} (ht : 9 / 2 ≤ t) :
    XiHorizontalAbsMono (1 / 2 - 1 / 100 / Real.log (t + 1 / 2)) t := by
  have hlog5 : 1 < Real.log (t + 1 / 2) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  set x₀ := 1 / 2 - 1 / 100 / Real.log (t + 1 / 2) with hx₀def
  have hsmall : 1 / 100 / Real.log (t + 1 / 2) < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  have hx₀ : 0 ≤ x₀ := by rw [hx₀def]; linarith
  refine xiHorizontalAbsMono_of_hyperbola hx₀ fun q => ?_
  set β := (q.1 : ℂ).re with hβ
  set γ := (q.1 : ℂ).im with hγ
  have hquarter : (β - 1 / 2) ^ 2 < 1 / 4 := by
    have := xi_divisor_support_centered_re_sq_lt_quarter q.1
    simpa [hβ] using this
  by_cases hfar : 1 / 2 ≤ |γ - t|
  · have : (1 / 2 : ℝ) ^ 2 ≤ (γ - t) ^ 2 := by
      rw [← sq_abs (γ - t)]; exact pow_le_pow_left₀ (by norm_num) hfar 2
    nlinarith [sq_nonneg x₀]
  · have hnear : |γ - t| < 1 / 2 := lt_of_not_ge hfar
    have hγ4 : 4 ≤ γ := by
      have := (abs_lt.mp hnear).1; linarith
    have hγt : γ < t + 1 / 2 := by have := (abs_lt.mp hnear).2; linarith
    have hup := xiZeroCopy_zero_free_from_four (q := q) hγ4
    have hpart : 4 ≤ ((lagPartner q).1 : ℂ).im := by
      rw [lagPartner_coe]; simpa [hγ] using hγ4
    have hlow := xiZeroCopy_zero_free_from_four (q := lagPartner q) hpart
    rw [lagPartner_coe] at hlow
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.sub_im, Complex.one_im,
      Complex.conj_im, zero_sub, neg_neg] at hlow
    rw [← hβ, ← hγ] at hup
    rw [← hβ, ← hγ] at hlow
    have hlogγ : 0 < Real.log γ := Real.log_pos (by linarith)
    have hlogle : Real.log γ ≤ Real.log (t + 1 / 2) := Real.log_le_log (by linarith) hγt.le
    have hcmp : 1 / 100 / Real.log (t + 1 / 2) ≤ 1 / 100 / Real.log γ :=
      div_le_div_of_nonneg_left (by norm_num) hlogγ hlogle
    have habs : |β - 1 / 2| ≤ x₀ := by
      rw [abs_le, hx₀def]; constructor <;> linarith
    have : (β - 1 / 2) ^ 2 ≤ x₀ ^ 2 := by
      rw [← sq_abs (β - 1 / 2)]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    nlinarith [sq_nonneg (γ - t)]

/-- **Centre positivity on the critical-line band.**  For `(|t| + ½)² ≤ 431/2` every Taylor
coefficient of the slice at height `t` is nonnegative. -/
theorem xiHorizontalAbsMono_zero_of_band {t : ℝ} (ht : (|t| + 1 / 2) ^ 2 ≤ 431 / 2) :
    XiHorizontalAbsMono 0 t := by
  refine xiHorizontalAbsMono_of_hyperbola le_rfl fun q => ?_
  set β := (q.1 : ℂ).re with hβ
  set γ := (q.1 : ℂ).im with hγ
  have hquarter : (β - 1 / 2) ^ 2 < 1 / 4 := by
    have := xi_divisor_support_centered_re_sq_lt_quarter q.1
    simpa [hβ] using this
  by_cases hfar : 1 / 2 ≤ |γ - t|
  · have : (1 / 2 : ℝ) ^ 2 ≤ (γ - t) ^ 2 := by
      rw [← sq_abs (γ - t)]; exact pow_le_pow_left₀ (by norm_num) hfar 2
    nlinarith
  · have hnear : |γ - t| < 1 / 2 := lt_of_not_ge hfar
    have hγabs : |γ| < |t| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub γ t
      linarith
    have hγsq : γ ^ (2 : ℕ) < 431 / 2 := by
      have h1 : |γ| ^ 2 < (|t| + 1 / 2) ^ 2 :=
        pow_lt_pow_left₀ hγabs (abs_nonneg _) two_ne_zero
      rw [sq_abs] at h1
      linarith
    have hline := xiZeroCopy_re_eq_half_of_im_sq_lt_fourHundredThirtyOne_halves q hγsq
    rw [← hβ] at hline
    rw [hline]
    nlinarith [sq_nonneg (γ - t)]

/-- **Absolute monotonicity from the Vinogradov–Korobov region.**  There is `T₀` such that for
every `t ≥ T₀` the slice at height `t` is absolutely monotone from `½ − w(t + ½)`, where
`w(T) = (log T)^{−2/3} (log log T)^{−5/3}/10⁸` is the Vinogradov–Korobov width. -/
theorem exists_xiHorizontalAbsMono_vinogradovKorobov :
    ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t →
      XiHorizontalAbsMono (1 / 2 - vinogradovKorobovGaussianWidth (t + 1 / 2)) t := by
  obtain ⟨t₀, ht₀2, ht₀e, hvk⟩ := exists_xiZero_re_le_vinogradovKorobov
  refine ⟨t₀ + 1 / 2, fun t ht => ?_⟩
  set w := vinogradovKorobovGaussianWidth (t + 1 / 2) with hw
  have hT : Real.exp (Real.exp 1) ≤ t + 1 / 2 := by linarith
  have hpos : 0 < t + 1 / 2 := lt_of_lt_of_le (Real.exp_pos _) hT
  have hl : Real.exp 1 ≤ Real.log (t + 1 / 2) := (Real.le_log_iff_exp_le hpos).mpr hT
  have hl1 : 1 ≤ Real.log (t + 1 / 2) := le_trans (Real.one_le_exp (by norm_num)) hl
  have hll : 1 ≤ Real.log (Real.log (t + 1 / 2)) :=
    (Real.le_log_iff_exp_le (by linarith)).mpr hl
  have hw0 : 0 ≤ w := by
    rw [hw]; unfold vinogradovKorobovGaussianWidth
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (by linarith) _)) (by norm_num)
  have hw1 : w ≤ 1 / 2 := by
    have ha : Real.log (t + 1 / 2) ^ (-(2 : ℝ) / 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hl1 (by norm_num)
    have hb : Real.log (Real.log (t + 1 / 2)) ^ (-(5 : ℝ) / 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hll (by norm_num)
    have ha0 : 0 ≤ Real.log (t + 1 / 2) ^ (-(2 : ℝ) / 3) := by positivity
    rw [hw]; unfold vinogradovKorobovGaussianWidth
    rw [div_le_iff₀ (by norm_num)]
    nlinarith [mul_le_one₀ ha (by positivity) hb]
  refine xiHorizontalAbsMono_of_hyperbola (by linarith) fun q => ?_
  set β := (q.1 : ℂ).re with hβ
  set γ := (q.1 : ℂ).im with hγ
  have hquarter : (β - 1 / 2) ^ 2 < 1 / 4 := by
    have := xi_divisor_support_centered_re_sq_lt_quarter q.1
    simpa [hβ] using this
  by_cases hfar : 1 / 2 ≤ |γ - t|
  · have : (1 / 2 : ℝ) ^ 2 ≤ (γ - t) ^ 2 := by
      rw [← sq_abs (γ - t)]; exact pow_le_pow_left₀ (by norm_num) hfar 2
    nlinarith [sq_nonneg (1 / 2 - w)]
  · have hnear : |γ - t| < 1 / 2 := lt_of_not_ge hfar
    have hγ0 : t₀ ≤ γ := by have := (abs_lt.mp hnear).1; linarith
    have hγt : γ < t + 1 / 2 := by have := (abs_lt.mp hnear).2; linarith
    have hγabs : |γ| = γ := abs_of_nonneg (by linarith)
    have hup := hvk q (by simp only [xiZero, ← hγ, hγabs]; exact hγ0)
    have hpart := hvk (lagPartner q) (by
      simp only [xiZero, lagPartner_coe, Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub,
        neg_neg, ← hγ, hγabs]; exact hγ0)
    simp only [xiZero, ← hβ, ← hγ, hγabs] at hup
    simp only [xiZero, lagPartner_coe, Complex.sub_re, Complex.one_re, Complex.conj_re,
      Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg, ← hβ, ← hγ,
      hγabs] at hpart
    have hanti := vinogradovKorobovGaussianWidth_anti (le_trans ht₀e hγ0) hγt.le
    rw [← hw] at hanti
    have habs : |β - 1 / 2| ≤ 1 / 2 - w := by
      rw [abs_le]; constructor <;> linarith
    have : (β - 1 / 2) ^ 2 ≤ (1 / 2 - w) ^ 2 := by
      rw [← sq_abs (β - 1 / 2)]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    nlinarith [sq_nonneg (γ - t)]

end

end RHTower.DeBruijn
