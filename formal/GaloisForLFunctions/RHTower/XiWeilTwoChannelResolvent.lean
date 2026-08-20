import GaloisForLFunctions.RHTower.XiEulerSafeCauchyLoss
import GaloisForLFunctions.RHTower.XiWeilResolventGram
import GaloisForLFunctions.RHTower.XiThetaEigenGramLaw
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv

/-!
# The critical logarithmic-derivative kernel is a two-channel Weil resolvent Gram

In centred coordinates `X(W) = ξ(1/2 + W)`, `L = X'/X`, and with `α` running over the
multiplicity-exact centred Xi divisor, the two canonical resolvent channels are

```
A_w (z) = w / (w ^ 2 + z ^ 2),      B_w (z) = z / (w ^ 2 + z ^ 2),
```

equivalently the two Hardy orientations `R_w^± (z) = 1 / (w ∓ i z)`.  The paired Hadamard
logarithmic derivative is `L w = ∑' α, A_w α`, and a one-line partial-fraction identity turns the
critical Carathéodory kernel into the sum of the two polarized Weil Gram kernels

```
(L w + conj (L v)) / (w + conj v) = q_W (A_w, A_v) + q_W (B_w, B_v)
                                  = (q_W (R_w^+, R_v^+) + q_W (R_w^-, R_v^-)) / 2 .
```

Combined with the Carathéodory criterion this makes the diagonal two-channel span a complete Weil
detector: its positivity on the Euler half plane is exactly the Riemann hypothesis.
-/

noncomputable section

open Complex
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate ComplexOrder

namespace RHTower

/-! ### The centred divisor lies in a horizontal strip -/

theorem abs_im_xiSpectralPoint_le (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
  have h := abs_xiZero_re_sub_half_le_of_halfPlaneBound xiZeroHalfPlaneBound_half q
  rw [xiSpectralPoint_im_eq, abs_sub_comm]
  exact h

theorem sub_I_mul_spectral_ne_zero {W : ℂ} (hW : 1 / 2 < W.re) (q : XiZeroCopy) :
    W - Complex.I * xiSpectralPoint q ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, sub_neg_eq_add, Complex.zero_re] at hre
  have hb := abs_le.mp (abs_im_xiSpectralPoint_le q)
  linarith [hb.2]

theorem add_I_mul_spectral_ne_zero {W : ℂ} (hW : 1 / 2 < W.re) (q : XiZeroCopy) :
    W + Complex.I * xiSpectralPoint q ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, Complex.zero_re] at hre
  have hb := abs_le.mp (abs_im_xiSpectralPoint_le q)
  linarith [hb.1]

theorem sq_add_spectral_sq_ne_zero {W : ℂ} (hW : 1 / 2 < W.re) (q : XiZeroCopy) :
    W ^ 2 + (xiSpectralPoint q) ^ 2 ≠ 0 := by
  have hfac : W ^ 2 + (xiSpectralPoint q) ^ 2
      = (W - Complex.I * xiSpectralPoint q) * (W + Complex.I * xiSpectralPoint q) := by
    have h := Complex.I_mul_I
    linear_combination (xiSpectralPoint q ^ 2) * h
  rw [hfac]
  exact mul_ne_zero (sub_I_mul_spectral_ne_zero hW q) (add_I_mul_spectral_ne_zero hW q)

/-! ### The two canonical channels -/

/-- The even resolvent channel `A_w`. -/
def weilChannelA (w z : ℂ) : ℂ := w / (w ^ 2 + z ^ 2)

/-- The odd resolvent channel `B_w`. -/
def weilChannelB (w z : ℂ) : ℂ := z / (w ^ 2 + z ^ 2)

/-- The forward Hardy resolvent orientation. -/
def weilResolventPlus (w z : ℂ) : ℂ := 1 / (w - Complex.I * z)

/-- The backward Hardy resolvent orientation. -/
def weilResolventMinus (w z : ℂ) : ℂ := 1 / (w + Complex.I * z)

theorem weilChannelA_eq_resolvent {w z : ℂ} (hz : w ^ 2 + z ^ 2 ≠ 0) :
    weilChannelA w z = (weilResolventPlus w z + weilResolventMinus w z) / 2 := by
  have hfac : w ^ 2 + z ^ 2 = (w - Complex.I * z) * (w + Complex.I * z) := by
    have h := Complex.I_mul_I
    linear_combination (z ^ 2) * h
  have h1 : w - Complex.I * z ≠ 0 := by
    intro h
    apply hz
    rw [hfac, h, zero_mul]
  have h2 : w + Complex.I * z ≠ 0 := by
    intro h
    apply hz
    rw [hfac, h, mul_zero]
  rw [weilChannelA, weilResolventPlus, weilResolventMinus, hfac]
  field_simp
  ring

theorem weilChannelB_eq_resolvent {w z : ℂ} (hz : w ^ 2 + z ^ 2 ≠ 0) :
    weilChannelB w z
      = (weilResolventPlus w z - weilResolventMinus w z) / (2 * Complex.I) := by
  have hfac : w ^ 2 + z ^ 2 = (w - Complex.I * z) * (w + Complex.I * z) := by
    have h := Complex.I_mul_I
    linear_combination (z ^ 2) * h
  have h1 : w - Complex.I * z ≠ 0 := by
    intro h
    apply hz
    rw [hfac, h, zero_mul]
  have h2 : w + Complex.I * z ≠ 0 := by
    intro h
    apply hz
    rw [hfac, h, mul_zero]
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  have key : (1 : ℂ) / (w - Complex.I * z) - 1 / (w + Complex.I * z)
      = (2 * Complex.I * z) / ((w - Complex.I * z) * (w + Complex.I * z)) := by
    field_simp
    ring
  rw [weilChannelB, weilResolventPlus, weilResolventMinus, hfac, key, div_div]
  have hD : (w - Complex.I * z) * (w + Complex.I * z) ≠ 0 := mul_ne_zero h1 h2
  field_simp

/-! ### The sharp involution acts by conjugating the parameter -/

theorem xiWeilSharp_channelA (v : ℂ) :
    xiWeilSharp (weilChannelA v) = weilChannelA (conj v) := by
  funext z
  simp only [xiWeilSharp, weilChannelA, map_div₀, map_add, map_pow, Complex.conj_conj]

theorem xiWeilSharp_channelB (v : ℂ) :
    xiWeilSharp (weilChannelB v) = weilChannelB (conj v) := by
  funext z
  simp only [xiWeilSharp, weilChannelB, map_div₀, map_add, map_pow, Complex.conj_conj]

theorem xiWeilSharp_resolventPlus (v : ℂ) :
    xiWeilSharp (weilResolventPlus v) = weilResolventMinus (conj v) := by
  funext z
  simp only [xiWeilSharp, weilResolventPlus, weilResolventMinus, map_div₀, map_one, map_sub,
    map_mul, Complex.conj_I, Complex.conj_conj, neg_mul, sub_neg_eq_add]

theorem xiWeilSharp_resolventMinus (v : ℂ) :
    xiWeilSharp (weilResolventMinus v) = weilResolventPlus (conj v) := by
  funext z
  simp only [xiWeilSharp, weilResolventMinus, weilResolventPlus, map_div₀, map_one, map_add,
    map_mul, Complex.conj_I, Complex.conj_conj, neg_mul, ← sub_eq_add_neg]

/-! ### The paired Hadamard logarithmic derivative -/

theorem weilChannelA_factored (w z : ℂ) :
    weilChannelA w z = w / ((w - Complex.I * z) * (w + Complex.I * z)) := by
  rw [weilChannelA]
  congr 1
  linear_combination (z ^ 2) * Complex.I_mul_I

theorem xiCent_ne_zero_spectral {W : ℂ} (hW : 1 / 2 < W.re) : XiC (-Complex.I * W) ≠ 0 := by
  rw [← xiCent_eq_XiC]
  exact xiCent_ne_zero_of_half_lt_re hW

theorem relativeResolventTerm_pair {W : ℂ} (hW : 1 / 2 < W.re) (q : XiZeroCopy) :
    xiRelativeResolventTerm (-Complex.I * W) q
      + xiRelativeResolventTerm (-Complex.I * W) (xiZeroCopyReflectEquiv q)
      = 2 * Complex.I * weilChannelA W (xiSpectralPoint q) := by
  have hne := xiSpectralPoint_ne_zero q
  have hP : W - Complex.I * xiSpectralPoint q ≠ 0 := sub_I_mul_spectral_ne_zero hW q
  have hQ : W + Complex.I * xiSpectralPoint q ≠ 0 := add_I_mul_spectral_ne_zero hW q
  have e1 : xiSpectralPoint q - -Complex.I * W
      = Complex.I * (W - Complex.I * xiSpectralPoint q) := by
    linear_combination (xiSpectralPoint q) * Complex.I_mul_I
  have e2 : -xiSpectralPoint q - -Complex.I * W
      = Complex.I * (W + Complex.I * xiSpectralPoint q) := by
    linear_combination (-(xiSpectralPoint q)) * Complex.I_mul_I
  have key : (Complex.I * (W - Complex.I * xiSpectralPoint q))⁻¹
      + (Complex.I * (W + Complex.I * xiSpectralPoint q))⁻¹
      = -(2 * Complex.I * (W / ((W - Complex.I * xiSpectralPoint q)
          * (W + Complex.I * xiSpectralPoint q)))) := by
    rw [mul_inv, mul_inv, Complex.inv_I]
    field_simp
    ring
  simp only [xiRelativeResolventTerm, xiSpectralPoint_reflect, e1, e2, weilChannelA_factored,
    inv_neg]
  linear_combination -key

theorem summable_channelA {W : ℂ} (hW : 1 / 2 < W.re) :
    Summable (fun q : XiZeroCopy => weilChannelA W (xiSpectralPoint q)) := by
  have hXi := xiCent_ne_zero_spectral hW
  have hsum := summable_xiRelativeResolventTerm hXi
  have hsum' : Summable (fun q : XiZeroCopy =>
      xiRelativeResolventTerm (-Complex.I * W) (xiZeroCopyReflectEquiv q)) :=
    xiZeroCopyReflectEquiv.summable_iff.mpr hsum
  have hI2 : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  refine ((hsum.add hsum').div_const (2 * Complex.I)).congr fun q => ?_
  rw [relativeResolventTerm_pair hW q]
  field_simp

/-- **Equation (11).**  The paired Hadamard logarithmic derivative is the divisor sum of the even
channel. -/
theorem logDeriv_xiCent_eq_tsum_channelA {W : ℂ} (hW : 1 / 2 < W.re) :
    logDeriv xiCent W = ∑' q : XiZeroCopy, weilChannelA W (xiSpectralPoint q) := by
  have hXi := xiCent_ne_zero_spectral hW
  have hsum := summable_xiRelativeResolventTerm hXi
  have hsum' : Summable (fun q : XiZeroCopy =>
      xiRelativeResolventTerm (-Complex.I * W) (xiZeroCopyReflectEquiv q)) :=
    xiZeroCopyReflectEquiv.summable_iff.mpr hsum
  have hrefl : (∑' q : XiZeroCopy,
      xiRelativeResolventTerm (-Complex.I * W) (xiZeroCopyReflectEquiv q))
      = ∑' q : XiZeroCopy, xiRelativeResolventTerm (-Complex.I * W) q :=
    xiZeroCopyReflectEquiv.tsum_eq _
  have hpair : (∑' q : XiZeroCopy, (xiRelativeResolventTerm (-Complex.I * W) q
        + xiRelativeResolventTerm (-Complex.I * W) (xiZeroCopyReflectEquiv q)))
      = 2 * xiRelativeResolventTrace (-Complex.I * W) := by
    rw [Summable.tsum_add hsum hsum', hrefl, xiRelativeResolventTrace]
    ring
  have hchan : (∑' q : XiZeroCopy, (xiRelativeResolventTerm (-Complex.I * W) q
        + xiRelativeResolventTerm (-Complex.I * W) (xiZeroCopyReflectEquiv q)))
      = 2 * Complex.I * ∑' q : XiZeroCopy, weilChannelA W (xiSpectralPoint q) := by
    rw [tsum_congr (relativeResolventTerm_pair hW), tsum_mul_left]
  have h2 : (2 : ℂ) * xiRelativeResolventTrace (-Complex.I * W)
      = 2 * (Complex.I * ∑' q : XiZeroCopy, weilChannelA W (xiSpectralPoint q)) := by
    rw [← hpair, hchan]
    ring
  have hT := mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) h2
  rw [logDeriv_xiCent_eq W, logDeriv_XiC_eq_relativeResolventTrace hXi, hT]
  linear_combination (-(∑' q : XiZeroCopy, weilChannelA W (xiSpectralPoint q))) * Complex.I_mul_I

/-- The divisor sum of the even channel is Schwarz real. -/
theorem tsum_channelA_conj {v : ℂ} :
    ∑' q : XiZeroCopy, weilChannelA (conj v) (xiSpectralPoint q)
      = conj (∑' q : XiZeroCopy, weilChannelA v (xiSpectralPoint q)) := by
  rw [Complex.conj_tsum,
    ← xiZeroCopyLineConjEquiv.tsum_eq (fun q => weilChannelA (conj v) (xiSpectralPoint q))]
  refine tsum_congr fun q => ?_
  rw [xiSpectralPoint_lineConj]
  simp only [weilChannelA, map_div₀, map_add, map_pow]

theorem logDeriv_xiCent_conj {v : ℂ} (hv : 1 / 2 < v.re) :
    logDeriv xiCent (conj v) = conj (logDeriv xiCent v) := by
  have hcv : 1 / 2 < (conj v).re := by
    rwa [Complex.conj_re]
  rw [logDeriv_xiCent_eq_tsum_channelA hcv, logDeriv_xiCent_eq_tsum_channelA hv,
    tsum_channelA_conj]

/-! ### Summability of the channel products -/

theorem eventually_norm_spectral_ge (M : ℝ) :
    ∀ᶠ q in Filter.cofinite, M ≤ ‖xiSpectralPoint q‖ := by
  by_cases hM : M ≤ 0
  · exact Filter.Eventually.of_forall fun q => le_trans hM (norm_nonneg _)
  · rw [not_le] at hM
    have hbase : Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖ ^ 2) :=
      xiSpectralPoint_inv_sq_summable
    have hlt : ∀ᶠ q in Filter.cofinite, 1 / ‖xiSpectralPoint q‖ ^ 2 < 1 / M ^ 2 :=
      hbase.tendsto_cofinite_zero.eventually_lt_const (by positivity)
    filter_upwards [hlt] with q hq
    have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    have hsq : M ^ 2 < ‖xiSpectralPoint q‖ ^ 2 := lt_of_one_div_lt_one_div (pow_pos hpos 2) hq
    exact le_of_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq)

theorem norm_sub_I_mul_spectral_ge {w : ℂ} {q : XiZeroCopy}
    (h : 2 * ‖w‖ ≤ ‖xiSpectralPoint q‖) :
    ‖xiSpectralPoint q‖ / 2 ≤ ‖w - Complex.I * xiSpectralPoint q‖ := by
  have hIa : ‖Complex.I * xiSpectralPoint q‖ = ‖xiSpectralPoint q‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have hb := norm_sub_norm_le (Complex.I * xiSpectralPoint q) w
  rw [hIa] at hb
  rw [show w - Complex.I * xiSpectralPoint q = -(Complex.I * xiSpectralPoint q - w) by ring,
    norm_neg]
  linarith

theorem norm_add_I_mul_spectral_ge {w : ℂ} {q : XiZeroCopy}
    (h : 2 * ‖w‖ ≤ ‖xiSpectralPoint q‖) :
    ‖xiSpectralPoint q‖ / 2 ≤ ‖w + Complex.I * xiSpectralPoint q‖ := by
  have hIa : ‖Complex.I * xiSpectralPoint q‖ = ‖xiSpectralPoint q‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have hb := norm_sub_norm_le (Complex.I * xiSpectralPoint q) (-w)
  rw [hIa, norm_neg] at hb
  rw [show w + Complex.I * xiSpectralPoint q = Complex.I * xiSpectralPoint q - -w by ring]
  linarith

theorem norm_sq_add_spectral_sq_ge {w : ℂ} {q : XiZeroCopy}
    (h : 2 * ‖w‖ ≤ ‖xiSpectralPoint q‖) :
    ‖xiSpectralPoint q‖ ^ 2 / 4 ≤ ‖w ^ 2 + (xiSpectralPoint q) ^ 2‖ := by
  have hfac : w ^ 2 + (xiSpectralPoint q) ^ 2
      = (w - Complex.I * xiSpectralPoint q) * (w + Complex.I * xiSpectralPoint q) := by
    linear_combination ((xiSpectralPoint q) ^ 2) * Complex.I_mul_I
  have h1 := norm_sub_I_mul_spectral_ge h
  have h2 := norm_add_I_mul_spectral_ge h
  rw [hfac, norm_mul]
  nlinarith [norm_nonneg (xiSpectralPoint q), norm_nonneg (w - Complex.I * xiSpectralPoint q),
    norm_nonneg (w + Complex.I * xiSpectralPoint q)]

theorem norm_weilChannelA_le {w : ℂ} {q : XiZeroCopy} (h : 2 * ‖w‖ ≤ ‖xiSpectralPoint q‖) :
    ‖weilChannelA w (xiSpectralPoint q)‖ ≤ 4 * ‖w‖ / ‖xiSpectralPoint q‖ ^ 2 := by
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hden := norm_sq_add_spectral_sq_ge h
  have hdenpos : (0 : ℝ) < ‖xiSpectralPoint q‖ ^ 2 / 4 := by positivity
  rw [weilChannelA, norm_div, div_le_div_iff₀ (lt_of_lt_of_le hdenpos hden) (by positivity)]
  nlinarith [norm_nonneg w, hden, hpos]

theorem norm_weilChannelB_le {w : ℂ} {q : XiZeroCopy} (h : 2 * ‖w‖ ≤ ‖xiSpectralPoint q‖) :
    ‖weilChannelB w (xiSpectralPoint q)‖ ≤ 4 / ‖xiSpectralPoint q‖ := by
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hden := norm_sq_add_spectral_sq_ge h
  have hdenpos : (0 : ℝ) < ‖xiSpectralPoint q‖ ^ 2 / 4 := by positivity
  rw [weilChannelB, norm_div, div_le_div_iff₀ (lt_of_lt_of_le hdenpos hden) hpos]
  nlinarith [hden, hpos]

theorem norm_weilResolventPlus_le {w : ℂ} {q : XiZeroCopy} (h : 2 * ‖w‖ ≤ ‖xiSpectralPoint q‖) :
    ‖weilResolventPlus w (xiSpectralPoint q)‖ ≤ 2 / ‖xiSpectralPoint q‖ := by
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hden := norm_sub_I_mul_spectral_ge h
  have hdenpos : (0 : ℝ) < ‖xiSpectralPoint q‖ / 2 := by positivity
  rw [weilResolventPlus, norm_div, norm_one,
    div_le_div_iff₀ (lt_of_lt_of_le hdenpos hden) hpos]
  nlinarith [hden, hpos]

theorem norm_weilResolventMinus_le {w : ℂ} {q : XiZeroCopy} (h : 2 * ‖w‖ ≤ ‖xiSpectralPoint q‖) :
    ‖weilResolventMinus w (xiSpectralPoint q)‖ ≤ 2 / ‖xiSpectralPoint q‖ := by
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hden := norm_add_I_mul_spectral_ge h
  have hdenpos : (0 : ℝ) < ‖xiSpectralPoint q‖ / 2 := by positivity
  rw [weilResolventMinus, norm_div, norm_one,
    div_le_div_iff₀ (lt_of_lt_of_le hdenpos hden) hpos]
  nlinarith [hden, hpos]

theorem summable_channelA_mul (w u : ℂ) :
    Summable (fun q : XiZeroCopy =>
      weilChannelA w (xiSpectralPoint q) * weilChannelA u (xiSpectralPoint q)) := by
  have hbase : Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable
  refine (hbase.mul_left (16 * (‖w‖ * ‖u‖))).of_norm_bounded_eventually ?_
  filter_upwards [eventually_norm_spectral_ge (2 * ‖w‖), eventually_norm_spectral_ge (2 * ‖u‖),
    eventually_norm_spectral_ge 1] with q hw hu h1
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have b1 := norm_weilChannelA_le hw
  have b2 := norm_weilChannelA_le hu
  rw [norm_mul]
  have hprod : ‖weilChannelA w (xiSpectralPoint q)‖ * ‖weilChannelA u (xiSpectralPoint q)‖
      ≤ (4 * ‖w‖ / ‖xiSpectralPoint q‖ ^ 2) * (4 * ‖u‖ / ‖xiSpectralPoint q‖ ^ 2) :=
    mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
  refine hprod.trans ?_
  rw [div_mul_div_comm, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq1 : (1 : ℝ) ≤ ‖xiSpectralPoint q‖ ^ 2 := by nlinarith [h1, hpos]
  have ha2 : ‖xiSpectralPoint q‖ ^ 2 ≤ ‖xiSpectralPoint q‖ ^ 2 * ‖xiSpectralPoint q‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hsq1 (sq_nonneg ‖xiSpectralPoint q‖)
    linarith
  have hkey : 0 ≤ (‖w‖ * ‖u‖) *
      (‖xiSpectralPoint q‖ ^ 2 * ‖xiSpectralPoint q‖ ^ 2 - ‖xiSpectralPoint q‖ ^ 2) :=
    mul_nonneg (mul_nonneg (norm_nonneg w) (norm_nonneg u)) (by linarith)
  nlinarith [hkey]

theorem summable_channelB_mul (w u : ℂ) :
    Summable (fun q : XiZeroCopy =>
      weilChannelB w (xiSpectralPoint q) * weilChannelB u (xiSpectralPoint q)) := by
  have hbase : Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable
  refine (hbase.mul_left 16).of_norm_bounded_eventually ?_
  filter_upwards [eventually_norm_spectral_ge (2 * ‖w‖), eventually_norm_spectral_ge (2 * ‖u‖)]
    with q hw hu
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have b1 := norm_weilChannelB_le hw
  have b2 := norm_weilChannelB_le hu
  rw [norm_mul]
  have hprod : ‖weilChannelB w (xiSpectralPoint q)‖ * ‖weilChannelB u (xiSpectralPoint q)‖
      ≤ (4 / ‖xiSpectralPoint q‖) * (4 / ‖xiSpectralPoint q‖) :=
    mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
  refine hprod.trans ?_
  rw [div_mul_div_comm, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hpos]

theorem summable_resolvent_mul (w u : ℂ) :
    Summable (fun q : XiZeroCopy =>
      weilResolventPlus w (xiSpectralPoint q) * weilResolventMinus u (xiSpectralPoint q)) := by
  have hbase : Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable
  refine (hbase.mul_left 4).of_norm_bounded_eventually ?_
  filter_upwards [eventually_norm_spectral_ge (2 * ‖w‖), eventually_norm_spectral_ge (2 * ‖u‖)]
    with q hw hu
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have b1 := norm_weilResolventPlus_le hw
  have b2 := norm_weilResolventMinus_le hu
  rw [norm_mul]
  have hprod : ‖weilResolventPlus w (xiSpectralPoint q)‖
      * ‖weilResolventMinus u (xiSpectralPoint q)‖
      ≤ (2 / ‖xiSpectralPoint q‖) * (2 / ‖xiSpectralPoint q‖) :=
    mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
  refine hprod.trans ?_
  rw [div_mul_div_comm, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hpos]

theorem summable_resolvent_mul' (w u : ℂ) :
    Summable (fun q : XiZeroCopy =>
      weilResolventMinus w (xiSpectralPoint q) * weilResolventPlus u (xiSpectralPoint q)) := by
  have hbase : Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable
  refine (hbase.mul_left 4).of_norm_bounded_eventually ?_
  filter_upwards [eventually_norm_spectral_ge (2 * ‖w‖), eventually_norm_spectral_ge (2 * ‖u‖)]
    with q hw hu
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have b1 := norm_weilResolventMinus_le hw
  have b2 := norm_weilResolventPlus_le hu
  rw [norm_mul]
  have hprod : ‖weilResolventMinus w (xiSpectralPoint q)‖
      * ‖weilResolventPlus u (xiSpectralPoint q)‖
      ≤ (2 / ‖xiSpectralPoint q‖) * (2 / ‖xiSpectralPoint q‖) :=
    mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
  refine hprod.trans ?_
  rw [div_mul_div_comm, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hpos]

/-! ### Square summability of the channels on the divisor -/

theorem xiWeilSquareSummable_channelA (w : ℂ) : XiWeilSquareSummable (weilChannelA w) := by
  have hbase : Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable
  refine (hbase.mul_left (16 * ‖w‖ ^ 2)).of_norm_bounded_eventually ?_
  filter_upwards [eventually_norm_spectral_ge (2 * ‖w‖), eventually_norm_spectral_ge 1]
    with q hw h1
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have b1 := norm_weilChannelA_le hw
  have hsq1 : (1 : ℝ) ≤ ‖xiSpectralPoint q‖ ^ 2 := by nlinarith [h1, hpos]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hstep : ‖weilChannelA w (xiSpectralPoint q)‖ ^ 2
      ≤ (4 * ‖w‖ / ‖xiSpectralPoint q‖ ^ 2) ^ 2 := by
    have := norm_nonneg (weilChannelA w (xiSpectralPoint q))
    nlinarith [b1]
  refine hstep.trans ?_
  rw [div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : 0 ≤ ‖w‖ ^ 2 *
      (‖xiSpectralPoint q‖ ^ 2 * (‖xiSpectralPoint q‖ ^ 2) ^ 2
        - ‖xiSpectralPoint q‖ ^ 2 * ‖xiSpectralPoint q‖ ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hsq1
      (by positivity : (0 : ℝ) ≤ ‖xiSpectralPoint q‖ ^ 2 * ‖xiSpectralPoint q‖ ^ 2)
    nlinarith [sq_nonneg ‖w‖]
  nlinarith [hkey]

theorem xiWeilSquareSummable_channelB (w : ℂ) : XiWeilSquareSummable (weilChannelB w) := by
  have hbase : Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable
  refine (hbase.mul_left 16).of_norm_bounded_eventually ?_
  filter_upwards [eventually_norm_spectral_ge (2 * ‖w‖)] with q hw
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have b1 := norm_weilChannelB_le hw
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hstep : ‖weilChannelB w (xiSpectralPoint q)‖ ^ 2 ≤ (4 / ‖xiSpectralPoint q‖) ^ 2 := by
    have := norm_nonneg (weilChannelB w (xiSpectralPoint q))
    nlinarith [b1]
  refine hstep.trans ?_
  rw [div_pow, mul_one_div]
  norm_num

/-! ### Equations (8) and (9): the exact resolvent--Weil identity -/

theorem channel_pair_pointwise {w u z : ℂ} (hw : w ^ 2 + z ^ 2 ≠ 0) (hu : u ^ 2 + z ^ 2 ≠ 0)
    (hwu : w + u ≠ 0) :
    weilChannelA w z * weilChannelA u z + weilChannelB w z * weilChannelB u z
      = (weilChannelA w z + weilChannelA u z) / (w + u) := by
  simp only [weilChannelA, weilChannelB]
  field_simp
  ring

/-- **Equation (8).**  The critical Carathéodory kernel is the sum of the two polarized Weil Gram
kernels on the canonical resolvent channels. -/
theorem criticalLogDerivKernel_eq_twoChannel {w v : ℂ} (hw : 1 / 2 < w.re) (hv : 1 / 2 < v.re) :
    criticalLogDerivKernel w v
      = xiWeilPolarization (weilChannelA w) (weilChannelA v)
        + xiWeilPolarization (weilChannelB w) (weilChannelB v) := by
  have hcv : 1 / 2 < (conj v).re := by
    rwa [Complex.conj_re]
  have hwu : w + conj v ≠ 0 := add_conj_ne_zero (by linarith) (by linarith)
  have hA := summable_channelA_mul w (conj v)
  have hB := summable_channelB_mul w (conj v)
  have hsw := summable_channelA hw
  have hsu := summable_channelA hcv
  simp only [xiWeilPolarization, xiWeilSharp_channelA, xiWeilSharp_channelB]
  rw [← Summable.tsum_add hA hB,
    tsum_congr (fun q => channel_pair_pointwise (sq_add_spectral_sq_ne_zero hw q)
      (sq_add_spectral_sq_ne_zero hcv q) hwu),
    tsum_div_const, Summable.tsum_add hsw hsu,
    ← logDeriv_xiCent_eq_tsum_channelA hw, ← logDeriv_xiCent_eq_tsum_channelA hcv,
    logDeriv_xiCent_conj hv, criticalLogDerivKernel]

theorem resolvent_pair_pointwise {w u z : ℂ} (hw : w ^ 2 + z ^ 2 ≠ 0) (hu : u ^ 2 + z ^ 2 ≠ 0) :
    weilResolventPlus w z * weilResolventMinus u z
        + weilResolventMinus w z * weilResolventPlus u z
      = 2 * (weilChannelA w z * weilChannelA u z + weilChannelB w z * weilChannelB u z) := by
  have hfw : w ^ 2 + z ^ 2 = (w - Complex.I * z) * (w + Complex.I * z) := by
    linear_combination (z ^ 2) * Complex.I_mul_I
  have hfu : u ^ 2 + z ^ 2 = (u - Complex.I * z) * (u + Complex.I * z) := by
    linear_combination (z ^ 2) * Complex.I_mul_I
  have hw1 : w - Complex.I * z ≠ 0 := by
    intro h; apply hw; rw [hfw, h, zero_mul]
  have hw2 : w + Complex.I * z ≠ 0 := by
    intro h; apply hw; rw [hfw, h, mul_zero]
  have hu1 : u - Complex.I * z ≠ 0 := by
    intro h; apply hu; rw [hfu, h, zero_mul]
  have hu2 : u + Complex.I * z ≠ 0 := by
    intro h; apply hu; rw [hfu, h, mul_zero]
  simp only [weilResolventPlus, weilResolventMinus, weilChannelA, weilChannelB, hfw, hfu]
  field_simp
  linear_combination (-2 * z ^ 2) * Complex.I_mul_I

/-- **Equation (9).**  The same kernel is the mean of the two Hardy orientation Gram kernels. -/
theorem criticalLogDerivKernel_eq_resolventChannels {w v : ℂ} (hw : 1 / 2 < w.re)
    (hv : 1 / 2 < v.re) :
    criticalLogDerivKernel w v
      = (xiWeilPolarization (weilResolventPlus w) (weilResolventPlus v)
          + xiWeilPolarization (weilResolventMinus w) (weilResolventMinus v)) / 2 := by
  have hcv : 1 / 2 < (conj v).re := by
    rwa [Complex.conj_re]
  have hR1 := summable_resolvent_mul w (conj v)
  have hR2 := summable_resolvent_mul' w (conj v)
  have hA := summable_channelA_mul w (conj v)
  have hB := summable_channelB_mul w (conj v)
  simp only [xiWeilPolarization, xiWeilSharp_resolventPlus, xiWeilSharp_resolventMinus]
  rw [← Summable.tsum_add hR1 hR2,
    tsum_congr (fun q => resolvent_pair_pointwise (sq_add_spectral_sq_ne_zero hw q)
      (sq_add_spectral_sq_ne_zero hcv q)),
    tsum_mul_left, Summable.tsum_add hA hB]
  have hid := criticalLogDerivKernel_eq_twoChannel hw hv
  simp only [xiWeilPolarization, xiWeilSharp_channelA, xiWeilSharp_channelB] at hid
  rw [← hid]
  ring

/-! ### Equations (16)-(17): the two-channel family is a complete Weil detector -/

theorem criticalLogDerivKernel_conj_symm (x y : ℂ) :
    conj (criticalLogDerivKernel x y) = criticalLogDerivKernel y x := by
  rw [criticalLogDerivKernel, criticalLogDerivKernel, map_div₀, map_add, map_add,
    Complex.conj_conj, Complex.conj_conj]
  ring

/-- The two-channel Weil Gram kernel on the Euler half plane. -/
def twoChannelKernel (x y : {W : ℂ // 1 / 2 < W.re}) : ℂ :=
  xiWeilPolarization (weilChannelA (x : ℂ)) (weilChannelA (y : ℂ))
    + xiWeilPolarization (weilChannelB (x : ℂ)) (weilChannelB (y : ℂ))

theorem twoChannelKernel_eq (x y : {W : ℂ // 1 / 2 < W.re}) :
    twoChannelKernel x y = criticalLogDerivKernel (x : ℂ) (y : ℂ) :=
  (criticalLogDerivKernel_eq_twoChannel x.2 y.2).symm

theorem twoChannelKernel_conj_symm (x y : {W : ℂ // 1 / 2 < W.re}) :
    conj (twoChannelKernel x y) = twoChannelKernel y x := by
  rw [twoChannelKernel_eq, twoChannelKernel_eq, criticalLogDerivKernel_conj_symm]

/-- **Equation (17).**  Positivity of the two-channel Gram kernel on the Euler half plane is the
Riemann hypothesis. -/
theorem riemannHypothesis_iff_isPSDKernel_twoChannel :
    RiemannHypothesis ↔ IsPSDKernel twoChannelKernel := by
  rw [riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel (le_refl (1 / 2 : ℝ))]
  exact ⟨fun h => h.congr fun x y => (twoChannelKernel_eq x y).symm,
    fun h => h.congr fun x y => twoChannelKernel_eq x y⟩

/-! ### Equations (15)-(16): the finite channel packets -/

/-- The even channel packet `A_c` of a finite node/coefficient system. -/
def channelPacketA {n : ℕ} (c : Fin n → ℂ) (w : Fin n → {W : ℂ // 1 / 2 < W.re}) : ℂ → ℂ :=
  fun z => ∑ j, c j * weilChannelA ((w j : ℂ)) z

/-- The odd channel packet `B_c` of a finite node/coefficient system. -/
def channelPacketB {n : ℕ} (c : Fin n → ℂ) (w : Fin n → {W : ℂ // 1 / 2 < W.re}) : ℂ → ℂ :=
  fun z => ∑ j, c j * weilChannelB ((w j : ℂ)) z

theorem xiWeilPolarization_channelPacketA {n : ℕ} (c d : Fin n → ℂ)
    (w : Fin n → {W : ℂ // 1 / 2 < W.re}) :
    xiWeilPolarization (channelPacketA c w) (channelPacketA d w)
      = ∑ j, ∑ k, c j * conj (d k)
          * xiWeilPolarization (weilChannelA ((w j : ℂ))) (weilChannelA ((w k : ℂ))) := by
  have hsum : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      XiWeilSquareSummable (weilChannelA ((w j : ℂ))) :=
    fun j _ => xiWeilSquareSummable_channelA _
  unfold channelPacketA
  rw [xiWeilPolarization_finsetSum_left hsum c (XiWeilSquareSummable.finsetSum hsum d)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [xiWeilPolarization_finsetSum_right hsum d (hsum j (Finset.mem_univ j)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem xiWeilPolarization_channelPacketB {n : ℕ} (c d : Fin n → ℂ)
    (w : Fin n → {W : ℂ // 1 / 2 < W.re}) :
    xiWeilPolarization (channelPacketB c w) (channelPacketB d w)
      = ∑ j, ∑ k, c j * conj (d k)
          * xiWeilPolarization (weilChannelB ((w j : ℂ))) (weilChannelB ((w k : ℂ))) := by
  have hsum : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      XiWeilSquareSummable (weilChannelB ((w j : ℂ))) :=
    fun j _ => xiWeilSquareSummable_channelB _
  unfold channelPacketB
  rw [xiWeilPolarization_finsetSum_left hsum c (XiWeilSquareSummable.finsetSum hsum d)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [xiWeilPolarization_finsetSum_right hsum d (hsum j (Finset.mem_univ j)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Equation (15).**  The two-channel packet energy is the Gram energy of the two-channel
kernel. -/
theorem twoChannel_packet_eq_kernelEnergy {n : ℕ} (c : Fin n → ℂ)
    (w : Fin n → {W : ℂ // 1 / 2 < W.re}) :
    xiWeilPolarization (channelPacketA c w) (channelPacketA c w)
        + xiWeilPolarization (channelPacketB c w) (channelPacketB c w)
      = kernelEnergy twoChannelKernel (fun j => conj (c j)) w := by
  rw [xiWeilPolarization_channelPacketA, xiWeilPolarization_channelPacketB, kernelEnergy,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [twoChannelKernel, Complex.conj_conj]
  ring

/-- **The complete-detector theorem `(16)`.**  The Riemann hypothesis is exactly the nonnegativity
of the two-channel Weil energy of every finite node/coefficient system on the Euler half plane. -/
theorem riemannHypothesis_iff_twoChannel_packet_nonneg :
    RiemannHypothesis ↔
      ∀ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → {W : ℂ // 1 / 2 < W.re}),
        0 ≤ (xiWeilPolarization (channelPacketA c w) (channelPacketA c w)
              + xiWeilPolarization (channelPacketB c w) (channelPacketB c w)).re := by
  have hherm : ∀ x y : {W : ℂ // 1 / 2 < W.re}, conj (twoChannelKernel x y) = twoChannelKernel y x :=
    twoChannelKernel_conj_symm
  constructor
  · intro hRH n c w
    rw [twoChannel_packet_eq_kernelEnergy]
    exact (isPSDKernel_iff_forall_energy_nonneg hherm).mp
      (riemannHypothesis_iff_isPSDKernel_twoChannel.mp hRH) n _ w
  · intro h
    refine riemannHypothesis_iff_isPSDKernel_twoChannel.mpr
      ((isPSDKernel_iff_forall_energy_nonneg hherm).mpr fun n c w => ?_)
    have hval := h n (fun j => conj (c j)) w
    rw [twoChannel_packet_eq_kernelEnergy] at hval
    simpa using hval

/-! ### Equation (19): the absolutely convergent Euler presentation -/

theorem logDeriv_xiCent_eq_shift (W : ℂ) : logDeriv xiCent W = logDeriv xi (1 / 2 + W) := by
  have hfun : xiCent = fun W : ℂ => xi (1 / 2 + W) := rfl
  rw [logDeriv_apply, logDeriv_apply, hfun, deriv_comp_const_add]

theorem one_lt_re_shift {W : ℂ} (hW : 1 / 2 < W.re) : 1 < ((1 : ℂ) / 2 + W).re := by
  have h : ((1 : ℂ) / 2).re = 1 / 2 := by
    rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]
  rw [Complex.add_re, h]
  linarith

/-- **Equation (19).**  On the Euler-safe half plane the centred logarithmic derivative is the
polar and archimedean head minus the absolutely convergent von Mangoldt series. -/
theorem logDeriv_xiCent_eq_eulerPresentation {W : ℂ} (hW : 1 / 2 < W.re) :
    logDeriv xiCent W
      = ((1 : ℂ) / 2 + W)⁻¹ + ((1 : ℂ) / 2 + W - 1)⁻¹ + logDeriv Complex.Gammaℝ ((1 : ℂ) / 2 + W)
        - LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((1 : ℂ) / 2 + W) := by
  have hs : 1 < ((1 : ℂ) / 2 + W).re := one_lt_re_shift hW
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hlogζ : logDeriv riemannZeta ((1 : ℂ) / 2 + W)
      = -LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((1 : ℂ) / 2 + W) := by
    rw [logDeriv_apply, hL]
    ring
  rw [logDeriv_xiCent_eq_shift, logDeriv_xi_split hs, hlogζ]
  ring

/-- The von Mangoldt series of the Euler presentation converges absolutely. -/
theorem lSeriesSummable_vonMangoldt_shift {W : ℂ} (hW : 1 / 2 < W.re) :
    LSeriesSummable (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((1 : ℂ) / 2 + W) :=
  ArithmeticFunction.LSeriesSummable_vonMangoldt (one_lt_re_shift hW)

/-- **Equation (20).**  Every entry of the two-channel Weil Gram is the Euler--Gamma logarithmic
derivative kernel. -/
theorem twoChannelKernel_eq_eulerKernel (x y : {W : ℂ // 1 / 2 < W.re}) :
    twoChannelKernel x y
      = (logDeriv xiCent (x : ℂ) + conj (logDeriv xiCent (y : ℂ)))
          / ((x : ℂ) + conj (y : ℂ)) := by
  rw [twoChannelKernel_eq, criticalLogDerivKernel]

end RHTower
