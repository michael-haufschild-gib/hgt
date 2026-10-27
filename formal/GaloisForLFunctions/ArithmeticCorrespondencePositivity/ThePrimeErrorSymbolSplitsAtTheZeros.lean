import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.RHTower.XiHadamardFinitePart
import GaloisForLFunctions.RHTower.ZetaNotchSmoothTest
import GaloisForLFunctions.RHTower.WeilLagFunction
import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance
import GaloisForLFunctions.RHTower.Reflection
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The prime-error symbol splits at the zeros

Under RH the symbol `F(s)/s = (−ζ′(s)/ζ(s) − ζ(s))/s` of the prime-error profile (P41) is, on
`Re s > ½`, a sum of simple poles at the zeros with square-summable residues plus an
archimedean remainder (`primeErrorSymbol_eq_zeroPart_add`):

`F(s)/s = Σ'_q (−1/ρ_q)/(s − ρ_q) + R(s)`,
`R(s) = (−C₀ + 1/s + 1/(s − 1) + Γℝ′/Γℝ(s) − ζ(s))/s`, `C₀ = Σ'_q 1/(2ρ_q(ρ_q − ½))`.

The proof combines the Hadamard partial fraction `ξ′/ξ(s) = Σ'_q ((ρ_q − ½)⁻¹ + (s − ρ_q)⁻¹)`
(`RHTower.logDeriv_xi_eq_partialFraction`), the factorization `ξ = ½ s(s − 1) Γℝ ζ`, and the
identity `((ρ − ½)⁻¹ + (s − ρ)⁻¹)/s = 1/(ρ(s − ρ)) + 1/(2ρ(ρ − ½)s)`.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open _root_.RHTower (XiZeroCopy xi)

/-- The constant `C₀ = Σ'_q 1/(2ρ_q(ρ_q − ½))` of the split. -/
def splitConstant : ℂ := ∑' q : XiZeroCopy, 1 / (2 * (q.1 : ℂ) * ((q.1 : ℂ) - 1 / 2))

/-- The zero part `Σ'_q (−1/ρ_q)/(s − ρ_q)`. -/
def zeroPart (s : ℂ) : ℂ := ∑' q : XiZeroCopy, -(1 / (q.1 : ℂ)) / (s - (q.1 : ℂ))

/-- The archimedean remainder `(−C₀ + 1/s + 1/(s − 1) + Γℝ′/Γℝ(s) − ζ(s))/s`. -/
def archRemainder (s : ℂ) : ℂ :=
  (-splitConstant + 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s - riemannZeta s) / s

/-- `ξ′/ξ = 1/s + 1/(s − 1) + Γℝ′/Γℝ + ζ′/ζ` wherever `Re s > 0`, `s ≠ 1`, `ζ(s) ≠ 0`. -/
theorem logDeriv_xi_eq_add {s : ℂ} (hre : 0 < s.re) (h1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    logDeriv xi s = s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  have h0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; exact lt_irrefl _ hre
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
  have hpoly_ne : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero
  have hopen : IsOpen {w : ℂ | w ≠ 0 ∧ w ≠ 1 ∧ 0 < w.re} :=
    isOpen_ne.inter (isOpen_ne.inter (isOpen_lt continuous_const Complex.continuous_re))
  have hev : xi =ᶠ[nhds s] fun w => w * (w - 1) / 2 * (Complex.Gammaℝ w * riemannZeta w) := by
    filter_upwards [hopen.mem_nhds ⟨h0, h1, hre⟩] with w hw
    exact _root_.RHTower.ZetaNotch.xi_eq_half_mul_gammaR_zeta hw.1 hw.2.1 hw.2.2
  have hlogcongr : logDeriv xi s =
      logDeriv (fun w => w * (w - 1) / 2 * (Complex.Gammaℝ w * riemannZeta w)) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hpolyd : HasDerivAt (fun w : ℂ => w * (w - 1) / 2) ((2 * s - 1) / 2) s := by
    have hbase : HasDerivAt (fun w : ℂ => w * (w - 1)) (1 * (s - 1) + s * 1) s :=
      (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const (1 : ℂ))
    rw [show (1 : ℂ) * (s - 1) + s * 1 = 2 * s - 1 by ring] at hbase
    exact hbase.div_const 2
  have hΓd : DifferentiableAt ℂ Complex.Gammaℝ s :=
    (_root_.RHTower.hasDerivAt_Gammaℝ_of_re_pos hre).differentiableAt
  have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta h1
  rw [hlogcongr,
    logDeriv_mul (f := fun w : ℂ => w * (w - 1) / 2)
      (g := fun w : ℂ => Complex.Gammaℝ w * riemannZeta w) s hpoly_ne
      (mul_ne_zero hΓ hζ) hpolyd.differentiableAt (hΓd.mul hζd),
    logDeriv_mul (f := Complex.Gammaℝ) (g := riemannZeta) s hΓ hζ hΓd hζd]
  have hpolylog : logDeriv (fun w : ℂ => w * (w - 1) / 2) s = s⁻¹ + (s - 1)⁻¹ := by
    rw [logDeriv_apply, hpolyd.deriv]
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr h1
    field_simp
    ring
  rw [hpolylog]
  ring

/-- Under RH, `ζ` has no zero on `Re s > ½`. -/
theorem riemannZeta_ne_zero_of_riemannHypothesis (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hs1 : s ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hz)
  have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    simp at hs
    linarith
  have := hRH s hz htriv hs1
  linarith

/-- Under RH, `ξ` has no zero on `Re s > ½`. -/
theorem xi_ne_zero_of_riemannHypothesis (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s ≠ 1) : xi s ≠ 0 := by
  have hre : 0 < s.re := by linarith
  have h0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; exact lt_irrefl _ hre
  rw [_root_.RHTower.ZetaNotch.xi_eq_half_mul_gammaR_zeta h0 hs1 hre]
  exact mul_ne_zero (div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr hs1)) two_ne_zero)
    (mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hre)
      (riemannZeta_ne_zero_of_riemannHypothesis hRH hs))

/-- Under RH every copy is a nonzero point `ρ = ½ + iγ` with `γ ≠ 0`. -/
theorem xiZeroCopy_facts (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    (q.1 : ℂ).re = 1 / 2 ∧ (q.1 : ℂ) ≠ 0 ∧ (q.1 : ℂ) - 1 / 2 ≠ 0 := by
  have hre := _root_.RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  refine ⟨hre, fun h => by rw [h, Complex.zero_re] at hre; norm_num at hre,
    sub_ne_zero.mpr (_root_.RHTower.xi_divisor_support_ne_half q.1)⟩

/-- Under RH, `‖ρ − ½‖ ≤ ‖ρ‖` for every copy. -/
theorem norm_sub_half_le_norm (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    ‖(q.1 : ℂ) - 1 / 2‖ ≤ ‖(q.1 : ℂ)‖ := by
  have hre := (xiZeroCopy_facts hRH q).1
  have h1 : ‖(q.1 : ℂ) - 1 / 2‖ ^ 2 = ((q.1 : ℂ).im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [hre]; ring
  have h2 : ‖(q.1 : ℂ)‖ ^ 2 = 1 / 4 + ((q.1 : ℂ).im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre]; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (by rw [h1, h2]; linarith)

/-- Under RH the split constant is absolutely summable. -/
theorem summable_splitConstant_term (hRH : RiemannHypothesis) :
    Summable fun q : XiZeroCopy => 1 / (2 * (q.1 : ℂ) * ((q.1 : ℂ) - 1 / 2)) := by
  refine Summable.of_norm (_root_.RHTower.xiSpectralPoint_inv_sq_summable.of_nonneg_of_le
    (fun _ => by positivity) fun q => ?_)
  obtain ⟨-, h0, hh⟩ := xiZeroCopy_facts hRH q
  rw [_root_.RHTower.norm_xiSpectralPoint, norm_div, norm_one, norm_mul, norm_mul]
  have hle := norm_sub_half_le_norm hRH q
  have hpos : 0 < ‖(q.1 : ℂ) - 1 / 2‖ := norm_pos_iff.mpr hh
  rw [show ‖(2 : ℂ)‖ = 2 by simp]
  refine one_div_le_one_div_of_le (by positivity) ?_
  nlinarith

/-- `((ρ − ½)⁻¹ + (s − ρ)⁻¹)/s = 1/(ρ(s − ρ)) + 1/(2ρ(ρ − ½)) · (1/s)`. -/
theorem partialFraction_div_eq {ρ s : ℂ} (h0 : ρ ≠ 0) (hh : ρ - 1 / 2 ≠ 0) (hs : s - ρ ≠ 0)
    (hs0 : s ≠ 0) :
    ((ρ - 1 / 2)⁻¹ + (s - ρ)⁻¹) / s = 1 / (ρ * (s - ρ)) + 1 / (2 * ρ * (ρ - 1 / 2)) * (1 / s) := by
  have h2 : 2 * ρ - 1 ≠ 0 := fun h => hh (by linear_combination h / 2)
  have h3 : -1 + ρ * 2 ≠ 0 := fun h => hh (by linear_combination h / 2)
  rw [show ρ - 1 / 2 = (2 * ρ - 1) / 2 by ring]
  field_simp
  ring

/-- Under RH the zero-part terms `(−1/ρ_q)/(s − ρ_q)` are summable on `Re s > ½`, `s ≠ 1`. -/
theorem summable_zeroPart_term (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s ≠ 1) :
    Summable fun q : XiZeroCopy => -(1 / (q.1 : ℂ)) / (s - (q.1 : ℂ)) := by
  have hre : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; exact lt_irrefl _ hre
  have hxi := xi_ne_zero_of_riemannHypothesis hRH hs hs1
  have hA : Summable fun q : XiZeroCopy => ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹ :=
    (_root_.RHTower.XiAtlasFinitePart.summable_logDerivTerm hxi).congr fun q => by
      simp only [_root_.RHTower.XiAtlasFinitePart.xiZero]
      rw [← neg_sub s (q.1 : ℂ), inv_neg, sub_neg_eq_add]
  have hC := summable_splitConstant_term hRH
  have hsne : ∀ q : XiZeroCopy, s - (q.1 : ℂ) ≠ 0 := fun q h => by
    have := congrArg Complex.re h
    simp [(xiZeroCopy_facts hRH q).1] at this
    linarith
  refine (((hA.div_const s).sub (hC.mul_right (1 / s))).neg).congr fun q => ?_
  rw [partialFraction_div_eq (xiZeroCopy_facts hRH q).2.1 (xiZeroCopy_facts hRH q).2.2 (hsne q) hs0]
  have := (xiZeroCopy_facts hRH q).2.1
  have := hsne q
  field_simp
  ring

/-- **The split.** Under RH, on `Re s > ½`, `s ≠ 1`:
`(−ζ′/ζ − ζ)(s)/s = Σ'_q (−1/ρ_q)/(s − ρ_q) + R(s)`. -/
theorem primeErrorSymbol_eq_zeroPart_add (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s ≠ 1) :
    (-deriv riemannZeta s / riemannZeta s - riemannZeta s) / s = zeroPart s + archRemainder s := by
  have hre : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; exact lt_irrefl _ hre
  have hζ := riemannZeta_ne_zero_of_riemannHypothesis hRH hs
  have hxi := xi_ne_zero_of_riemannHypothesis hRH hs hs1
  have hsplit := logDeriv_xi_eq_add hre hs1 hζ
  rw [_root_.RHTower.logDeriv_xi_eq_partialFraction hxi] at hsplit
  have hA : Summable fun q : XiZeroCopy => ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹ :=
    (_root_.RHTower.XiAtlasFinitePart.summable_logDerivTerm hxi).congr fun q => by
      simp only [_root_.RHTower.XiAtlasFinitePart.xiZero]
      rw [← neg_sub s (q.1 : ℂ), inv_neg, sub_neg_eq_add]
  have hC := summable_splitConstant_term hRH
  have hsne : ∀ q : XiZeroCopy, s - (q.1 : ℂ) ≠ 0 := fun q h => by
    have := congrArg Complex.re h
    simp [(xiZeroCopy_facts hRH q).1] at this
    linarith
  have hterm : ∀ q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹) / s =
      1 / ((q.1 : ℂ) * (s - (q.1 : ℂ))) +
        1 / (2 * (q.1 : ℂ) * ((q.1 : ℂ) - 1 / 2)) * (1 / s) := fun q =>
    partialFraction_div_eq (xiZeroCopy_facts hRH q).2.1 (xiZeroCopy_facts hRH q).2.2 (hsne q) hs0
  have hB : Summable fun q : XiZeroCopy => 1 / ((q.1 : ℂ) * (s - (q.1 : ℂ))) :=
    ((hA.div_const s).sub (hC.mul_right (1 / s))).congr fun q => by rw [hterm q]; ring
  have hsum : ∑' q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹) =
      s * ∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (s - (q.1 : ℂ))) + splitConstant := by
    have h : ∑' q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹) / s =
        ∑' q : XiZeroCopy, (1 / ((q.1 : ℂ) * (s - (q.1 : ℂ))) +
          1 / (2 * (q.1 : ℂ) * ((q.1 : ℂ) - 1 / 2)) * (1 / s)) := tsum_congr hterm
    rw [tsum_div_const, hB.tsum_add (hC.mul_right _), tsum_mul_right] at h
    rw [splitConstant]
    calc ∑' q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹)
        = s * ((∑' q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹)) / s) := by
          rw [mul_div_assoc', mul_div_cancel_left₀ _ hs0]
      _ = s * ((∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (s - (q.1 : ℂ)))) +
            (∑' q : XiZeroCopy, 1 / (2 * (q.1 : ℂ) * ((q.1 : ℂ) - 1 / 2))) * (1 / s)) := by
          rw [h]
      _ = _ := by field_simp
  have hneg : zeroPart s = -∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (s - (q.1 : ℂ))) := by
    rw [zeroPart, ← tsum_neg]
    exact tsum_congr fun q => by
      have := (xiZeroCopy_facts hRH q).2.1
      have := hsne q
      field_simp
  have hlog : -deriv riemannZeta s / riemannZeta s = -logDeriv riemannZeta s := by
    rw [logDeriv_apply, neg_div]
  rw [hneg, archRemainder, hlog]
  have hL : logDeriv riemannZeta s =
      s * ∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (s - (q.1 : ℂ))) + splitConstant -
        (s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s) := by
    rw [← hsum, hsplit]; ring
  rw [hL]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

/-! ### The remainder is uniformly square integrable near the critical line -/

theorem continuousOn_logDeriv_Gammaℝ :
    ContinuousOn (logDeriv Complex.Gammaℝ) {s : ℂ | 0 < s.re} := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Complex.Gammaℝ {s : ℂ | 0 < s.re} := fun s hs =>
    (_root_.RHTower.hasDerivAt_Gammaℝ_of_re_pos hs).differentiableAt.differentiableWithinAt
  have hderiv : ContinuousOn (deriv Complex.Gammaℝ) {s : ℂ | 0 < s.re} :=
    (hd.analyticOnNhd hU).deriv.continuousOn
  intro s hs
  have := (hderiv s hs).div (hd.continuousOn s hs) (Complex.Gammaℝ_ne_zero_of_re_pos hs)
  exact this.congr (fun z _ => logDeriv_apply _ _) (logDeriv_apply _ _)

theorem continuousOn_archRemainder : ContinuousOn archRemainder {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  intro s hs
  obtain ⟨hre, h1⟩ := hs
  have h0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; exact lt_irrefl _ hre
  have hΓ : ContinuousWithinAt (logDeriv Complex.Gammaℝ) {s : ℂ | 0 < s.re ∧ s ≠ 1} s :=
    (continuousOn_logDeriv_Gammaℝ s hre).mono fun z hz => hz.1
  have hζ : ContinuousAt riemannZeta s := (differentiableAt_riemannZeta h1).continuousAt
  unfold archRemainder
  exact ((((continuousWithinAt_const.add (continuousWithinAt_const.div continuousWithinAt_id h0)).add
    (continuousWithinAt_const.div (continuousWithinAt_id.sub continuousWithinAt_const)
      (sub_ne_zero.mpr h1))).add hΓ).sub hζ.continuousWithinAt).div continuousWithinAt_id h0

/-- `Γℝ′/Γℝ` commutes with conjugation. -/
theorem logDeriv_Gammaℝ_conj {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (logDeriv Complex.Gammaℝ s) := by
  have hd := _root_.RHTower.hasDerivAt_Gammaℝ_of_re_pos hs
  have hc := hd.conj_conj
  have hfun : (⇑(starRingEnd ℂ) ∘ Complex.Gammaℝ ∘ ⇑(starRingEnd ℂ)) = Complex.Gammaℝ := by
    funext z
    simp only [Function.comp_apply, _root_.RHTower.Gammaℝ_conj, Complex.conj_conj]
  rw [hfun] at hc
  rw [logDeriv_apply, logDeriv_apply, hc.deriv, hd.deriv, map_div₀, _root_.RHTower.Gammaℝ_conj]

/-- Vertical bounds for `ζ` and `Γℝ′/Γℝ` on `½ ≤ σ ≤ 3/4`, `|t| ≥ 8`. -/
theorem exists_vertical_bounds :
    ∃ Cζ KΓ : ℝ, 0 < Cζ ∧ 0 ≤ KΓ ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 → 8 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * |t| ^ (3 / 8 : ℝ) ∧
      ‖logDeriv Complex.Gammaℝ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Real.log |t| + KΓ := by
  obtain ⟨Cζ, hCζ, hζ⟩ := _root_.RHTower.exists_norm_riemannZeta_le_convexity
    (η := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨Cζ, |GaloisForLFunctions.digammaVerticalLogConstant|, hCζ, abs_nonneg _,
    fun σ t hσ hσ' ht => ?_⟩
  have hpos : ∀ u : ℝ, 8 ≤ u →
      ‖riemannZeta ((σ : ℂ) + (u : ℂ) * I)‖ ≤ Cζ * u ^ (3 / 8 : ℝ) ∧
      ‖logDeriv Complex.Gammaℝ ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        Real.log u + |GaloisForLFunctions.digammaVerticalLogConstant| := by
    intro u hu
    refine ⟨(hζ σ u (by linarith) (by linarith) hu).trans ?_, ?_⟩
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith)
        (by linarith)) hCζ.le
    · exact (_root_.RHTower.norm_logDeriv_Gammaℝ_le hσ (by linarith) (by linarith)).trans
        (by linarith [le_abs_self GaloisForLFunctions.digammaVerticalLogConstant])
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢; exact hpos t ht
  · rw [abs_of_neg h] at ht ⊢
    obtain ⟨h1, h2⟩ := hpos (-t) ht
    have hconj : (σ : ℂ) + (t : ℂ) * I = starRingEnd ℂ ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    have hre : 0 < ((σ : ℂ) + ((-t : ℝ) : ℂ) * I).re := by simp; linarith
    rw [hconj, riemannZeta_conj, Complex.norm_conj, logDeriv_Gammaℝ_conj hre, Complex.norm_conj]
    exact ⟨h1, h2⟩

/-- **The remainder decays.** `‖R(½ + c + iy)‖ ≤ K (1 + |y|)^{−5/8}` for `0 < c ≤ ¼`. -/
theorem exists_norm_archRemainder_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 0 < c → c ≤ 1 / 4 → ∀ y : ℝ,
      ‖archRemainder (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ K * (1 + |y|) ^ (-(5 / 8 : ℝ)) := by
  -- the compact part
  have hcomp : IsCompact (Set.Icc (1 / 2 : ℝ) (3 / 4) ×ˢ Set.Icc (-8 : ℝ) 8) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => archRemainder ((p.1 : ℂ) + (p.2 : ℂ) * I))
      (Set.Icc (1 / 2 : ℝ) (3 / 4) ×ˢ Set.Icc (-8 : ℝ) 8) := by
    refine continuousOn_archRemainder.comp (by fun_prop) fun p hp => ?_
    obtain ⟨⟨h1, h2⟩, -⟩ := hp
    refine ⟨by simp; linarith, fun h => ?_⟩
    have := congrArg Complex.re h
    simp at this
    linarith
  obtain ⟨B₀, hB₀⟩ := hcomp.exists_bound_of_continuousOn hcont
  obtain ⟨Cζ, KΓ, hCζ, hKΓ, hb⟩ := exists_vertical_bounds
  set K₁ : ℝ := ‖splitConstant‖ + 1 + KΓ + 8 / 3 + Cζ with hK₁
  refine ⟨max (9 * |B₀|) (2 * K₁), by positivity, fun c hc hc4 y => ?_⟩
  have hσ : (1 / 2 : ℝ) ≤ c + 1 / 2 := by linarith
  have hσ' : c + 1 / 2 ≤ 3 / 4 := by linarith
  have hKmax1 : 9 * |B₀| ≤ max (9 * |B₀|) (2 * K₁) := le_max_left _ _
  have hKmax2 : 2 * K₁ ≤ max (9 * |B₀|) (2 * K₁) := le_max_right _ _
  have hpow0 : 0 < (1 + |y|) ^ (-(5 / 8 : ℝ)) := by positivity
  rcases le_or_gt |y| 8 with hy | hy
  · -- `|y| ≤ 8`: the compact bound
    have hB := hB₀ (c + 1 / 2, y) ⟨⟨hσ, hσ'⟩, abs_le.mp hy⟩
    have hpow : 1 / 9 ≤ (1 + |y|) ^ (-(5 / 8 : ℝ)) := by
      rw [Real.rpow_neg (by positivity)]
      have h1 : (1 + |y|) ^ (5 / 8 : ℝ) ≤ 9 :=
        (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) (by norm_num :
          (5 / 8 : ℝ) ≤ 1)).trans (by rw [Real.rpow_one]; linarith)
      rw [one_div]
      exact inv_anti₀ (by positivity) h1
    calc ‖archRemainder (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ |B₀| :=
          hB.trans (le_abs_self _)
      _ = 9 * |B₀| * (1 / 9) := by ring
      _ ≤ max (9 * |B₀|) (2 * K₁) * (1 + |y|) ^ (-(5 / 8 : ℝ)) :=
          mul_le_mul hKmax1 hpow (by norm_num) (by positivity)
  · -- `|y| > 8`: the vertical bounds
    set t := |y| with ht
    have ht8 : 8 ≤ t := hy.le
    have ht0 : 0 < t := by linarith
    obtain ⟨hζb, hΓb⟩ := hb (c + 1 / 2) y hσ hσ' ht8
    set z : ℂ := ((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I with hz
    have hzim : z.im = y := by simp [hz]
    have hzt : t ≤ ‖z‖ := by rw [ht, ← hzim]; exact Complex.abs_im_le_norm z
    have hz1t : t ≤ ‖z - 1‖ := by
      rw [ht, show y = (z - 1).im by simp [hzim]]; exact Complex.abs_im_le_norm _
    have htpow : 1 ≤ t ^ (3 / 8 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hlog : Real.log t ≤ 8 / 3 * t ^ (3 / 8 : ℝ) := by
      have := Real.log_le_rpow_div ht0.le (show (0 : ℝ) < 3 / 8 by norm_num)
      linarith [show t ^ (3 / 8 : ℝ) / (3 / 8) = 8 / 3 * t ^ (3 / 8 : ℝ) by ring]
    have hinv : ‖1 / z‖ + ‖1 / (z - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one, norm_div, norm_one]
      have h1 : 1 / ‖z‖ ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      have h2 : 1 / ‖z - 1‖ ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have hnum : ‖-splitConstant + 1 / z + 1 / (z - 1) + logDeriv Complex.Gammaℝ z -
        riemannZeta z‖ ≤ K₁ * t ^ (3 / 8 : ℝ) := by
      calc ‖-splitConstant + 1 / z + 1 / (z - 1) + logDeriv Complex.Gammaℝ z - riemannZeta z‖
          ≤ ‖splitConstant‖ + (‖1 / z‖ + ‖1 / (z - 1)‖) + ‖logDeriv Complex.Gammaℝ z‖ +
              ‖riemannZeta z‖ := by
            have e1 := norm_sub_le (-splitConstant + 1 / z + 1 / (z - 1) +
              logDeriv Complex.Gammaℝ z) (riemannZeta z)
            have e2 := norm_add_le (-splitConstant + 1 / z + 1 / (z - 1))
              (logDeriv Complex.Gammaℝ z)
            have e3 := norm_add_le (-splitConstant + 1 / z) (1 / (z - 1))
            have e4 := norm_add_le (-splitConstant) (1 / z)
            rw [norm_neg] at e4
            linarith
        _ ≤ ‖splitConstant‖ + 1 + (Real.log t + KΓ) + Cζ * t ^ (3 / 8 : ℝ) := by
            gcongr
        _ ≤ K₁ * t ^ (3 / 8 : ℝ) := by
            rw [hK₁]
            have := norm_nonneg splitConstant
            nlinarith
    have hR : ‖archRemainder z‖ ≤ K₁ * t ^ (-(5 / 8 : ℝ)) := by
      rw [archRemainder, norm_div]
      have hdiv : K₁ * t ^ (3 / 8 : ℝ) / t = K₁ * t ^ (-(5 / 8 : ℝ)) := by
        rw [mul_div_assoc, show (-(5 / 8 : ℝ)) = 3 / 8 - 1 by norm_num,
          Real.rpow_sub ht0, Real.rpow_one]
      rw [← hdiv]
      exact div_le_div₀ (by positivity) hnum ht0 hzt
    have hcmp : t ^ (-(5 / 8 : ℝ)) ≤ 2 * (1 + t) ^ (-(5 / 8 : ℝ)) := by
      rw [Real.rpow_neg ht0.le, Real.rpow_neg (by positivity)]
      have h1 : (1 + t) ^ (5 / 8 : ℝ) ≤ 2 * t ^ (5 / 8 : ℝ) := by
        calc (1 + t) ^ (5 / 8 : ℝ) ≤ (2 * t) ^ (5 / 8 : ℝ) :=
              Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
          _ = 2 ^ (5 / 8 : ℝ) * t ^ (5 / 8 : ℝ) := Real.mul_rpow (by norm_num) ht0.le
          _ ≤ 2 * t ^ (5 / 8 : ℝ) := by
              gcongr
              exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num :
                (5 / 8 : ℝ) ≤ 1)).trans (by rw [Real.rpow_one])
      have hp : 0 < t ^ (5 / 8 : ℝ) := by positivity
      have hq : 0 < (1 + t) ^ (5 / 8 : ℝ) := by positivity
      rw [← div_eq_mul_inv, le_div_iff₀ hq]
      calc (t ^ (5 / 8 : ℝ))⁻¹ * (1 + t) ^ (5 / 8 : ℝ)
          ≤ (t ^ (5 / 8 : ℝ))⁻¹ * (2 * t ^ (5 / 8 : ℝ)) := by gcongr
        _ = 2 := by field_simp
    have hK1 : 0 ≤ K₁ := by rw [hK₁]; positivity
    calc ‖archRemainder z‖ ≤ K₁ * t ^ (-(5 / 8 : ℝ)) := hR
      _ ≤ K₁ * (2 * (1 + t) ^ (-(5 / 8 : ℝ))) := mul_le_mul_of_nonneg_left hcmp hK1
      _ = 2 * K₁ * (1 + t) ^ (-(5 / 8 : ℝ)) := by ring
      _ ≤ max (9 * |B₀|) (2 * K₁) * (1 + t) ^ (-(5 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_right hKmax2 (by positivity)

/-- **The remainder is uniformly square integrable:** `∫ ‖R(½ + c + iy)‖² dy ≤ K₂` for
`0 < c ≤ ¼`. -/
theorem exists_integral_norm_sq_archRemainder_le :
    ∃ K₂ : ℝ, ∀ c : ℝ, 0 < c → c ≤ 1 / 4 →
      MeasureTheory.Integrable
        (fun y : ℝ => ‖archRemainder (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2) ∧
      ∫ y : ℝ, ‖archRemainder (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤ K₂ := by
  obtain ⟨K, hK, hb⟩ := exists_norm_archRemainder_le
  have hint : MeasureTheory.Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(5 / 4 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  refine ⟨∫ y : ℝ, K ^ 2 * (1 + ‖y‖) ^ (-(5 / 4 : ℝ)), fun c hc hc4 => ?_⟩
  have hpt : ∀ y : ℝ, ‖archRemainder (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤
      K ^ 2 * (1 + ‖y‖) ^ (-(5 / 4 : ℝ)) := by
    intro y
    rw [Real.norm_eq_abs]
    calc ‖archRemainder (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2
        ≤ (K * (1 + |y|) ^ (-(5 / 8 : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hb c hc hc4 y) 2
      _ = K ^ 2 * (1 + |y|) ^ (-(5 / 4 : ℝ)) := by
          rw [mul_pow, ← Real.rpow_natCast ((1 + |y|) ^ (-(5 / 8 : ℝ))),
            ← Real.rpow_mul (by positivity)]
          norm_num
  have hcont : Continuous fun y : ℝ => archRemainder (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) :=
    continuousOn_archRemainder.comp_continuous (by fun_prop) fun y => by
      refine ⟨by simp; linarith, fun h => ?_⟩
      have := congrArg Complex.re h
      simp at this
      linarith
  have hI : MeasureTheory.Integrable
      (fun y : ℝ => ‖archRemainder (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2) :=
    (hint.const_mul (K ^ 2)).mono (hcont.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
        exact hpt y)
  exact ⟨hI, MeasureTheory.integral_mono hI (hint.const_mul _) hpt⟩

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
