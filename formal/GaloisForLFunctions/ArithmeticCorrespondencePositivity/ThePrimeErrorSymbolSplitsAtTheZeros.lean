import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.RHTower.XiHadamardFinitePart
import GaloisForLFunctions.RHTower.ZetaNotchSmoothTest
import GaloisForLFunctions.RHTower.WeilLagFunction

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
    field_simp at h
    linear_combination h
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

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
