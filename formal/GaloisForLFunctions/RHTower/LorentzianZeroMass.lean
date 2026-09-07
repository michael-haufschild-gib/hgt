import GaloisForLFunctions.RHTower.MontgomeryFormHeightMeanSquare
import GaloisForLFunctions.HTGeometry.GammaDigammaStirlingBound

/-!
# The Lorentzian zero mass `Σ_ρ 1/(1 + (t − γ)²)`

For every real `t` the Lorentzian mass of the zeros of `ξ`, `M(t) := Σ_ρ 1/(1 + (t − γ)²)` over all
zeros with multiplicity, is at most `8 Re ξ'/ξ(2 + it)`.  The mechanism: the partial fraction
`ξ'/ξ(s) = Σ_ρ [(ρ − ½)⁻¹ + (s − ρ)⁻¹]` is invariant under the reflection `ρ ↦ 1 − ρ` of the zero
set; adding the reflected copy kills the `(ρ − ½)⁻¹` parts exactly and leaves the two non-negative
real parts `Re (s − ρ)⁻¹ + Re (s − 1 + ρ)⁻¹`, the first of which is at least `¼ · 1/(1 + (t − γ)²)`
on the line `Re s = 2`.

On that line `ξ'/ξ` is bounded by an explicit constant plus `log(|t| + 3)`: the polar terms are
bounded, the zeta term by `Σ Λ(n)/n²`, and the archimedean term by the Stirling bound for the digamma
function after two recurrence steps.  Consequently `M(t) ≤ 8 (C + log(|t| + 3))` for all `t`.
-/

open Complex MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry
open ArithmeticFunction (vonMangoldt)

namespace RHTower

/-! ## The mass and its summability -/

/-- The Lorentzian mass term `1/(1 + (t − γ)²)` of a zero copy at height `t`. -/
noncomputable def lorentzMassTerm (t : ℝ) (q : XiZeroCopy) : ℝ :=
  1 / (1 + (t - (q.1 : ℂ).im) ^ 2)

/-- The Lorentzian zero mass `Σ_ρ 1/(1 + (t − γ)²)` at height `t`. -/
noncomputable def lorentzMass (t : ℝ) : ℝ := ∑' q : XiZeroCopy, lorentzMassTerm t q

theorem lorentzMassTerm_nonneg (t : ℝ) (q : XiZeroCopy) : 0 ≤ lorentzMassTerm t q := by
  unfold lorentzMassTerm; positivity

theorem lorentzMassTerm_le_one (t : ℝ) (q : XiZeroCopy) : lorentzMassTerm t q ≤ 1 := by
  unfold lorentzMassTerm
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (t - (q.1 : ℂ).im)]

/-- `‖1 + (t + a)²‖ ≤ (5/4)(1 + (t + Re a)²)` when `|Im a| ≤ 1/2`. -/
theorem norm_one_add_sq_le {a : ℂ} (ha : |a.im| ≤ 1 / 2) (t : ℝ) :
    ‖1 + ((t : ℂ) + a) ^ 2‖ ≤ (5 / 4) * (1 + (t + a.re) ^ 2) := by
  have h1 : ‖1 + ((t : ℂ) + a) ^ 2‖ ≤ 1 + ‖(t : ℂ) + a‖ ^ 2 := by
    calc ‖1 + ((t : ℂ) + a) ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖((t : ℂ) + a) ^ 2‖ := norm_add_le _ _
      _ = 1 + ‖(t : ℂ) + a‖ ^ 2 := by rw [norm_one, norm_pow]
  have h2 : ‖(t : ℂ) + a‖ ^ 2 = (t + a.re) ^ 2 + a.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, zero_add]
    ring
  have h3 : a.im ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp ha
    nlinarith
  rw [h2] at h1
  nlinarith [sq_nonneg (t + a.re)]

/-- The mass term is at most `5/4` times the Lorentzian at the centre `i(ρ − ½)`. -/
theorem lorentzMassTerm_le_norm_lorentzShift (t : ℝ) (q : XiZeroCopy) :
    lorentzMassTerm t q ≤ (5 / 4) * ‖lorentzShift (lorentzCentre (q.1 : ℂ)) t‖ := by
  have hβ0 := xiZeroCopy_re_pos q
  have hβ1 := xiZeroCopy_re_lt_one q
  have him : |(lorentzCentre (q.1 : ℂ)).im| ≤ 1 / 2 := by
    rw [lorentzCentre_im, abs_le]; constructor <;> linarith
  have hre : (lorentzCentre (q.1 : ℂ)).re = -(q.1 : ℂ).im := lorentzCentre_re _
  have hne : (1 : ℂ) + ((t : ℂ) + lorentzCentre (q.1 : ℂ)) ^ 2 ≠ 0 := by
    refine one_add_sq_ne_zero ?_ t
    rw [mem_unitStrip]; exact lt_of_le_of_lt him (by norm_num)
  have hpos : 0 < ‖(1 : ℂ) + ((t : ℂ) + lorentzCentre (q.1 : ℂ)) ^ 2‖ := norm_pos_iff.mpr hne
  have hb := norm_one_add_sq_le him t
  rw [hre] at hb
  rw [lorentzShift, norm_div, norm_one, lorentzMassTerm]
  rw [show t + -(q.1 : ℂ).im = t - (q.1 : ℂ).im by ring] at hb
  rw [div_le_iff₀ (by positivity)]
  calc (1 : ℝ) = (5 / 4) * (1 / ‖(1 : ℂ) + ((t : ℂ) + lorentzCentre (q.1 : ℂ)) ^ 2‖)
        * ((4 / 5) * ‖(1 : ℂ) + ((t : ℂ) + lorentzCentre (q.1 : ℂ)) ^ 2‖) := by
        field_simp
    _ ≤ (5 / 4) * (1 / ‖(1 : ℂ) + ((t : ℂ) + lorentzCentre (q.1 : ℂ)) ^ 2‖)
        * (1 + (t - (q.1 : ℂ).im) ^ 2) := by
        gcongr
        linarith

theorem norm_montgomeryZeroTerm_one (t : ℝ) (q : XiZeroCopy) :
    ‖montgomeryZeroTerm 1 t q‖ = 2 * ‖lorentzShift (lorentzCentre (q.1 : ℂ)) t‖ := by
  rw [montgomeryZeroTerm_eq_lorentz, Complex.ofReal_one, Complex.one_cpow, mul_one, norm_mul,
    norm_neg]
  norm_num

theorem summable_lorentzMassTerm (t : ℝ) : Summable (lorentzMassTerm t) := by
  have hs := (summable_montgomeryZeroTerm (le_refl (1 : ℝ)) t).norm
  refine Summable.of_nonneg_of_le (lorentzMassTerm_nonneg t) (fun q => ?_) (hs.mul_left (5 / 8))
  rw [norm_montgomeryZeroTerm_one]
  have := lorentzMassTerm_le_norm_lorentzShift t q
  linarith

/-! ## The reflection argument -/

/-- The partial-fraction summand `(ρ − ½)⁻¹ + (s − ρ)⁻¹`. -/
noncomputable def partialFractionSummand (s : ℂ) (q : XiZeroCopy) : ℂ :=
  ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹

theorem xiZeroCopyReflectEquiv_coe (q : XiZeroCopy) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := rfl

/-- The summand plus its reflection is `(s − ρ)⁻¹ + (s − 1 + ρ)⁻¹`. -/
theorem partialFractionSummand_add_reflect (s : ℂ) (q : XiZeroCopy) :
    partialFractionSummand s q + partialFractionSummand s (xiZeroCopyReflectEquiv q)
      = (s - (q.1 : ℂ))⁻¹ + (s - 1 + (q.1 : ℂ))⁻¹ := by
  simp only [partialFractionSummand, xiZeroCopyReflectEquiv_coe]
  have : ((1 : ℂ) - (q.1 : ℂ) - 1 / 2)⁻¹ = -((q.1 : ℂ) - 1 / 2)⁻¹ := by
    rw [← inv_neg]; congr 1; ring
  rw [this, show s - (1 - (q.1 : ℂ)) = s - 1 + (q.1 : ℂ) by ring]
  ring

theorem re_inv_nonneg_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) : 0 ≤ z⁻¹.re := by
  rw [Complex.inv_re]
  exact div_nonneg hz (Complex.normSq_nonneg z)

/-- On the line `Re s = 2`, `Re (s − ρ)⁻¹ ≥ ¼ · 1/(1 + (t − γ)²)`. -/
theorem lorentzMassTerm_le_re_inv (t : ℝ) (q : XiZeroCopy) :
    lorentzMassTerm t q ≤ 4 * ((lineTwo t - (q.1 : ℂ))⁻¹).re := by
  have hβ0 := xiZeroCopy_re_pos q
  have hβ1 := xiZeroCopy_re_lt_one q
  have hre : (lineTwo t - (q.1 : ℂ)).re = 2 - (q.1 : ℂ).re := by rw [lineTwo_eq]; simp
  have him : (lineTwo t - (q.1 : ℂ)).im = t - (q.1 : ℂ).im := by rw [lineTwo_eq]; simp
  rw [Complex.inv_re, Complex.normSq_apply, hre, him]
  have hden : 0 < (2 - (q.1 : ℂ).re) * (2 - (q.1 : ℂ).re)
      + (t - (q.1 : ℂ).im) * (t - (q.1 : ℂ).im) := by
    nlinarith [sq_nonneg (t - (q.1 : ℂ).im)]
  rw [lorentzMassTerm, mul_div_assoc', div_le_div_iff₀ (by positivity) hden]
  nlinarith [sq_nonneg (t - (q.1 : ℂ).im), sq_nonneg ((q.1 : ℂ).re - 1)]

theorem xi_lineTwo_ne_zero (t : ℝ) : xi (lineTwo t) ≠ 0 := by
  apply xi_ne_zero_of_one_le_re
  rw [lineTwo_eq]; simp

theorem summable_re_partialFractionSummand (t : ℝ) :
    Summable (fun q : XiZeroCopy => (partialFractionSummand (lineTwo t) q).re) :=
  (Complex.hasSum_re (summable_partialFractionTerm (xi_lineTwo_ne_zero t)).hasSum).summable

theorem summable_re_partialFractionSummand_reflect (t : ℝ) :
    Summable (fun q : XiZeroCopy =>
      (partialFractionSummand (lineTwo t) (xiZeroCopyReflectEquiv q)).re) :=
  (xiZeroCopyReflectEquiv.summable_iff
    (f := fun q : XiZeroCopy => (partialFractionSummand (lineTwo t) q).re)).mpr
    (summable_re_partialFractionSummand t)

/-- **The Lorentzian mass is at most `8 Re ξ'/ξ(2 + it)`.** -/
theorem lorentzMass_le_re_logDeriv_xi (t : ℝ) :
    lorentzMass t ≤ 8 * (logDeriv xi (lineTwo t)).re := by
  set s := lineTwo t with hs
  have hB := summable_partialFractionTerm (xi_lineTwo_ne_zero t)
  have hBre := summable_re_partialFractionSummand t
  have hBre' := summable_re_partialFractionSummand_reflect t
  have hpt : ∀ q : XiZeroCopy, lorentzMassTerm t q ≤
      4 * ((partialFractionSummand s q).re
        + (partialFractionSummand s (xiZeroCopyReflectEquiv q)).re) := by
    intro q
    have h1 := lorentzMassTerm_le_re_inv t q
    have h2 : 0 ≤ ((s - 1 + (q.1 : ℂ))⁻¹).re := by
      apply re_inv_nonneg_of_re_nonneg
      rw [hs, lineTwo_eq]
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, Complex.one_re]
      linarith [xiZeroCopy_re_pos q]
    have h3 : (partialFractionSummand s q).re
        + (partialFractionSummand s (xiZeroCopyReflectEquiv q)).re
        = ((s - (q.1 : ℂ))⁻¹).re + ((s - 1 + (q.1 : ℂ))⁻¹).re := by
      rw [← Complex.add_re, partialFractionSummand_add_reflect, Complex.add_re]
    rw [h3]; linarith
  have hsum : Summable (fun q : XiZeroCopy => 4 * ((partialFractionSummand s q).re
      + (partialFractionSummand s (xiZeroCopyReflectEquiv q)).re)) :=
    (hBre.add hBre').mul_left 4
  calc lorentzMass t ≤ ∑' q : XiZeroCopy, 4 * ((partialFractionSummand s q).re
        + (partialFractionSummand s (xiZeroCopyReflectEquiv q)).re) :=
        Summable.tsum_le_tsum hpt (summable_lorentzMassTerm t) hsum
    _ = 4 * ((∑' q : XiZeroCopy, (partialFractionSummand s q).re)
        + ∑' q : XiZeroCopy, (partialFractionSummand s (xiZeroCopyReflectEquiv q)).re) := by
        rw [tsum_mul_left, hBre.tsum_add hBre']
    _ = 8 * ∑' q : XiZeroCopy, (partialFractionSummand s q).re := by
        rw [xiZeroCopyReflectEquiv.tsum_eq
          (fun q : XiZeroCopy => (partialFractionSummand s q).re)]
        ring
    _ = 8 * (logDeriv xi s).re := by
        rw [logDeriv_xi_eq_partialFraction (xi_lineTwo_ne_zero t), Complex.re_tsum hB]
        rfl

theorem lorentzMass_le_norm_logDeriv_xi (t : ℝ) :
    lorentzMass t ≤ 8 * ‖logDeriv xi (lineTwo t)‖ :=
  (lorentzMass_le_re_logDeriv_xi t).trans
    (by gcongr; exact Complex.re_le_norm _)

/-! ## `ξ'/ξ` on the line `Re s = 2` -/

/-- `Σ_n Λ(n)/n²`. -/
noncomputable def vonMangoldtSquareMass : ℝ := ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ 2

theorem vonMangoldtSquareMass_nonneg : 0 ≤ vonMangoldtSquareMass :=
  tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

theorem norm_logDeriv_zeta_lineTwo_le (t : ℝ) :
    ‖logDeriv riemannZeta (lineTwo t)‖ ≤ vonMangoldtSquareMass := by
  have hre : 1 < (lineTwo t).re := by rw [lineTwo_eq]; simp
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  have hlog : logDeriv riemannZeta (lineTwo t)
      = -LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo t) := by
    rw [hL, logDeriv_apply]; ring
  rw [hlog, norm_neg, LSeries]
  have hterm : ∀ n : ℕ, ‖LSeries.term (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo t) n‖
      = vonMangoldt n / (n : ℝ) ^ 2 := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · subst h0; simp
    · rw [lineTwo_eq]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      norm_cast
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · simp_rw [hterm]; exact summable_vonMangoldt_div_sq
  · simp_rw [hterm]; exact le_rfl

/-- `‖log z‖ ≤ log ‖z‖ + π` for `‖z‖ ≥ 1`. -/
theorem norm_log_le_of_one_le {z : ℂ} (hz : 1 ≤ ‖z‖) : ‖Complex.log z‖ ≤ Real.log ‖z‖ + Real.pi := by
  calc ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = Real.log ‖z‖ + |z.arg| := by
        rw [Complex.log_re, Complex.log_im, abs_of_nonneg (Real.log_nonneg hz)]
    _ ≤ Real.log ‖z‖ + Real.pi := by gcongr; exact Complex.abs_arg_le_pi z

/-- The constant in the digamma bound on the line `Re z = 1`. -/
noncomputable def digammaLineOneConstant : ℝ := Real.pi + 1 / 6 + 2 / 3 + 1 + 1 / 2

/-- `‖ψ(1 + iu)‖ ≤ log(|u| + 3) + C` for every real `u`, from the Stirling bound at `3 + iu`. -/
theorem norm_digamma_one_add_le (u : ℝ) :
    ‖Complex.digamma (1 + (u : ℂ) * I)‖ ≤ Real.log (|u| + 3) + digammaLineOneConstant := by
  set z : ℂ := 1 + (u : ℂ) * I with hz
  have hzre : z.re = 1 := by rw [hz]; simp
  have hzim : z.im = u := by rw [hz]; simp
  have hz1 : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    rw [hzre] at this; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hz2 : ∀ m : ℕ, z + 1 ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp [hzre] at this; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hrec1 := Complex.digamma_apply_add_one z hz1
  have hrec2 := Complex.digamma_apply_add_one (z + 1) hz2
  -- `ψ(z) = ψ(z + 2) − 1/(z+1) − 1/z`
  have hψ : Complex.digamma z = Complex.digamma (z + 1 + 1) - (z + 1)⁻¹ - z⁻¹ := by
    rw [hrec2, hrec1]; ring
  set w : ℂ := z + 1 + 1 with hw
  have hwre : w.re = 3 := by rw [hw]; simp [hzre]; norm_num
  have hwim : w.im = u := by rw [hw]; simp [hzim]
  have hwnorm : 3 ≤ ‖w‖ := by
    have := Complex.re_le_norm w; rw [hwre] at this; exact this
  have hwpos : 0 < w.re := by rw [hwre]; norm_num
  have hstir := norm_digammaStirlingDefect_le hwpos (by linarith)
  have hwnorm_le : ‖w‖ ≤ |u| + 3 := by
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ = |u| + 3 := by rw [hwre, hwim]; norm_num; ring
  -- `ψ(w) = defect + log w − 1/(2w)`
  have hψw : Complex.digamma w = digammaStirlingDefect w + Complex.log w - 1 / (2 * w) := by
    rw [digammaStirlingDefect]; ring
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hwre; simp at hwre
  have hnormz : 1 ≤ ‖z‖ := by
    have := Complex.re_le_norm z; rw [hzre] at this; exact this
  have hnormz1 : 2 ≤ ‖z + 1‖ := by
    have := Complex.re_le_norm (z + 1); simp [hzre] at this; linarith
  have hlogw := norm_log_le_of_one_le (z := w) (by linarith)
  have hlogw' : Real.log ‖w‖ ≤ Real.log (|u| + 3) :=
    Real.log_le_log (by linarith) hwnorm_le
  have hdef : ‖digammaStirlingDefect w‖ ≤ 6 / 9 := by
    refine hstir.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hhalf : ‖1 / (2 * w)‖ ≤ 1 / 6 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hinvz : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ hnormz
  have hinvz1 : ‖(z + 1)⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    simpa using hnormz1
  rw [hψ, hψw]
  calc ‖digammaStirlingDefect w + Complex.log w - 1 / (2 * w) - (z + 1)⁻¹ - z⁻¹‖
      ≤ ‖digammaStirlingDefect w‖ + ‖Complex.log w‖ + ‖1 / (2 * w)‖ + ‖(z + 1)⁻¹‖ + ‖z⁻¹‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 6 / 9 + (Real.log (|u| + 3) + Real.pi) + 1 / 6 + 1 / 2 + 1 := by
        gcongr
        exact hlogw.trans (by linarith)
    _ = Real.log (|u| + 3) + digammaLineOneConstant := by
        rw [digammaLineOneConstant]; ring

/-- The constant in the bound for `ξ'/ξ` on the line `Re s = 2`. -/
noncomputable def xiLineTwoLogDerivConstant : ℝ :=
  1 / 2 + 1 + (digammaLineOneConstant / 2 + Real.log Real.pi / 2) + vonMangoldtSquareMass

/-- **`‖ξ'/ξ(2 + it)‖ ≤ C + log(|t| + 3)`** for every real `t`. -/
theorem norm_logDeriv_xi_lineTwo_le (t : ℝ) :
    ‖logDeriv xi (lineTwo t)‖ ≤ xiLineTwoLogDerivConstant + Real.log (|t| + 3) := by
  have hre : 1 < (lineTwo t).re := by rw [lineTwo_eq]; simp
  have hre0 : 0 < (lineTwo t).re := by linarith
  rw [logDeriv_xi_split hre, logDeriv_Gammaℝ_digamma hre0]
  have h1 : ‖(lineTwo t)⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv]
    have hre2 : (lineTwo t).re = 2 := by rw [lineTwo_eq]; simp
    have : 2 ≤ ‖lineTwo t‖ := by
      have := Complex.re_le_norm (lineTwo t); rwa [hre2] at this
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; simpa using this
  have h2 : ‖(lineTwo t - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have hre1 : (lineTwo t - 1).re = 1 := by rw [lineTwo_eq]; simp; norm_num
    have : 1 ≤ ‖lineTwo t - 1‖ := by
      have := Complex.re_le_norm (lineTwo t - 1); rwa [hre1] at this
    exact inv_le_one_of_one_le₀ this
  have hhalf : lineTwo t / 2 = 1 + ((t / 2 : ℝ) : ℂ) * I := by
    rw [lineTwo_eq]; push_cast; ring
  have h3 : ‖Complex.digamma (lineTwo t / 2) / 2 - (Real.log Real.pi : ℂ) / 2‖
      ≤ (Real.log (|t| + 3) + digammaLineOneConstant) / 2 + Real.log Real.pi / 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    gcongr
    rw [hhalf]
    refine (norm_digamma_one_add_le (t / 2)).trans ?_
    have : Real.log (|t / 2| + 3) ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by positivity) (by rw [abs_div, abs_two]; linarith [abs_nonneg t])
    linarith
  have h4 := norm_logDeriv_zeta_lineTwo_le t
  calc ‖(lineTwo t)⁻¹ + (lineTwo t - 1)⁻¹
        + (Complex.digamma (lineTwo t / 2) / 2 - (Real.log Real.pi : ℂ) / 2)
        + logDeriv riemannZeta (lineTwo t)‖
      ≤ ‖(lineTwo t)⁻¹‖ + ‖(lineTwo t - 1)⁻¹‖
        + ‖Complex.digamma (lineTwo t / 2) / 2 - (Real.log Real.pi : ℂ) / 2‖
        + ‖logDeriv riemannZeta (lineTwo t)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 1 / 2 + 1 + ((Real.log (|t| + 3) + digammaLineOneConstant) / 2 + Real.log Real.pi / 2)
        + vonMangoldtSquareMass := by gcongr
    _ ≤ xiLineTwoLogDerivConstant + Real.log (|t| + 3) := by
        rw [xiLineTwoLogDerivConstant]
        have : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
        linarith

/-- **The Lorentzian zero mass is `O(log |t|)`**: `Σ_ρ 1/(1 + (t − γ)²) ≤ 8 (C + log(|t| + 3))`. -/
theorem lorentzMass_le_log (t : ℝ) :
    lorentzMass t ≤ 8 * (xiLineTwoLogDerivConstant + Real.log (|t| + 3)) :=
  (lorentzMass_le_norm_logDeriv_xi t).trans (by gcongr; exact norm_logDeriv_xi_lineTwo_le t)

end RHTower
