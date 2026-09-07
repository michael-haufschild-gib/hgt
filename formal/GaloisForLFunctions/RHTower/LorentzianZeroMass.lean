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

/-- `‖ψ(z)‖ ≤ log(‖z‖ + 2) + C` for `Re z ≥ 1`, from the Stirling bound at `z + 2`. -/
theorem norm_digamma_le_of_one_le_re {z : ℂ} (hzre : 1 ≤ z.re) :
    ‖Complex.digamma z‖ ≤ Real.log (‖z‖ + 2) + digammaLineOneConstant := by
  have hz1 : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hz2 : ∀ m : ℕ, z + 1 ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hrec1 := Complex.digamma_apply_add_one z hz1
  have hrec2 := Complex.digamma_apply_add_one (z + 1) hz2
  have hψ : Complex.digamma z = Complex.digamma (z + 1 + 1) - (z + 1)⁻¹ - z⁻¹ := by
    rw [hrec2, hrec1]; ring
  set w : ℂ := z + 1 + 1 with hw
  have hwre : w.re = z.re + 2 := by rw [hw]; simp; ring
  have hwnorm : 3 ≤ ‖w‖ := by
    have := Complex.re_le_norm w; rw [hwre] at this; linarith
  have hwpos : 0 < w.re := by rw [hwre]; linarith
  have hstir := norm_digammaStirlingDefect_le hwpos (by linarith)
  have hwnorm_le : ‖w‖ ≤ ‖z‖ + 2 := by
    calc ‖w‖ = ‖z + 2‖ := by rw [hw]; ring_nf
      _ ≤ ‖z‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + 2 := by rw [Complex.norm_ofNat]
  have hψw : Complex.digamma w = digammaStirlingDefect w + Complex.log w - 1 / (2 * w) := by
    rw [digammaStirlingDefect]; ring
  have hnormz : 1 ≤ ‖z‖ := by
    have := Complex.re_le_norm z; linarith
  have hnormz1 : 2 ≤ ‖z + 1‖ := by
    have := Complex.re_le_norm (z + 1); simp at this; linarith
  have hlogw := norm_log_le_of_one_le (z := w) (by linarith)
  have hlogw' : Real.log ‖w‖ ≤ Real.log (‖z‖ + 2) :=
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
    _ ≤ 6 / 9 + (Real.log (‖z‖ + 2) + Real.pi) + 1 / 6 + 1 / 2 + 1 := by
        gcongr
        exact hlogw.trans (by linarith)
    _ = Real.log (‖z‖ + 2) + digammaLineOneConstant := by
        rw [digammaLineOneConstant]; ring

/-- The constant in the bound for `ξ'/ξ` on `Re s ≥ 2`. -/
noncomputable def xiLineTwoLogDerivConstant : ℝ :=
  1 / 2 + 1 + (digammaLineOneConstant / 2 + Real.log Real.pi / 2) + vonMangoldtSquareMass

theorem norm_logDeriv_zeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖logDeriv riemannZeta s‖ ≤ vonMangoldtSquareMass := by
  have hre : 1 < s.re := by linarith
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  have hlog : logDeriv riemannZeta s = -LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) s := by
    rw [hL, logDeriv_apply]; ring
  rw [hlog, norm_neg, LSeries]
  have hterm : ∀ n : ℕ, ‖LSeries.term (fun n => ((vonMangoldt n : ℝ) : ℂ)) s n‖
      ≤ vonMangoldt n / (n : ℝ) ^ 2 := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · subst h0; simp
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      gcongr
      calc ((n : ℝ) ^ 2) = (n : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]
        _ ≤ (n : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hn hs
  have hsum : Summable (fun n => ‖LSeries.term (fun n => ((vonMangoldt n : ℝ) : ℂ)) s n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm summable_vonMangoldt_div_sq
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  exact Summable.tsum_le_tsum hterm hsum summable_vonMangoldt_div_sq

/-- **`‖ξ'/ξ(s)‖ ≤ C + log(‖s‖/2 + 3)`** on the half-plane `Re s ≥ 2`. -/
theorem norm_logDeriv_xi_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖logDeriv xi s‖ ≤ xiLineTwoLogDerivConstant + Real.log (‖s‖ / 2 + 3) := by
  have hre : 1 < s.re := by linarith
  have hre0 : 0 < s.re := by linarith
  rw [logDeriv_xi_split hre, logDeriv_Gammaℝ_digamma hre0]
  have h1 : ‖s⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv]
    have : 2 ≤ ‖s‖ := by have := Complex.re_le_norm s; linarith
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; simpa using this
  have h2 : ‖(s - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have : 1 ≤ ‖s - 1‖ := by
      have := Complex.re_le_norm (s - 1); simp at this; linarith
    exact inv_le_one_of_one_le₀ this
  have hhalfre : 1 ≤ (s / 2).re := by simp; linarith
  have h3 : ‖Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2‖
      ≤ (Real.log (‖s‖ / 2 + 3) + digammaLineOneConstant) / 2 + Real.log Real.pi / 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    gcongr
    refine (norm_digamma_le_of_one_le_re hhalfre).trans ?_
    have : Real.log (‖s / 2‖ + 2) ≤ Real.log (‖s‖ / 2 + 3) := by
      apply Real.log_le_log (by positivity)
      rw [norm_div, Complex.norm_ofNat]; linarith
    linarith
  have h4 := norm_logDeriv_zeta_le_of_two_le_re hs
  calc ‖s⁻¹ + (s - 1)⁻¹ + (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2)
        + logDeriv riemannZeta s‖
      ≤ ‖s⁻¹‖ + ‖(s - 1)⁻¹‖ + ‖Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2‖
        + ‖logDeriv riemannZeta s‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 1 / 2 + 1 + ((Real.log (‖s‖ / 2 + 3) + digammaLineOneConstant) / 2 + Real.log Real.pi / 2)
        + vonMangoldtSquareMass := by gcongr
    _ ≤ xiLineTwoLogDerivConstant + Real.log (‖s‖ / 2 + 3) := by
        rw [xiLineTwoLogDerivConstant]
        have : 0 ≤ Real.log (‖s‖ / 2 + 3) := Real.log_nonneg (by linarith [norm_nonneg s])
        linarith

/-- **`‖ξ'/ξ(2 + it)‖ ≤ C + log(|t| + 4)`** for every real `t`. -/
theorem norm_logDeriv_xi_lineTwo_le (t : ℝ) :
    ‖logDeriv xi (lineTwo t)‖ ≤ xiLineTwoLogDerivConstant + Real.log (|t| + 4) := by
  refine (norm_logDeriv_xi_le_of_two_le_re (by rw [lineTwo_eq]; simp)).trans ?_
  have hn : ‖lineTwo t‖ ≤ 2 + |t| := by
    rw [lineTwo_eq]
    calc ‖((2 : ℝ) : ℂ) + t * I‖ ≤ ‖((2 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |t| := by simp
  have : Real.log (‖lineTwo t‖ / 2 + 3) ≤ Real.log (|t| + 4) :=
    Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
  linarith

/-- **The Lorentzian zero mass is `O(log |t|)`**: `Σ_ρ 1/(1 + (t − γ)²) ≤ 8 (C + log(|t| + 4))`. -/
theorem lorentzMass_le_log (t : ℝ) :
    lorentzMass t ≤ 8 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) :=
  (lorentzMass_le_norm_logDeriv_xi t).trans (by gcongr; exact norm_logDeriv_xi_lineTwo_le t)

/-! ## The width-`w` mass and the one-sided tails -/

/-- The generic reflection bound: a non-negative summable family dominated by
`c · Re (s − ρ)⁻¹` has sum at most `2c · Re ξ'/ξ(s)`, for `Re s ≥ 1`. -/
theorem tsum_le_re_logDeriv_xi_of_le {s : ℂ} (hs : 1 ≤ s.re) {c : ℝ} (hc : 0 ≤ c)
    (f : XiZeroCopy → ℝ) (hf : Summable f)
    (hfle : ∀ q : XiZeroCopy, f q ≤ c * ((s - (q.1 : ℂ))⁻¹).re) :
    ∑' q : XiZeroCopy, f q ≤ 2 * c * (logDeriv xi s).re := by
  have hxi : xi s ≠ 0 := xi_ne_zero_of_one_le_re hs
  have hB := summable_partialFractionTerm hxi
  have hBre : Summable (fun q : XiZeroCopy => (partialFractionSummand s q).re) :=
    (Complex.hasSum_re hB.hasSum).summable
  have hBre' : Summable (fun q : XiZeroCopy =>
      (partialFractionSummand s (xiZeroCopyReflectEquiv q)).re) :=
    (xiZeroCopyReflectEquiv.summable_iff
      (f := fun q : XiZeroCopy => (partialFractionSummand s q).re)).mpr hBre
  have hpt : ∀ q : XiZeroCopy, f q ≤
      c * ((partialFractionSummand s q).re
        + (partialFractionSummand s (xiZeroCopyReflectEquiv q)).re) := by
    intro q
    have h1 := hfle q
    have h2 : 0 ≤ ((s - 1 + (q.1 : ℂ))⁻¹).re := by
      apply re_inv_nonneg_of_re_nonneg
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re]
      linarith [xiZeroCopy_re_pos q]
    have h3 : (partialFractionSummand s q).re
        + (partialFractionSummand s (xiZeroCopyReflectEquiv q)).re
        = ((s - (q.1 : ℂ))⁻¹).re + ((s - 1 + (q.1 : ℂ))⁻¹).re := by
      rw [← Complex.add_re, partialFractionSummand_add_reflect, Complex.add_re]
    rw [h3]; nlinarith
  have hsum : Summable (fun q : XiZeroCopy => c * ((partialFractionSummand s q).re
      + (partialFractionSummand s (xiZeroCopyReflectEquiv q)).re)) :=
    (hBre.add hBre').mul_left c
  calc ∑' q : XiZeroCopy, f q ≤ ∑' q : XiZeroCopy, c * ((partialFractionSummand s q).re
        + (partialFractionSummand s (xiZeroCopyReflectEquiv q)).re) :=
        Summable.tsum_le_tsum hpt hf hsum
    _ = c * ((∑' q : XiZeroCopy, (partialFractionSummand s q).re)
        + ∑' q : XiZeroCopy, (partialFractionSummand s (xiZeroCopyReflectEquiv q)).re) := by
        rw [tsum_mul_left, hBre.tsum_add hBre']
    _ = 2 * c * ∑' q : XiZeroCopy, (partialFractionSummand s q).re := by
        rw [xiZeroCopyReflectEquiv.tsum_eq
          (fun q : XiZeroCopy => (partialFractionSummand s q).re)]
        ring
    _ = 2 * c * (logDeriv xi s).re := by
        rw [logDeriv_xi_eq_partialFraction hxi, Complex.re_tsum hB]
        rfl

/-- The width-`w` mass term `1/(w² + (t − γ)²)`. -/
noncomputable def lorentzMassWTerm (w t : ℝ) (q : XiZeroCopy) : ℝ :=
  1 / (w ^ 2 + (t - (q.1 : ℂ).im) ^ 2)

/-- The width-`w` Lorentzian zero mass `Σ_ρ 1/(w² + (t − γ)²)`. -/
noncomputable def lorentzMassW (w t : ℝ) : ℝ := ∑' q : XiZeroCopy, lorentzMassWTerm w t q

theorem lorentzMassWTerm_nonneg {w : ℝ} (hw : 1 ≤ w) (t : ℝ) (q : XiZeroCopy) :
    0 ≤ lorentzMassWTerm w t q := by
  unfold lorentzMassWTerm
  have : 0 < w ^ 2 := by positivity
  positivity

theorem lorentzMassWTerm_le {w : ℝ} (hw : 1 ≤ w) (t : ℝ) (q : XiZeroCopy) :
    lorentzMassWTerm w t q ≤ lorentzMassTerm t q := by
  unfold lorentzMassWTerm lorentzMassTerm
  have : 1 ≤ w ^ 2 := by nlinarith
  gcongr

theorem summable_lorentzMassWTerm {w : ℝ} (hw : 1 ≤ w) (t : ℝ) :
    Summable (lorentzMassWTerm w t) :=
  Summable.of_nonneg_of_le (lorentzMassWTerm_nonneg hw t) (lorentzMassWTerm_le hw t)
    (summable_lorentzMassTerm t)

/-- The point `1 + w + it`. -/
noncomputable def widthPoint (w t : ℝ) : ℂ := ((1 + w : ℝ) : ℂ) + (t : ℂ) * I

theorem widthPoint_re (w t : ℝ) : (widthPoint w t).re = 1 + w := by simp [widthPoint]

theorem widthPoint_im (w t : ℝ) : (widthPoint w t).im = t := by simp [widthPoint]

theorem norm_widthPoint_le (w t : ℝ) (hw : 0 ≤ w) : ‖widthPoint w t‖ ≤ 1 + w + |t| := by
  calc ‖widthPoint w t‖ ≤ |(widthPoint w t).re| + |(widthPoint w t).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = 1 + w + |t| := by rw [widthPoint_re, widthPoint_im, abs_of_nonneg (by linarith)]

/-- At the point `1 + w + it`, `Re (s − ρ)⁻¹ ≥ (w/4) · 1/(w² + (t − γ)²)` for `w ≥ 1`. -/
theorem lorentzMassWTerm_le_re_inv {w : ℝ} (hw : 1 ≤ w) (t : ℝ) (q : XiZeroCopy) :
    lorentzMassWTerm w t q ≤ (4 / w) * ((widthPoint w t - (q.1 : ℂ))⁻¹).re := by
  have hβ0 := xiZeroCopy_re_pos q
  have hβ1 := xiZeroCopy_re_lt_one q
  have hre : (widthPoint w t - (q.1 : ℂ)).re = 1 + w - (q.1 : ℂ).re := by
    rw [Complex.sub_re, widthPoint_re]
  have him : (widthPoint w t - (q.1 : ℂ)).im = t - (q.1 : ℂ).im := by
    rw [Complex.sub_im, widthPoint_im]
  rw [Complex.inv_re, Complex.normSq_apply, hre, him]
  have hden : 0 < (1 + w - (q.1 : ℂ).re) * (1 + w - (q.1 : ℂ).re)
      + (t - (q.1 : ℂ).im) * (t - (q.1 : ℂ).im) := by
    nlinarith [sq_nonneg (t - (q.1 : ℂ).im)]
  have hw0 : 0 < w := by linarith
  rw [lorentzMassWTerm, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (t - (q.1 : ℂ).im), sq_nonneg ((q.1 : ℂ).re - 1),
    mul_pos hw0 hw0, mul_nonneg hw0.le (sq_nonneg (t - (q.1 : ℂ).im))]

/-- **The width-`w` mass is at most `(8/w) Re ξ'/ξ(1 + w + it)`.** -/
theorem lorentzMassW_le_re_logDeriv_xi {w : ℝ} (hw : 1 ≤ w) (t : ℝ) :
    lorentzMassW w t ≤ (8 / w) * (logDeriv xi (widthPoint w t)).re := by
  have h := tsum_le_re_logDeriv_xi_of_le (s := widthPoint w t) (by rw [widthPoint_re]; linarith)
    (c := 4 / w) (by positivity) (lorentzMassWTerm w t) (summable_lorentzMassWTerm hw t)
    (lorentzMassWTerm_le_re_inv hw t)
  rw [lorentzMassW]
  calc ∑' q : XiZeroCopy, lorentzMassWTerm w t q ≤ 2 * (4 / w) * (logDeriv xi (widthPoint w t)).re := h
    _ = (8 / w) * (logDeriv xi (widthPoint w t)).re := by ring

/-- **`Σ_ρ 1/(w² + (t − γ)²) ≤ (8/w)(C + log(w + |t| + 4))`** for `w ≥ 1`. -/
theorem lorentzMassW_le_log {w : ℝ} (hw : 1 ≤ w) (t : ℝ) :
    lorentzMassW w t ≤ (8 / w) * (xiLineTwoLogDerivConstant + Real.log (w + |t| + 4)) := by
  refine (lorentzMassW_le_re_logDeriv_xi hw t).trans ?_
  have hw0 : 0 < w := by linarith
  gcongr
  refine (Complex.re_le_norm _).trans ?_
  refine (norm_logDeriv_xi_le_of_two_le_re (by rw [widthPoint_re]; linarith)).trans ?_
  have hn := norm_widthPoint_le w t hw0.le
  have : Real.log (‖widthPoint w t‖ / 2 + 3) ≤ Real.log (w + |t| + 4) :=
    Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
  linarith

/-- The mass of the zeros above height `T`, seen from `t ≤ T`, is at most the width-`√(1+(T−t)²)`
mass at `T`. -/
theorem tsum_indicator_gt_le_lorentzMassW {t T : ℝ} (htT : t ≤ T) :
    ∑' q : XiZeroCopy, {q : XiZeroCopy | T < (q.1 : ℂ).im}.indicator (lorentzMassTerm t) q
      ≤ lorentzMassW (Real.sqrt (1 + (T - t) ^ 2)) T := by
  have hw : 1 ≤ Real.sqrt (1 + (T - t) ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [sq_nonneg (T - t)]
  refine Summable.tsum_le_tsum (fun q => ?_)
    ((summable_lorentzMassTerm t).indicator _) (summable_lorentzMassWTerm hw T)
  classical
  unfold Set.indicator
  split_ifs with h
  · simp only [Set.mem_setOf_eq] at h
    unfold lorentzMassTerm lorentzMassWTerm
    rw [Real.sq_sqrt (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr h.le) (sub_nonneg.mpr htT)]
  · exact lorentzMassWTerm_nonneg hw T q

/-- The mass of the zeros below height `0`, seen from `t ≥ 0`, is at most the width-`√(1+t²)`
mass at `0`. -/
theorem tsum_indicator_le_zero_le_lorentzMassW {t : ℝ} (ht : 0 ≤ t) :
    ∑' q : XiZeroCopy, {q : XiZeroCopy | (q.1 : ℂ).im ≤ 0}.indicator (lorentzMassTerm t) q
      ≤ lorentzMassW (Real.sqrt (1 + t ^ 2)) 0 := by
  have hw : 1 ≤ Real.sqrt (1 + t ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [sq_nonneg t]
  refine Summable.tsum_le_tsum (fun q => ?_)
    ((summable_lorentzMassTerm t).indicator _) (summable_lorentzMassWTerm hw 0)
  classical
  unfold Set.indicator
  split_ifs with h
  · simp only [Set.mem_setOf_eq] at h
    unfold lorentzMassTerm lorentzMassWTerm
    rw [Real.sq_sqrt (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_nonneg ht (neg_nonneg.mpr h)]
  · exact lorentzMassWTerm_nonneg hw 0 q

theorem sqrt_one_add_sq_le (u : ℝ) (hu : 0 ≤ u) : Real.sqrt (1 + u ^ 2) ≤ 1 + u := by
  rw [Real.sqrt_le_left (by linarith)]; nlinarith

theorem div_sqrt_one_add_sq_le (u : ℝ) (hu : 0 ≤ u) :
    8 / Real.sqrt (1 + u ^ 2) ≤ 16 / (1 + u) := by
  have hs : (1 + u) / 2 ≤ Real.sqrt (1 + u ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; nlinarith [sq_nonneg (u - 1)]
  have hpos : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_div_iff₀ hpos (by positivity)]
  nlinarith

theorem xiLineTwoLogDerivConstant_nonneg : 0 ≤ xiLineTwoLogDerivConstant := by
  unfold xiLineTwoLogDerivConstant digammaLineOneConstant
  have := vonMangoldtSquareMass_nonneg
  have := Real.log_nonneg (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
  linarith [Real.pi_pos]

/-- **Upper tail.** For `0 ≤ t ≤ T`, `Σ_{γ>T} 1/(1+(t−γ)²) ≤ 16 (C + log(2T + 5)) / (1 + (T − t))`. -/
theorem tsum_indicator_gt_le {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ∑' q : XiZeroCopy, {q : XiZeroCopy | T < (q.1 : ℂ).im}.indicator (lorentzMassTerm t) q
      ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (2 * T + 5)) / (1 + (T - t)) := by
  refine (tsum_indicator_gt_le_lorentzMassW htT).trans ?_
  set u := T - t with hu
  have hu0 : 0 ≤ u := by linarith
  have hw : 1 ≤ Real.sqrt (1 + u ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [sq_nonneg u]
  refine (lorentzMassW_le_log hw T).trans ?_
  have hC0 := xiLineTwoLogDerivConstant_nonneg
  have hC' : 0 ≤ xiLineTwoLogDerivConstant + Real.log (Real.sqrt (1 + u ^ 2) + |T| + 4) := by
    have : 0 ≤ Real.log (Real.sqrt (1 + u ^ 2) + |T| + 4) :=
      Real.log_nonneg (by linarith [Real.sqrt_nonneg (1 + u ^ 2), abs_nonneg T])
    linarith
  have hlog : Real.log (Real.sqrt (1 + u ^ 2) + |T| + 4) ≤ Real.log (2 * T + 5) := by
    apply Real.log_le_log (by positivity)
    have := sqrt_one_add_sq_le u hu0
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h8 := div_sqrt_one_add_sq_le u hu0
  calc 8 / Real.sqrt (1 + u ^ 2) *
        (xiLineTwoLogDerivConstant + Real.log (Real.sqrt (1 + u ^ 2) + |T| + 4))
      ≤ 16 / (1 + u) * (xiLineTwoLogDerivConstant + Real.log (2 * T + 5)) :=
        mul_le_mul h8 (by linarith) hC' (by positivity)
    _ = 16 * (xiLineTwoLogDerivConstant + Real.log (2 * T + 5)) / (1 + u) := by ring

/-- **Lower tail.** For `0 ≤ t ≤ T`, `Σ_{γ≤0} 1/(1+(t−γ)²) ≤ 16 (C + log(2T + 5)) / (1 + t)`. -/
theorem tsum_indicator_le_zero_le {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ∑' q : XiZeroCopy, {q : XiZeroCopy | (q.1 : ℂ).im ≤ 0}.indicator (lorentzMassTerm t) q
      ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (2 * T + 5)) / (1 + t) := by
  refine (tsum_indicator_le_zero_le_lorentzMassW ht).trans ?_
  have hw : 1 ≤ Real.sqrt (1 + t ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [sq_nonneg t]
  refine (lorentzMassW_le_log hw 0).trans ?_
  have hC0 := xiLineTwoLogDerivConstant_nonneg
  have hC' : 0 ≤ xiLineTwoLogDerivConstant + Real.log (Real.sqrt (1 + t ^ 2) + |(0 : ℝ)| + 4) := by
    have : 0 ≤ Real.log (Real.sqrt (1 + t ^ 2) + |(0 : ℝ)| + 4) :=
      Real.log_nonneg (by linarith [Real.sqrt_nonneg (1 + t ^ 2), abs_nonneg (0 : ℝ)])
    linarith
  have hlog : Real.log (Real.sqrt (1 + t ^ 2) + |(0 : ℝ)| + 4) ≤ Real.log (2 * T + 5) := by
    apply Real.log_le_log (by positivity)
    have := sqrt_one_add_sq_le t ht
    rw [abs_zero]
    linarith
  have h8 := div_sqrt_one_add_sq_le t ht
  calc 8 / Real.sqrt (1 + t ^ 2) *
        (xiLineTwoLogDerivConstant + Real.log (Real.sqrt (1 + t ^ 2) + |(0 : ℝ)| + 4))
      ≤ 16 / (1 + t) * (xiLineTwoLogDerivConstant + Real.log (2 * T + 5)) :=
        mul_le_mul h8 (by linarith) hC' (by positivity)
    _ = 16 * (xiLineTwoLogDerivConstant + Real.log (2 * T + 5)) / (1 + t) := by ring

/-- The mass of the zeros at or below height `T`, seen from `t ≥ T`, is at most the
width-`√(1+(t−T)²)` mass at `T`. -/
theorem tsum_indicator_le_le_lorentzMassW {t T : ℝ} (hTt : T ≤ t) :
    ∑' q : XiZeroCopy, {q : XiZeroCopy | (q.1 : ℂ).im ≤ T}.indicator (lorentzMassTerm t) q
      ≤ lorentzMassW (Real.sqrt (1 + (t - T) ^ 2)) T := by
  have hw : 1 ≤ Real.sqrt (1 + (t - T) ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [sq_nonneg (t - T)]
  refine Summable.tsum_le_tsum (fun q => ?_)
    ((summable_lorentzMassTerm t).indicator _) (summable_lorentzMassWTerm hw T)
  classical
  unfold Set.indicator
  split_ifs with h
  · simp only [Set.mem_setOf_eq] at h
    unfold lorentzMassTerm lorentzMassWTerm
    rw [Real.sq_sqrt (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hTt) (sub_nonneg.mpr h)]
  · exact lorentzMassWTerm_nonneg hw T q

/-- **Window seen from above.** For `0 ≤ T ≤ t`,
`Σ_{γ≤T} 1/(1+(t−γ)²) ≤ 16 (C + log(t + 5)) / (1 + (t − T))`. -/
theorem tsum_indicator_le_le {t T : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) :
    ∑' q : XiZeroCopy, {q : XiZeroCopy | (q.1 : ℂ).im ≤ T}.indicator (lorentzMassTerm t) q
      ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (t + 5)) / (1 + (t - T)) := by
  refine (tsum_indicator_le_le_lorentzMassW hTt).trans ?_
  set u := t - T with hu
  have hu0 : 0 ≤ u := by linarith
  have hw : 1 ≤ Real.sqrt (1 + u ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [sq_nonneg u]
  refine (lorentzMassW_le_log hw T).trans ?_
  have hC0 := xiLineTwoLogDerivConstant_nonneg
  have hC' : 0 ≤ xiLineTwoLogDerivConstant + Real.log (Real.sqrt (1 + u ^ 2) + |T| + 4) := by
    have : 0 ≤ Real.log (Real.sqrt (1 + u ^ 2) + |T| + 4) :=
      Real.log_nonneg (by linarith [Real.sqrt_nonneg (1 + u ^ 2), abs_nonneg T])
    linarith
  have hlog : Real.log (Real.sqrt (1 + u ^ 2) + |T| + 4) ≤ Real.log (t + 5) := by
    apply Real.log_le_log (by positivity)
    have := sqrt_one_add_sq_le u hu0
    rw [abs_of_nonneg hT]
    linarith
  have h8 := div_sqrt_one_add_sq_le u hu0
  calc 8 / Real.sqrt (1 + u ^ 2) *
        (xiLineTwoLogDerivConstant + Real.log (Real.sqrt (1 + u ^ 2) + |T| + 4))
      ≤ 16 / (1 + u) * (xiLineTwoLogDerivConstant + Real.log (t + 5)) :=
        mul_le_mul h8 (by linarith) hC' (by positivity)
    _ = 16 * (xiLineTwoLogDerivConstant + Real.log (t + 5)) / (1 + u) := by ring

/-- **Window seen from below.** For `t ≤ 0`,
`Σ_{γ>0} 1/(1+(t−γ)²) ≤ 16 (C + log(|t| + 5)) / (1 + |t|)`. -/
theorem tsum_indicator_gt_zero_le {t : ℝ} (ht : t ≤ 0) :
    ∑' q : XiZeroCopy, {q : XiZeroCopy | 0 < (q.1 : ℂ).im}.indicator (lorentzMassTerm t) q
      ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (|t| + 5)) / (1 + |t|) := by
  refine (tsum_indicator_gt_le_lorentzMassW (T := 0) ht).trans ?_
  have hu0 : 0 ≤ |t| := abs_nonneg t
  have hsq : (0 - t) ^ 2 = |t| ^ 2 := by rw [sq_abs]; ring
  rw [hsq]
  have hw : 1 ≤ Real.sqrt (1 + |t| ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [sq_nonneg |t|]
  refine (lorentzMassW_le_log hw 0).trans ?_
  have hC0 := xiLineTwoLogDerivConstant_nonneg
  have hC' : 0 ≤ xiLineTwoLogDerivConstant + Real.log (Real.sqrt (1 + |t| ^ 2) + |(0 : ℝ)| + 4) := by
    have : 0 ≤ Real.log (Real.sqrt (1 + |t| ^ 2) + |(0 : ℝ)| + 4) :=
      Real.log_nonneg (by linarith [Real.sqrt_nonneg (1 + |t| ^ 2), abs_nonneg (0 : ℝ)])
    linarith
  have hlog : Real.log (Real.sqrt (1 + |t| ^ 2) + |(0 : ℝ)| + 4) ≤ Real.log (|t| + 5) := by
    apply Real.log_le_log (by positivity)
    have := sqrt_one_add_sq_le |t| hu0
    rw [abs_zero]
    linarith
  have h8 := div_sqrt_one_add_sq_le |t| hu0
  calc 8 / Real.sqrt (1 + |t| ^ 2) *
        (xiLineTwoLogDerivConstant + Real.log (Real.sqrt (1 + |t| ^ 2) + |(0 : ℝ)| + 4))
      ≤ 16 / (1 + |t|) * (xiLineTwoLogDerivConstant + Real.log (|t| + 5)) :=
        mul_le_mul h8 (by linarith) hC' (by positivity)
    _ = 16 * (xiLineTwoLogDerivConstant + Real.log (|t| + 5)) / (1 + |t|) := by ring

end RHTower
