import GaloisForLFunctions.RHTower.SelbergCuspSpectrumRadius
import GaloisForLFunctions.RHTower.SelbergStripPolynomialGrowth
import GaloisForLFunctions.SelbergClass.ComplexRayMellinInversionGeneralLine

/-!
# Mellin–Barnes representation of the theta function on the imaginary axis

For a class member `F` of positive degree `d`, a height `y > 0` and a line `Re w = c > 0` with
`Re s + c/d > 1`,

```text
Φ_F(s, iy) = (1/2π) ∫ (2πy)^{-(c+it)} Γ(c+it) F(s + (c+it)/d) dt
```

(`ExtendedSelbergClass.theta_imag_eq_mellinBarnes`).  Each term `e^{-2πy n^{1/d}}` is the inverse
Mellin transform of `Γ` on the line; the power `(2πy n^{1/d})^{-w}` factors into
`(2πy)^{-w} n^{-w/d}`; and the sum over `n` passes under the integral because
`Σ |a(n)| n^{-Re s - c/d}` converges.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.SelbergClass

namespace RHTower

noncomputable section

/-- A complex power of a positive real is the exponential of its real logarithm. -/
theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (r : ℂ) ^ z = Complex.exp ((Real.log r : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.ofReal_log hr.le]

/-- A positive real power splits over a product of positive reals. -/
theorem ofReal_mul_rpow_cpow_neg {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) (d : ℝ) (w : ℂ) :
    (((x * (n : ℝ) ^ (1 / d) : ℝ)) : ℂ) ^ (-w) = (x : ℂ) ^ (-w) * (n : ℂ) ^ (-(w / d)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnd : (0 : ℝ) < (n : ℝ) ^ (1 / d) := Real.rpow_pos_of_pos hnR _
  rw [ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp hx,
    show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, ofReal_cpow_eq_exp hnR, ← Complex.exp_add,
    Real.log_mul hx.ne' hnd.ne', Real.log_rpow hnR]
  congr 1
  push_cast
  ring

/-- The Mellin–Barnes line `c + it`. -/
def mellinLine (c t : ℝ) : ℂ := (c : ℂ) + (t : ℂ) * I

theorem mellinLine_re (c t : ℝ) : (mellinLine c t).re = c := by simp [mellinLine]

theorem re_add_mellinLine_div (s : ℂ) (c t d : ℝ) :
    (s + mellinLine c t / (d : ℂ)).re = s.re + c / d := by
  rw [Complex.add_re, Complex.div_ofReal_re, mellinLine_re]

/-- One term of the Mellin–Barnes integrand. -/
def thetaMellinTerm (F : ExtendedSelbergClass) (s : ℂ) (y c : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  if n = 0 then 0 else
    (F.coeff n : ℂ) * (n : ℂ) ^ (-(s + mellinLine c t / (F.gammaData.degree : ℂ))) *
      (((2 * Real.pi * y : ℝ)) : ℂ) ^ (-mellinLine c t) * Complex.Gamma (mellinLine c t)

theorem norm_thetaMellinTerm (F : ExtendedSelbergClass) (s : ℂ) {y c : ℝ} (hy : 0 < y)
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖thetaMellinTerm F s y c n t‖ =
      ‖(F.coeff n : ℂ)‖ * (n : ℝ) ^ (-(s.re + c / F.gammaData.degree)) *
        (2 * Real.pi * y) ^ (-c) * ‖Complex.Gamma (mellinLine c t)‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (0 : ℝ) < 2 * Real.pi * y := by positivity
  rw [thetaMellinTerm, if_neg hn.ne', norm_mul, norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos hn, Complex.norm_cpow_eq_rpow_re_of_pos h2]
  congr 3
  · rw [Complex.neg_re, re_add_mellinLine_div]
  · rw [Complex.neg_re, mellinLine_re]

/-- **Termwise Mellin inversion.** -/
theorem thetaTerm_imag_eq_integral (F : ExtendedSelbergClass) (s : ℂ) {y c : ℝ} (hy : 0 < y)
    (hc : 0 < c) (n : ℕ) :
    thetaTerm (fun n => F.coeff n) F.gammaData.degree s ((y : ℂ) * I) n =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, thetaMellinTerm F s y c n t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [thetaMellinTerm]
  set d := F.gammaData.degree
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set x : ℝ := 2 * Real.pi * y * (n : ℝ) ^ (1 / d) with hx
  have hxpos : 0 < x := by positivity
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * I * ((y : ℂ) * I) *
      (((n : ℝ) ^ (1 / d) : ℝ) : ℂ)) = Complex.exp (-(x : ℂ)) := by
    congr 1
    rw [hx]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hinv := complexMellinInvLine_Gamma_ofReal hc hxpos
  rw [thetaTerm, if_neg hn.ne', hexp, ← hinv, complexMellinInvLine]
  rw [Complex.real_smul, Complex.real_smul, ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  congr 1
  funext t
  rw [thetaMellinTerm, if_neg hn.ne']
  have hsplit := ofReal_mul_rpow_cpow_neg (x := 2 * Real.pi * y) (by positivity) hn d
    ((c : ℂ) + (t : ℂ) * I)
  rw [show (x : ℂ) = (((2 * Real.pi * y * (n : ℝ) ^ (1 / d) : ℝ)) : ℂ) from rfl, hsplit]
  have hpow : (n : ℂ) ^ (-s) * (n : ℂ) ^ (-(((c : ℂ) + (t : ℂ) * I) / (d : ℂ))) =
      (n : ℂ) ^ (-(s + mellinLine c t / (d : ℂ))) := by
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]
    congr 1
    simp only [mellinLine]
    ring
  rw [← hpow]
  simp only [mellinLine]
  ring

theorem continuous_mellinLine (c : ℝ) : Continuous (mellinLine c) := by
  unfold mellinLine; fun_prop

theorem integrable_norm_Gamma_mellinLine {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => ‖Complex.Gamma (mellinLine c t)‖) := by
  have h := gamma_verticalIntegrable_of_pos hc
  exact h.norm

theorem aestronglyMeasurable_thetaMellinTerm (F : ExtendedSelbergClass) (s : ℂ) {y c : ℝ}
    (hy : 0 < y) (hc : 0 < c) (n : ℕ) :
    AEStronglyMeasurable (thetaMellinTerm F s y c n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : thetaMellinTerm F s y c 0 = fun _ => 0 := by
      funext t; simp [thetaMellinTerm]
    rw [h0]
    exact aestronglyMeasurable_const
  have hΓ : Continuous fun t : ℝ => Complex.Gamma (mellinLine c t) :=
    continuous_Gamma_line_of_pos hc |>.congr fun t => by simp [mellinLine]
  have h2 : (((2 * Real.pi * y : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi * y).ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcont : Continuous (thetaMellinTerm F s y c n) := by
    have heq : thetaMellinTerm F s y c n = fun t =>
        (F.coeff n : ℂ) * (n : ℂ) ^ (-(s + mellinLine c t / (F.gammaData.degree : ℂ))) *
          (((2 * Real.pi * y : ℝ)) : ℂ) ^ (-mellinLine c t) * Complex.Gamma (mellinLine c t) := by
      funext t; rw [thetaMellinTerm, if_neg hn.ne']
    rw [heq]
    refine ((continuous_const.mul ?_).mul ?_).mul hΓ
    · exact continuous_const.cpow
        ((continuous_const.add ((continuous_mellinLine c).div_const _)).neg)
        fun _ => Or.inl (by exact_mod_cast hn)
    · exact continuous_const.cpow ((continuous_mellinLine c).neg) fun _ => Or.inl (by
        have : (0 : ℝ) < 2 * Real.pi * y := by positivity
        simpa using this)
  exact hcont.aestronglyMeasurable

theorem integrable_thetaMellinTerm (F : ExtendedSelbergClass) (s : ℂ) {y c : ℝ}
    (hy : 0 < y) (hc : 0 < c) (n : ℕ) :
    Integrable (thetaMellinTerm F s y c n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : thetaMellinTerm F s y c 0 = fun _ => 0 := by
      funext t; simp [thetaMellinTerm]
    rw [h0]
    exact integrable_zero _ _ _
  refine Integrable.mono' ((integrable_norm_Gamma_mellinLine hc).const_mul
    (‖(F.coeff n : ℂ)‖ * (n : ℝ) ^ (-(s.re + c / F.gammaData.degree)) *
      (2 * Real.pi * y) ^ (-c))) (aestronglyMeasurable_thetaMellinTerm F s hy hc n) ?_
  exact Filter.Eventually.of_forall fun t => by
    rw [norm_thetaMellinTerm F s hy hn t]

theorem integral_norm_thetaMellinTerm (F : ExtendedSelbergClass) (s : ℂ) {y : ℝ} (c : ℝ)
    (hy : 0 < y) (n : ℕ) :
    ∫ t : ℝ, ‖thetaMellinTerm F s y c n t‖ =
      ‖LSeries.term (fun n => (F.coeff n : ℂ)) ((s.re + c / F.gammaData.degree : ℝ) : ℂ) n‖ *
        ((2 * Real.pi * y) ^ (-c) * ∫ t : ℝ, ‖Complex.Gamma (mellinLine c t)‖) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [thetaMellinTerm]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp_rw [norm_thetaMellinTerm F s hy hn]
  rw [MeasureTheory.integral_const_mul, LSeries.norm_term_eq, if_neg hn.ne', Complex.ofReal_re,
    Real.rpow_neg hnR.le]
  ring

/-- **The Mellin–Barnes representation of the theta function on the imaginary axis.** -/
theorem ExtendedSelbergClass.theta_imag_eq_mellinBarnes (F : ExtendedSelbergClass)
    (s : ℂ) {y c : ℝ} (hy : 0 < y) (hc : 0 < c)
    (hsc : 1 < s.re + c / F.gammaData.degree) :
    thetaSeries (fun n => F.coeff n) F.gammaData.degree s ((y : ℂ) * I) =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (((2 * Real.pi * y : ℝ)) : ℂ) ^ (-mellinLine c t) * Complex.Gamma (mellinLine c t) *
          F (s + mellinLine c t / (F.gammaData.degree : ℂ)) := by
  have hsumm : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n => (F.coeff n : ℂ)) ((s.re + c / F.gammaData.degree : ℝ) : ℂ) n‖) :=
    (F.lSeriesSummable _ (by simpa using hsc)).norm
  have hint := integrable_thetaMellinTerm F s hy hc
  have hsumint : Summable (fun n : ℕ => ∫ t : ℝ, ‖thetaMellinTerm F s y c n t‖) := by
    simp_rw [integral_norm_thetaMellinTerm F s c hy]
    exact hsumm.mul_right _
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hint hsumint
  rw [thetaSeries]
  simp_rw [thetaTerm_imag_eq_integral F s hy hc]
  rw [tsum_const_smul'' (g := (1 / (2 * Real.pi) : ℝ)), hswap]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  -- the summed integrand
  have hre : 1 < (s + mellinLine c t / (F.gammaData.degree : ℂ)).re := by
    rw [re_add_mellinLine_div]; exact hsc
  have hval := F.lSeries_eq_value _ hre
  change ∑' n : ℕ, thetaMellinTerm F s y c n t = _
  have hterm : ∀ n : ℕ, thetaMellinTerm F s y c n t =
      (((2 * Real.pi * y : ℝ)) : ℂ) ^ (-mellinLine c t) * Complex.Gamma (mellinLine c t) *
        LSeries.term (fun n => (F.coeff n : ℂ))
          (s + mellinLine c t / (F.gammaData.degree : ℂ)) n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [thetaMellinTerm]
    rw [thetaMellinTerm, if_neg hn.ne', LSeries.term_of_ne_zero hn.ne', Complex.cpow_neg,
      div_eq_mul_inv]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  congr 1

end

end RHTower
