import GaloisForLFunctions.RHTower.RiemannHypothesisZetaGrowth
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.RieszFunctionMellinCriterion
import GaloisForLFunctions.HTGeometry.SmoothedPerronContourShift

/-!
# Riesz means of `1/ζ` under RH: the Perron contour shift

Let `X = N + ½` and `Q_N(z) = Σ_{n ≤ N} μ(n)(1 − n/X) n^{−z}` (`moebiusRieszPoly`).  For `c > 0` and
`Re z + c > 1`,

`Q_N(z) = (1/2πi) ∫_{(c)} X^w/(w(w + 1)) · (1/ζ)(z + w) dw`

(`moebiusRieszPoly_eq_verticalIntegral'`): expand `1/ζ = Σ μ(n) n^{−s}`, exchange sum and integral,
and evaluate each term with the Perron kernel `(1/2πi)∫ x^w/(w(w + 1)) dw = (1 − 1/x)₊`.

Under RH, `(u − 1)/((u − 1)ζ(u))` (`invZetaCont`) is holomorphic on `Re u > ½` and
`|1/ζ(σ + iv)| ≪ (|v| + 3)^ε` there.  Shifting the integral to `Re w = −δ/2` past the simple pole at
`w = 0` (residue `1/ζ(z)`) gives, for `0 < δ < 1`, `0 < ε < 1`,

`|Q_N(½ + δ + it) − 1/ζ(½ + δ + it)| ≤ C X^{−δ/2} (|t| + 3)^ε`   for all `N`, `t`

(`exists_norm_moebiusRieszPoly_sub_le_of_rh`).
-/

open Complex Set Filter Topology MeasureTheory
open scoped Interval

namespace RHTower

noncomputable section

/-! ## The continuation of `1/ζ` -/

/-- The continuation of `1/ζ`: `(u − 1)/((u − 1)ζ(u))`, with the value `0` at `u = 1`. -/
def invZetaCont (u : ℂ) : ℂ := (u - 1) / zetaResidueUnit u

theorem invZetaCont_eq {u : ℂ} (hu : u ≠ 1) : invZetaCont u = (riemannZeta u)⁻¹ := by
  rw [invZetaCont, (zetaResidueUnit_eventuallyEq hu).eq_of_nhds]
  exact div_mul_cancel_left₀ (sub_ne_zero.mpr hu) _

theorem invZetaCont_eq_LSeries {u : ℂ} (hu : 1 < u.re) :
    invZetaCont u = LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) u := by
  have hu1 : u ≠ 1 := fun h => by rw [h] at hu; norm_num at hu
  rw [invZetaCont_eq hu1]
  exact (eq_inv_of_mul_eq_one_left (LSeries_moebius_mul_riemannZeta hu)).symm

theorem zetaResidueUnit_ne_zero_of_rh (hRH : RiemannHypothesis) {u : ℂ} (hu : 1 / 2 < u.re) :
    zetaResidueUnit u ≠ 0 := by
  by_cases h1 : u = 1
  · rw [h1, zetaResidueUnit_one]; exact one_ne_zero
  rw [(zetaResidueUnit_eventuallyEq h1).eq_of_nhds]
  refine mul_ne_zero (sub_ne_zero.mpr h1) fun hz => ?_
  rcases le_or_gt 1 u.re with h | h
  · exact riemannZeta_ne_zero_of_one_le_re h hz
  · have hre := hRH u hz (fun ⟨n, hn⟩ => by
      have := congrArg Complex.re hn
      simp at this
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) h1
    linarith

theorem differentiableAt_invZetaCont (hRH : RiemannHypothesis) {u : ℂ} (hu : 1 / 2 < u.re) :
    DifferentiableAt ℂ invZetaCont u :=
  (differentiableAt_id.sub_const 1).div (analyticAt_zetaResidueUnit u).differentiableAt
    (zetaResidueUnit_ne_zero_of_rh hRH hu)

/-- Under RH, `|1/ζ(u)| ≤ (|Im u| + 3)^ε` on `½ + d ≤ Re u ≤ 5/2` for large `|Im u|`. -/
theorem exists_norm_invZetaCont_le_of_rh (hRH : RiemannHypothesis) {d : ℝ} (hd : 0 < d)
    (hd1 : d < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ u : ℂ, 1 / 2 + d ≤ u.re → u.re ≤ 5 / 2 → T₀ ≤ |u.im| →
      ‖invZetaCont u‖ ≤ (|u.im| + 3) ^ ε := by
  obtain ⟨T₀, hT₀⟩ := ZetaGrowth.exists_norm_riemannZeta_two_sided hRH hd hd1 hε
  refine ⟨max T₀ 1, le_max_right _ _, fun u hu1 hu2 hT => ?_⟩
  have hu1' : u ≠ 1 := fun h => by
    rw [h] at hT; simp at hT; linarith [le_max_right T₀ 1]
  have h := (hT₀ u.im (le_trans (le_max_left _ _) hT) u.re hu1 hu2).1
  rw [Complex.re_add_im] at h
  have hpos : 0 < (|u.im| + 3) ^ (-ε) := by positivity
  rw [invZetaCont_eq hu1', norm_inv]
  calc ‖riemannZeta u‖⁻¹ ≤ ((|u.im| + 3) ^ (-ε))⁻¹ := inv_anti₀ hpos h
    _ = (|u.im| + 3) ^ ε := by rw [Real.rpow_neg (by positivity), inv_inv]

/-- Under RH, `|1/ζ(σ + iv)| ≤ M (|v| + 3)^ε` for all real `v`, for `½ < σ ≤ 5/2`. -/
theorem exists_norm_invZetaCont_vertical_le_of_rh (hRH : RiemannHypothesis) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ2 : σ ≤ 5 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v : ℝ, ‖invZetaCont ((σ : ℂ) + (v : ℂ) * I)‖ ≤ M * (|v| + 3) ^ ε := by
  set d := min ((σ - 1 / 2)) (1 / 4) with hd
  have hd0 : 0 < d := lt_min (by linarith) (by norm_num)
  have hd1 : d < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨T₀, hT1, hT⟩ := exists_norm_invZetaCont_le_of_rh hRH hd0 hd1 hε
  have hcont : ContinuousOn (fun v : ℝ => invZetaCont ((σ : ℂ) + (v : ℂ) * I)) (Icc (-T₀) T₀) :=
    fun v _ => ((differentiableAt_invZetaCont hRH (by simp; linarith)).continuousAt.comp
      (f := fun v : ℝ => (σ : ℂ) + (v : ℂ) * I) (by fun_prop)).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 1, le_max_of_le_right zero_le_one, fun v => ?_⟩
  have hp1 : 1 ≤ (|v| + 3) ^ ε := Real.one_le_rpow (by linarith [abs_nonneg v]) hε.le
  rcases le_or_gt |v| T₀ with hv | hv
  · calc ‖invZetaCont ((σ : ℂ) + (v : ℂ) * I)‖ ≤ C := hC v (abs_le.mp hv)
      _ ≤ max C 1 := le_max_left _ _
      _ ≤ max C 1 * (|v| + 3) ^ ε := le_mul_of_one_le_right (le_max_of_le_right zero_le_one) hp1
  · have hre : 1 / 2 + d ≤ ((σ : ℂ) + (v : ℂ) * I).re := by
      simp; linarith [min_le_left (σ - 1 / 2) (1 / 4)]
    have h := hT ((σ : ℂ) + (v : ℂ) * I) hre (by simp; exact hσ2) (by simp; exact hv.le)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero] at h
    calc _ ≤ (|v| + 3) ^ ε := h
      _ ≤ max C 1 * (|v| + 3) ^ ε := le_mul_of_one_le_left (by positivity) (le_max_right _ _)

/-! ## The Riesz-smoothed Möbius polynomial and its Perron integral -/

/-- The Perron length `X = N + ½`. -/
def perronLength (N : ℕ) : ℝ := (N : ℝ) + 1 / 2

theorem perronLength_pos (N : ℕ) : 0 < perronLength N := by
  unfold perronLength; positivity

/-- `Q_N(z) = Σ_{n ≤ N} μ(n)(1 − n/X) n^{−z}` with `X = N + ½`. -/
def moebiusRieszPoly (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
    ((1 - (n : ℝ) / perronLength N : ℝ) : ℂ) * (n : ℂ) ^ (-z)

/-- The Perron kernel at `x = X/n`: `1 − n/X` for `n ≤ N` and `0` for `n > N`. -/
theorem verticalIntegral'_perron_f_eq (N : ℕ) {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    VerticalIntegral' (Perron.f (perronLength N / n)) σ =
      if n ≤ N then ((1 - (n : ℝ) / perronLength N : ℝ) : ℂ) else 0 := by
  have hX := perronLength_pos N
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  split_ifs with hnN
  · have hgt : 1 < perronLength N / n := by
      rw [one_lt_div hn0]; unfold perronLength
      have : (n : ℝ) ≤ N := by exact_mod_cast hnN
      linarith
    rw [Perron.formulaGtOne hgt hσ]
    push_cast
    field_simp
  · have hlt : perronLength N / n < 1 := by
      rw [div_lt_one hn0]; unfold perronLength
      have : (N : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.lt_of_not_le hnN)
      linarith
    simp only [VerticalIntegral']
    rw [Perron.formulaLtOne (div_pos hX hn0) hlt hσ, smul_zero]

/-- The `n`-th Perron term `μ(n) n^{−z} f(X/n, w)`. -/
def moebiusPerronTerm (N : ℕ) (z : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  if n = 0 then 0 else
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-z) * Perron.f (perronLength N / n) w

theorem norm_perron_f (x : ℝ) (hx : 0 < x) (w : ℂ) :
    ‖Perron.f x w‖ = x ^ w.re * ‖Perron.f 1 w‖ := by
  simp only [Perron.f, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.ofReal_one,
    Complex.one_cpow, norm_one]
  ring

theorem perron_f_mul_invZetaCont_eq_tsum (N : ℕ) {z w : ℂ} (hzw : 1 < (z + w).re) :
    Perron.f (perronLength N) w * invZetaCont (z + w) = ∑' n, moebiusPerronTerm N z n w := by
  rw [invZetaCont_eq_LSeries hzw, LSeries, ← tsum_mul_left]
  congr 1
  funext n
  unfold moebiusPerronTerm
  split_ifs with hn
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn]
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [← Perron.f_mul_eq_f (perronLength_pos N) hn' w]
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hz : (n : ℂ) ^ z ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
    have hw : (n : ℂ) ^ w ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
    rw [Complex.cpow_add _ _ hnc, Complex.cpow_neg, Complex.cpow_neg]
    push_cast
    field_simp

theorem norm_moebiusPerronTerm_le (N : ℕ) (z : ℂ) (n : ℕ) (w : ℂ) :
    ‖moebiusPerronTerm N z n w‖ ≤
      perronLength N ^ w.re * (n : ℝ) ^ (-(z.re + w.re)) * ‖Perron.f 1 w‖ := by
  have hX := perronLength_pos N
  unfold moebiusPerronTerm
  split_ifs with hn
  · rw [norm_zero]; positivity
  · have hn0 := Nat.pos_of_ne_zero hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [norm_mul, norm_mul, norm_perron_f _ (div_pos hX hn'),
      Complex.norm_natCast_cpow_of_pos hn0, Real.div_rpow hX.le hn'.le]
    have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have heq : perronLength N ^ w.re * (n : ℝ) ^ (-(z.re + w.re)) =
        (n : ℝ) ^ (-z).re * (perronLength N ^ w.re / (n : ℝ) ^ w.re) := by
      rw [Complex.neg_re, Real.rpow_neg hn'.le, Real.rpow_neg hn'.le, Real.rpow_add hn']
      field_simp
    rw [heq]
    have h0 : 0 ≤ (n : ℝ) ^ (-z).re *
        (perronLength N ^ w.re / (n : ℝ) ^ w.re * ‖Perron.f 1 w‖) := by
      positivity
    calc ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ * (n : ℝ) ^ (-z).re *
          (perronLength N ^ w.re / (n : ℝ) ^ w.re * ‖Perron.f 1 w‖)
        ≤ 1 * (n : ℝ) ^ (-z).re * (perronLength N ^ w.re / (n : ℝ) ^ w.re * ‖Perron.f 1 w‖) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right hmu h0
      _ = _ := by ring

/-- **The Perron formula for the Riesz-smoothed Möbius polynomial.**  For `c > 0` and
`Re z + c > 1`, `Q_N(z) = (1/2πi) ∫_{(c)} X^w/(w(w + 1)) · (1/ζ)(z + w) dw`. -/
theorem moebiusRieszPoly_eq_verticalIntegral' (N : ℕ) {z : ℂ} {c : ℝ} (hc : 0 < c)
    (hzc : 1 < z.re + c) :
    moebiusRieszPoly N z =
      VerticalIntegral' (fun w => Perron.f (perronLength N) w * invZetaCont (z + w)) c := by
  have hX := perronLength_pos N
  set L : ℂ → ℂ := fun w => (c : ℂ) + w with hL
  have hint1 : Integrable (fun y : ℝ => Perron.f 1 ((c : ℂ) + (y : ℂ) * I)) :=
    Perron.isIntegrable one_pos hc.ne' (by linarith)
  have hint : ∀ n, Integrable (fun y : ℝ => moebiusPerronTerm N z n ((c : ℂ) + (y : ℂ) * I)) := by
    intro n
    unfold moebiusPerronTerm
    split_ifs with hn
    · exact integrable_zero _ _ _
    · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      exact (Perron.isIntegrable (div_pos hX hn') hc.ne' (by linarith)).const_mul _
  have hre : ∀ y : ℝ, ((c : ℂ) + (y : ℂ) * I).re = c := fun y => by simp
  have hsum : Summable (fun n => ∫ y : ℝ, ‖moebiusPerronTerm N z n ((c : ℂ) + (y : ℂ) * I)‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _)
      (fun n => ?_) (((Real.summable_nat_rpow.mpr (by linarith : -(z.re + c) < -1)).mul_left
        (perronLength N ^ c)).mul_right (∫ y : ℝ, ‖Perron.f 1 ((c : ℂ) + (y : ℂ) * I)‖))
    calc ∫ y : ℝ, ‖moebiusPerronTerm N z n ((c : ℂ) + (y : ℂ) * I)‖
        ≤ ∫ y : ℝ, perronLength N ^ c * (n : ℝ) ^ (-(z.re + c)) *
            ‖Perron.f 1 ((c : ℂ) + (y : ℂ) * I)‖ :=
          integral_mono (hint n).norm (hint1.norm.const_mul _) fun y => by
            have := norm_moebiusPerronTerm_le N z n ((c : ℂ) + (y : ℂ) * I)
            rwa [hre] at this
      _ = _ := integral_const_mul _ _
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hterm : ∀ n, 1 / (2 * (Real.pi : ℂ) * I) *
      (I * ∫ y : ℝ, moebiusPerronTerm N z n ((c : ℂ) + (y : ℂ) * I)) =
      if n ∈ Finset.Icc 1 N then ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
        ((1 - (n : ℝ) / perronLength N : ℝ) : ℂ) * (n : ℂ) ^ (-z) else 0 := by
    intro n
    by_cases hn : n = 0
    · simp [moebiusPerronTerm, hn]
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hP := verticalIntegral'_perron_f_eq N hn1 hc
    simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul] at hP
    simp only [moebiusPerronTerm, hn, if_false]
    rw [integral_const_mul]
    have : 1 / (2 * (Real.pi : ℂ) * I) * (I * (((ArithmeticFunction.moebius n : ℤ) : ℂ) *
        (n : ℂ) ^ (-z) * ∫ y : ℝ, Perron.f (perronLength N / n) ((c : ℂ) + (y : ℂ) * I))) =
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-z) *
          (1 / (2 * (Real.pi : ℂ) * I) *
            (I * ∫ y : ℝ, Perron.f (perronLength N / n) ((c : ℂ) + (y : ℂ) * I))) := by ring
    rw [this, hP]
    simp only [Finset.mem_Icc, hn1, true_and]
    split_ifs <;> ring
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  rw [show (fun y : ℝ => Perron.f (perronLength N) ((c : ℂ) + (y : ℂ) * I) *
      invZetaCont (z + ((c : ℂ) + (y : ℂ) * I))) =
      fun y : ℝ => ∑' n, moebiusPerronTerm N z n ((c : ℂ) + (y : ℂ) * I) from
    funext fun y => perron_f_mul_invZetaCont_eq_tsum N (by simp; linarith)]
  rw [← hswap, ← tsum_mul_left, ← tsum_mul_left]
  simp_rw [← mul_assoc, mul_assoc (1 / (2 * (Real.pi : ℂ) * I)), hterm]
  rw [tsum_eq_sum (s := Finset.Icc 1 N) (fun n hn => by simp [hn]), moebiusRieszPoly]
  exact Finset.sum_congr rfl fun n hn => by simp [hn]

/-! ## Kernel bounds -/

theorem norm_perron_f_one_eq (w : ℂ) : ‖Perron.f 1 w‖ = (‖w‖ * ‖w + 1‖)⁻¹ := by
  simp [Perron.f]

theorem two_mul_norm_ge (w : ℂ) : |w.re| + |w.im| ≤ 2 * ‖w‖ := by
  linarith [Complex.abs_re_le_norm w, Complex.abs_im_le_norm w]

/-- `|f(1, σ + iy)| ≤ 4/(ab) (1 + |y|)^{−2}` when `a ≤ |σ|`, `b ≤ |σ + 1|`, `0 < a, b ≤ 1`. -/
theorem norm_perron_f_one_vertical_le {σ a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b)
    (hb1 : b ≤ 1) (hσa : a ≤ |σ|) (hσb : b ≤ |σ + 1|) (y : ℝ) :
    ‖Perron.f 1 ((σ : ℂ) + (y : ℂ) * I)‖ ≤ 4 / (a * b) * (1 + |y|) ^ (-2 : ℝ) := by
  rw [norm_perron_f_one_eq]
  set w : ℂ := (σ : ℂ) + (y : ℂ) * I with hw
  have h1 := two_mul_norm_ge w
  have h2 := two_mul_norm_ge (w + 1)
  have hwre : w.re = σ := by simp [hw]
  have hwim : w.im = y := by simp [hw]
  rw [hwre, hwim] at h1
  rw [Complex.add_re, Complex.add_im, hwre, hwim] at h2
  simp only [Complex.one_re, Complex.one_im, add_zero] at h2
  have hy0 := abs_nonneg y
  have hA : a * (1 + |y|) ≤ 2 * ‖w‖ := by nlinarith
  have hB : b * (1 + |y|) ≤ 2 * ‖w + 1‖ := by nlinarith
  have hpos : 0 < 1 + |y| := by positivity
  have hprod : a * b * (1 + |y|) ^ 2 ≤ 4 * (‖w‖ * ‖w + 1‖) := by
    have := mul_le_mul hA hB (by positivity) (by positivity)
    nlinarith
  have hprodpos : 0 < ‖w‖ * ‖w + 1‖ := by
    have : 0 < a * b * (1 + |y|) ^ 2 := by positivity
    linarith
  rw [Real.rpow_neg hpos.le, Real.rpow_two]
  rw [inv_le_iff_one_le_mul₀ hprodpos]
  calc (1 : ℝ) = (a * b * (1 + |y|) ^ 2) / (a * b * (1 + |y|) ^ 2) :=
        (div_self (by positivity)).symm
    _ ≤ (4 * (‖w‖ * ‖w + 1‖)) / (a * b * (1 + |y|) ^ 2) :=
        div_le_div_of_nonneg_right hprod (by positivity)
    _ = 4 / (a * b) * ((1 + |y|) ^ 2)⁻¹ * (‖w‖ * ‖w + 1‖) := by field_simp

/-- `|f(1, x + iy)| ≤ 1/y²`. -/
theorem norm_perron_f_one_horizontal_le (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ‖Perron.f 1 ((x : ℂ) + (y : ℂ) * I)‖ ≤ (y ^ 2)⁻¹ := by
  rw [norm_perron_f_one_eq]
  set w : ℂ := (x : ℂ) + (y : ℂ) * I with hw
  have h1 : |y| ≤ ‖w‖ := by simpa [hw] using Complex.abs_im_le_norm w
  have h2 : |y| ≤ ‖w + 1‖ := by simpa [hw] using Complex.abs_im_le_norm (w + 1)
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have : y ^ 2 ≤ ‖w‖ * ‖w + 1‖ := by
    rw [← sq_abs]; nlinarith
  exact inv_anti₀ (by positivity) this

theorem rpow_abs_add_le_mul (t y : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (|t + y| + 3) ^ ε ≤ (|t| + 3) ^ ε * (1 + |y|) ^ ε := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  refine Real.rpow_le_rpow (by positivity) ?_ hε
  have := abs_add_le t y
  nlinarith [abs_nonneg t, abs_nonneg y]

/-! ## The contour shift -/

/-- **Riesz--Perron under RH.**  For `0 < δ < 1` and `0 < ε < 1` there is `C` with
`|Q_N(½ + δ + it) − 1/ζ(½ + δ + it)| ≤ C X^{−δ/2} (|t| + 3)^ε` for all `N` and `t`
(`X = N + ½`).  The Perron integral on `Re w = 1 − δ` is shifted to `Re w = −δ/2` past the simple
pole at `w = 0` with residue `1/ζ(z)`; on the new line `|1/ζ| ≪ (|v| + 3)^ε` by RH. -/
theorem exists_norm_moebiusRieszPoly_sub_le_of_rh (hRH : RiemannHypothesis) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ t : ℝ,
      ‖moebiusRieszPoly N (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) -
          invZetaCont (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        C * perronLength N ^ (-(δ / 2)) * (|t| + 3) ^ ε := by
  set η : ℝ := δ / 2 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η < 1 / 2 := by linarith
  obtain ⟨M, hM0, hM⟩ := exists_norm_invZetaCont_vertical_le_of_rh hRH
    (σ := 1 / 2 + η) (by linarith) (by linarith) hε
  obtain ⟨T₀, hT₀1, hT₀⟩ := exists_norm_invZetaCont_le_of_rh hRH hη0 hη1 one_pos
  set k : ℝ := 4 / (η * (1 - η)) with hk
  have hbase : Integrable fun y : ℝ => (1 + |y|) ^ (-(2 - ε)) := by
    have h : Integrable fun y : ℝ => (1 + ‖y‖) ^ (-(2 - ε)) :=
      integrable_one_add_norm (by simp; linarith)
    exact h.congr (Eventually.of_forall fun y => by simp only [Real.norm_eq_abs])
  set J : ℝ := ∫ y : ℝ, (1 + |y|) ^ (-(2 - ε)) with hJ
  have hk0 : 0 ≤ k := div_nonneg (by norm_num) (mul_nonneg hη0.le (by linarith))
  have hJ0 : 0 ≤ J := integral_nonneg fun y => by positivity
  refine ⟨(2 * Real.pi)⁻¹ * (M * k * J),
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hM0 hk0) hJ0), fun N t => ?_⟩
  set X : ℝ := perronLength N with hX
  have hX0 : 0 < X := perronLength_pos N
  set z : ℂ := ((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I with hz
  have hzre : z.re = 1 / 2 + δ := by simp [hz]
  have hzim : z.im = t := by simp [hz]
  set f : ℂ → ℂ := fun w => Perron.f X w * invZetaCont (z + w) with hf
  have hzw : ∀ w : ℂ, (z + w).re = 1 / 2 + δ + w.re := fun w => by simp [hzre]
  -- holomorphy
  have hfd : ∀ w : ℂ, -η ≤ w.re → w ≠ 0 → DifferentiableAt ℂ f w := by
    intro w hw hw0
    have hw1 : w ≠ -1 := fun h => by rw [h] at hw; simp at hw; linarith
    have hP : DifferentiableAt ℂ (Perron.f X) w := by
      have hopen : IsOpen ({0, -1}ᶜ : Set ℂ) := (Set.toFinite _).isClosed.isOpen_compl
      exact ((Perron.isHolomorphicOn hX0).differentiableAt
        (hopen.mem_nhds (by simp [hw0, hw1])))
    have hI : DifferentiableAt ℂ (fun w => invZetaCont (z + w)) w :=
      (differentiableAt_invZetaCont hRH (by rw [hzw]; linarith)).comp w
        (differentiableAt_id.const_add z)
    exact hP.mul hI
  have hhol : HolomorphicOn f (Set.Icc (-η) (1 - δ) ×ℂ Set.univ \ {0}) := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    rw [Complex.mem_reProdIm] at hw1
    exact (hfd w hw1.1.1 hw2).differentiableWithinAt
  -- the pole
  have hpole : (f - fun w => invZetaCont z / (w - 0)) =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
    have hG : DifferentiableAt ℂ (fun w : ℂ => (X : ℂ) ^ w / (w + 1) * invZetaCont (z + w)) 0 := by
      have h1 : DifferentiableAt ℂ (fun w : ℂ => (X : ℂ) ^ w) 0 :=
        differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hX0.ne'))
      have h2 : DifferentiableAt ℂ (fun w : ℂ => invZetaCont (z + w)) 0 :=
        (differentiableAt_invZetaCont hRH (by rw [hzw]; simp; linarith)).comp 0
          (differentiableAt_id.const_add z)
      exact (h1.div (differentiableAt_id.add_const 1) (by norm_num)).mul h2
    have h := GaloisForLFunctions.HTGeometry.SmoothedPerron.isBigO_div_sub_div hG
    refine h.congr' (Eventually.of_forall fun w => ?_) (Eventually.of_forall fun w => rfl)
    simp only [Pi.sub_apply, hf, Perron.f, Complex.cpow_zero, add_zero, zero_add, sub_zero,
      div_eq_mul_inv, mul_inv]
    ring
  -- horizontal decay
  set T₁ : ℝ := T₀ + |t| + 3 with hT₁
  set B : ℝ := (X ^ (-η) + X ^ (1 - δ)) * 2 with hB
  have hhor : ∀ y : ℝ, T₁ ≤ |y| → ∀ x ∈ Ι (-η) (1 - δ),
      ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * |y|⁻¹ := by
    intro y hy x hx
    rw [uIoc_of_le (by linarith)] at hx
    have hy0 : 0 < |y| := by linarith [abs_nonneg t, hT₀1]
    have hyne : y ≠ 0 := abs_pos.mp hy0
    set w : ℂ := (x : ℂ) + (y : ℂ) * I with hw
    have hwre : w.re = x := by simp [hw]
    have hwim : w.im = y := by simp [hw]
    have hP : ‖Perron.f X w‖ ≤ (X ^ (-η) + X ^ (1 - δ)) * (y ^ 2)⁻¹ := by
      rw [norm_perron_f X hX0, hwre]
      refine mul_le_mul ?_ (norm_perron_f_one_horizontal_le x hyne) (norm_nonneg _)
        (by positivity)
      rcases le_or_gt 1 X with h | h
      · have := Real.rpow_le_rpow_of_exponent_le h hx.2
        linarith [Real.rpow_nonneg hX0.le (-η)]
      · have := Real.rpow_le_rpow_of_exponent_ge hX0 h.le hx.1.le
        linarith [Real.rpow_nonneg hX0.le (1 - δ)]
    have hty : T₀ ≤ |(z + w).im| := by
      rw [Complex.add_im, hzim, hwim]
      have := abs_sub_abs_le_abs_sub y (-t)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      linarith
    have hI := hT₀ (z + w) (by rw [hzw, hwre]; linarith [hx.1]) (by rw [hzw, hwre]; linarith [hx.2])
      hty
    rw [Real.rpow_one, Complex.add_im, hzim, hwim] at hI
    have hI' : ‖invZetaCont (z + w)‖ ≤ 2 * |y| := by
      have := abs_add_le t y
      linarith
    calc ‖f w‖ = ‖Perron.f X w‖ * ‖invZetaCont (z + w)‖ := norm_mul _ _
      _ ≤ (X ^ (-η) + X ^ (1 - δ)) * (y ^ 2)⁻¹ * (2 * |y|) :=
          mul_le_mul hP hI' (norm_nonneg _) (by positivity)
      _ = B * |y|⁻¹ := by
          rw [hB, ← sq_abs y]; field_simp
  have hlimB : Tendsto (fun y : ℝ => B * |y|⁻¹ * |1 - δ - -η|) atTop (𝓝 0) ∧
      Tendsto (fun y : ℝ => B * |y|⁻¹ * |1 - δ - -η|) atBot (𝓝 0) := by
    constructor
    · have := ((tendsto_inv_atTop_zero.comp tendsto_abs_atTop_atTop).const_mul B).mul_const
        |1 - δ - -η|
      simpa using this
    · have := ((tendsto_inv_atTop_zero.comp tendsto_abs_atBot_atTop).const_mul B).mul_const
        |1 - δ - -η|
      simpa using this
  have htop : Tendsto (fun y : ℝ => ∫ x in (-η)..(1 - δ), f ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlimB.1
    filter_upwards [eventually_ge_atTop T₁] with y hy
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hhor y (le_trans hy (le_abs_self y)) x hx
  have hbot : Tendsto (fun y : ℝ => ∫ x in (-η)..(1 - δ), f ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlimB.2
    filter_upwards [eventually_le_atBot (-T₁)] with y hy
    have hy' : T₁ ≤ |y| := by
      rw [abs_of_neg (by linarith [abs_nonneg t, hT₀1])]; linarith
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => hhor y hy' x hx
  -- the left line
  have hleftBound : ∀ y : ℝ, ‖f (((-η : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      X ^ (-η) * (M * k * (|t| + 3) ^ ε) * (1 + |y|) ^ (-(2 - ε)) := by
    intro y
    set w : ℂ := ((-η : ℝ) : ℂ) + (y : ℂ) * I with hw
    have hP : ‖Perron.f X w‖ ≤ X ^ (-η) * (k * (1 + |y|) ^ (-2 : ℝ)) := by
      rw [norm_perron_f X hX0]
      have hre : w.re = -η := by simp [hw]
      rw [hre]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := norm_perron_f_one_vertical_le (σ := -η) (a := η) (b := 1 - η) hη0 (by linarith)
        (by linarith) (by linarith) (by rw [abs_neg, abs_of_pos hη0])
        (by rw [abs_of_pos (by linarith)]; linarith) y
      simpa [hk, hw] using this
    have hzw' : z + w = (((1 / 2 + η : ℝ)) : ℂ) + ((t + y : ℝ) : ℂ) * I := by
      rw [hz, hw, hη]; push_cast; ring
    have hI : ‖invZetaCont (z + w)‖ ≤ M * ((|t| + 3) ^ ε * (1 + |y|) ^ ε) := by
      rw [hzw']
      exact (hM (t + y)).trans (mul_le_mul_of_nonneg_left (rpow_abs_add_le_mul t y hε.le) hM0)
    have hpos : 0 < 1 + |y| := by positivity
    calc ‖f w‖ = ‖Perron.f X w‖ * ‖invZetaCont (z + w)‖ := norm_mul _ _
      _ ≤ X ^ (-η) * (k * (1 + |y|) ^ (-2 : ℝ)) * (M * ((|t| + 3) ^ ε * (1 + |y|) ^ ε)) :=
          mul_le_mul hP hI (norm_nonneg _) (by positivity)
      _ = X ^ (-η) * (M * k * (|t| + 3) ^ ε) * ((1 + |y|) ^ (-2 : ℝ) * (1 + |y|) ^ ε) := by ring
      _ = _ := by rw [← Real.rpow_add hpos]; ring_nf
  have hleftInt : Integrable fun y : ℝ => f (((-η : ℝ) : ℂ) + (y : ℂ) * I) := by
    refine (hbase.const_mul (X ^ (-η) * (M * k * (|t| + 3) ^ ε))).mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun y => ?_)
      have hne : ((-η : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      exact ContinuousAt.comp (g := f) (hfd _ (by simp) hne).continuousAt (by fun_prop)
    · exact Eventually.of_forall hleftBound
  -- the right line
  have hrightInt : Integrable fun y : ℝ => f (((1 - δ : ℝ) : ℂ) + (y : ℂ) * I) := by
    have hint1 : Integrable (fun y : ℝ => Perron.f 1 (((1 - δ : ℝ) : ℂ) + (y : ℂ) * I)) :=
      Perron.isIntegrable one_pos (by linarith) (by linarith)
    set Z : ℝ := ∑' n, ‖LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
      (3 / 2 : ℂ) n‖ with hZ
    refine (hint1.norm.const_mul (X ^ (1 - δ) * Z)).mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun y => ?_)
      have hne : ((1 - δ : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      exact ContinuousAt.comp (g := f) (hfd _ (by simp; linarith) hne).continuousAt
        (by fun_prop)
    · refine Eventually.of_forall fun y => ?_
      set w : ℂ := ((1 - δ : ℝ) : ℂ) + (y : ℂ) * I with hw
      have hre : w.re = 1 - δ := by simp [hw]
      have hzwre : (z + w).re = 3 / 2 := by rw [hzw, hre]; ring
      have hL : ‖invZetaCont (z + w)‖ ≤ Z := by
        rw [invZetaCont_eq_LSeries (by rw [hzwre]; norm_num)]
        refine GaloisForLFunctions.HTGeometry.SmoothedPerron.norm_LSeries_le_of_re
          (fun n => ?_) hzwre
        rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      calc ‖f w‖ = ‖Perron.f X w‖ * ‖invZetaCont (z + w)‖ := norm_mul _ _
        _ = X ^ (1 - δ) * ‖Perron.f 1 w‖ * ‖invZetaCont (z + w)‖ := by
            rw [norm_perron_f X hX0, hre]
        _ ≤ X ^ (1 - δ) * ‖Perron.f 1 w‖ * Z :=
            mul_le_mul_of_nonneg_left hL (by positivity)
        _ = X ^ (1 - δ) * Z * ‖Perron.f 1 w‖ := by ring
  -- assemble
  have hshift := GaloisForLFunctions.HTGeometry.verticalIntegral'_sub_of_simple_pole
    (σ := -η) (σ' := 1 - δ) (p := 0) (A := invZetaCont z) (f := f) (by simp; linarith)
    (by simp; linarith) hhol hpole hbot htop hleftInt hrightInt
  have hPer := moebiusRieszPoly_eq_verticalIntegral' N (z := z) (c := 1 - δ) (by linarith)
    (by rw [hzre]; linarith)
  have hdiff : moebiusRieszPoly N z - invZetaCont z = VerticalIntegral' f (-η) := by
    rw [hPer]; linear_combination hshift
  rw [hdiff]
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hnorm : ‖1 / (2 * (Real.pi : ℂ) * I)‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, one_div]
  rw [hnorm]
  have hint := norm_integral_le_of_norm_le (hbase.const_mul (X ^ (-η) * (M * k * (|t| + 3) ^ ε)))
    (Eventually.of_forall hleftBound)
  rw [integral_const_mul] at hint
  calc (2 * Real.pi)⁻¹ * ‖∫ y : ℝ, f (((-η : ℝ) : ℂ) + (y : ℂ) * I)‖
      ≤ (2 * Real.pi)⁻¹ * (X ^ (-η) * (M * k * (|t| + 3) ^ ε) * J) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (2 * Real.pi)⁻¹ * (M * k * J) * X ^ (-(δ / 2)) * (|t| + 3) ^ ε := by rw [hη]; ring

end

end RHTower
