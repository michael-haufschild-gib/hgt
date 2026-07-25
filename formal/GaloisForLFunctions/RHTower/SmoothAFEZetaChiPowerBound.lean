/-
# Quantitative power decay of the zeta functional-equation factor

The existing right-half-strip theorem records only `|χ|≤1`.  Smooth AFE
localization needs the power of the height.  Integrating the unconditional
vertical digamma lower bound gives the explicit estimate

`|χ(σ+it)| ≤ exp((σ-1/2)(log π-log(t/2)+E(t)))`

for `1/2≤σ<1`, where `E(t)=1/(t/2)^2+π/(2(t/2))`.
-/
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualContourLimit

namespace RHTower

open Complex Set intervalIntegral MeasureTheory Real

noncomputable section

/-- Quantitative version of right-half-strip decay. -/
theorem norm_zetaChi_le_right_line_exp
    {σ t : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ < 1) (ht : 0 < t) :
    ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      Real.exp ((σ - 1 / 2) *
        (Real.log Real.pi - Real.log (t / 2) +
          (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))))) := by
  set z : ℂ := (σ : ℂ) + (t : ℂ) * I with hzdef
  set a : ℝ := (1 - σ) / 2 with hadef
  set b : ℝ := σ / 2 with hbdef
  set y : ℝ := t / 2 with hydef
  have hy0 : 0 < y := by rw [hydef]; linarith
  have ha0 : 0 ≤ a := by rw [hadef]; linarith
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have hba : b - a = σ - 1 / 2 := by rw [hadef, hbdef]; ring
  have hzre : z.re = σ := by rw [hzdef]; simp
  have h1z : (1 - z) / 2 = (a : ℂ) - (y : ℂ) * I := by
    rw [hzdef, hadef, hydef]
    push_cast
    ring
  have hnorm1 :
      ‖Complex.Gamma ((1 - z) / 2)‖ =
        ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by
    rw [h1z, show
      (a : ℂ) - (y : ℂ) * I =
        (starRingEnd ℂ) ((a : ℂ) + (y : ℂ) * I) by
          rw [map_add, map_mul, Complex.conj_ofReal,
            Complex.conj_ofReal, Complex.conj_I]
          ring,
      Complex.Gamma_conj, RCLike.norm_conj]
  have h2z : z / 2 = (b : ℂ) + (y : ℂ) * I := by
    rw [hzdef, hbdef, hydef]
    push_cast
    ring
  have hnorm2 :
      ‖Complex.Gamma (z / 2)‖ =
        ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ := by
    rw [h2z]
  have hGammaNe :
      ∀ w : ℝ, Complex.Gamma ((w : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro w
    apply Complex.Gamma_ne_zero
    intro m hm
    have him := congrArg Complex.im hm
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_zero, mul_one,
      zero_add, add_zero, Complex.neg_im, Complex.natCast_im, neg_zero] at him
    linarith
  have hga : 0 < ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ :=
    norm_pos_iff.mpr (hGammaNe a)
  have hgb : 0 < ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ :=
    norm_pos_iff.mpr (hGammaNe b)
  let E : ℝ := 1 / y ^ 2 + Real.pi / (2 * y)
  have hftc := ftc_log_norm_Gamma (a := a) (b := b) hy0
  have hintge :
      (b - a) * (Real.log y - E) ≤
        ∫ x in a..b,
          (Complex.digamma ((x : ℂ) + (y : ℂ) * I)).re := by
    have hconst :
        ∫ _x in a..b, (Real.log y - E) =
          (b - a) * (Real.log y - E) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hconst]
    apply intervalIntegral.integral_mono_on hab
    · exact intervalIntegral.intervalIntegrable_const
    · apply ContinuousOn.intervalIntegrable
      have hφ :
          ContinuousOn (fun x : ℝ => (x : ℂ) + (y : ℂ) * I)
            (Set.uIcc a b) := by fun_prop
      have hmaps :
          Set.MapsTo (fun x : ℝ => (x : ℂ) + (y : ℂ) * I)
            (Set.uIcc a b) {z : ℂ | 0 < z.im} := by
        intro x _
        simp only [Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.I_im, Complex.ofReal_re, Complex.I_re,
          mul_zero, mul_one, zero_add, add_zero]
        exact hy0
      exact Complex.continuous_re.comp_continuousOn
        (digamma_continuousOn_uhp.comp hφ hmaps)
    · intro x hx
      rw [Set.mem_Icc] at hx
      have hbound := re_digamma_ge (by linarith [ha0, hx.1]) hy0
      simpa [E] using hbound
  have hlogratio :
      (σ - 1 / 2) * (Real.log y - E) ≤
        Real.log ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ -
          Real.log ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by
    rw [← hftc, ← hba]
    exact hintge
  rw [norm_zetaChi_eq z, hnorm1, hnorm2, hzre]
  have hpi :
      Real.pi ^ (σ - 1 / 2) =
        Real.exp ((σ - 1 / 2) * Real.log Real.pi) := by
    rw [Real.rpow_def_of_pos Real.pi_pos]
    ring_nf
  have hexpr :
      Real.pi ^ (σ - 1 / 2) *
          ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ =
        Real.exp ((σ - 1 / 2) * Real.log Real.pi +
          (Real.log ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ -
            Real.log ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖)) := by
    rw [Real.exp_add, hpi, Real.exp_sub, Real.exp_log hga,
      Real.exp_log hgb]
    ring
  rw [hexpr]
  apply Real.exp_le_exp.mpr
  change
    (σ - 1 / 2) * Real.log Real.pi +
        (Real.log ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ -
          Real.log ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖) ≤
      (σ - 1 / 2) *
        (Real.log Real.pi - Real.log y + E)
  nlinarith [hlogratio]

/-- At height at least `256`, the exponential estimate has the expected
power form. -/
theorem norm_zetaChi_le_right_line_rpow
    {σ t : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ < 1)
    (ht : 256 ≤ t) :
    ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      Real.exp ((σ - 1 / 2) *
          (Real.log Real.pi + Real.log 2 + 2)) *
        t ^ (-(σ - 1 / 2)) := by
  have ht0 : 0 < t := by linarith
  have hhalf : 1 ≤ t / 2 := by linarith
  have hfirst : 1 / (t / 2) ^ 2 ≤ 1 := by
    apply (div_le_one (by positivity)).2
    nlinarith
  have hsecond : Real.pi / (2 * (t / 2)) ≤ 1 := by
    rw [show 2 * (t / 2) = t by ring, div_le_one ht0]
    linarith [Real.pi_lt_four]
  have herror :
      1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2)) ≤ 2 := by
    linarith
  have hlogtwo : Real.log (t / 2) = Real.log t - Real.log 2 := by
    rw [Real.log_div (ne_of_gt ht0) (by norm_num : (2 : ℝ) ≠ 0)]
  have hσnonneg : 0 ≤ σ - 1 / 2 := by linarith
  have hbase := norm_zetaChi_le_right_line_exp hσ1 hσ2 ht0
  calc
    ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        Real.exp ((σ - 1 / 2) *
          (Real.log Real.pi - Real.log (t / 2) +
            (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))))) := hbase
    _ ≤ Real.exp ((σ - 1 / 2) *
          (Real.log Real.pi + Real.log 2 + 2 - Real.log t)) := by
      apply Real.exp_le_exp.mpr
      rw [hlogtwo]
      nlinarith
    _ = Real.exp ((σ - 1 / 2) *
          (Real.log Real.pi + Real.log 2 + 2)) *
        t ^ (-(σ - 1 / 2)) := by
      rw [Real.rpow_def_of_pos ht0, ← Real.exp_add]
      congr 1
      ring

/-- On every fixed line `σ=1/2+δ`, the functional-equation factor has a
global `max(1,|t|)^(-δ)` envelope. -/
theorem exists_norm_zetaChi_fixed_right_line_le_rpow
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      ‖zetaChi (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        K / (max 1 |t|) ^ δ := by
  obtain ⟨C, hC, hglobal⟩ :=
    exists_norm_zetaChi_fixed_right_line_bound
      (σ := 1 / 2 + δ) (by linarith) (by linarith)
  let A : ℝ :=
    Real.exp (δ * (Real.log Real.pi + Real.log 2 + 2))
  let K : ℝ := max A (C * (256 : ℝ) ^ δ)
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hK : 0 ≤ K := hA.le.trans (le_max_left _ _)
  refine ⟨K, hK, fun t => ?_⟩
  rw [norm_zetaChi_real_add_im_eq_abs]
  by_cases ht : 256 ≤ |t|
  · have habs0 : 0 ≤ |t| := abs_nonneg t
    have hbase :=
      norm_zetaChi_le_right_line_rpow
        (σ := 1 / 2 + δ) (t := |t|)
        (by linarith) (by linarith) ht
    have hmax : max 1 |t| = |t| := max_eq_right (by linarith)
    have hbase' :
        ‖zetaChi (((1 / 2 + δ : ℝ) : ℂ) + ((|t| : ℝ) : ℂ) * I)‖ ≤
          A * ((|t| : ℝ) ^ δ)⁻¹ := by
      simpa [A, Real.rpow_neg habs0] using hbase
    rw [hmax, div_eq_mul_inv]
    exact hbase'.trans
      (mul_le_mul_of_nonneg_right (le_max_left A (C * 256 ^ δ))
        (by positivity))
  · have habs : |t| < 256 := lt_of_not_ge ht
    let q : ℝ := max 1 |t|
    have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hq256 : q ≤ 256 := by
      exact max_le (by norm_num) habs.le
    have hqpow :
        q ^ δ ≤ (256 : ℝ) ^ δ :=
      Real.rpow_le_rpow hqpos.le hq256 hδ.le
    have hCq :
        C * q ^ δ ≤ C * (256 : ℝ) ^ δ :=
      mul_le_mul_of_nonneg_left hqpow hC
    have hCK : C * (256 : ℝ) ^ δ ≤ K :=
      le_max_right _ _
    calc
      ‖zetaChi ((((1 / 2 : ℝ) + δ : ℝ) : ℂ) +
          ((abs t : ℝ) : ℂ) * I)‖ ≤ C :=
        hglobal |t|
      _ ≤ K / q ^ δ := by
        apply (le_div_iff₀ (Real.rpow_pos_of_pos hqpos δ)).2
        exact hCq.trans hCK
      _ = K / (max 1 |t|) ^ δ := by rfl

/-- Multiplicative triangle inequality adapted to the global height weight. -/
theorem max_one_abs_le_shift_mul
    (τ v : ℝ) :
    max 1 |τ| ≤ max 1 |τ - v| * (1 + |v|) := by
  let m : ℝ := max 1 |τ - v|
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmd : |τ - v| ≤ m := le_max_right _ _
  have hv0 : 0 ≤ |v| := abs_nonneg v
  have hv : |v| ≤ m * |v| := by
    nlinarith
  have habs : |τ| ≤ |τ - v| + |v| := by
    calc
      |τ| = |(τ - v) + v| := by
        congr 1
        ring_nf
      _ ≤ |τ - v| + |v| := abs_add_le _ _
  apply max_le
  · have hone : 1 ≤ 1 + |v| := by linarith
    exact le_trans hm1 (le_mul_of_one_le_right (by linarith) hone)
  · calc
      |τ| ≤ |τ - v| + |v| := habs
      _ ≤ m + m * |v| := add_le_add hmd hv
      _ = m * (1 + |v|) := by ring

/-- Reciprocal power form of `max_one_abs_le_shift_mul`. -/
theorem one_div_max_one_abs_shift_rpow_le
    {δ : ℝ} (hδ : 0 ≤ δ) (τ v : ℝ) :
    1 / (max 1 |τ - v|) ^ δ ≤
      (1 + |v|) ^ δ / (max 1 |τ|) ^ δ := by
  have hleftPos : 0 < max 1 |τ - v| :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hrightPos : 0 < max 1 |τ| :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hvPos : 0 < 1 + |v| := by positivity
  have hpow :=
    Real.rpow_le_rpow hrightPos.le
      (max_one_abs_le_shift_mul τ v) hδ
  rw [Real.mul_rpow hleftPos.le hvPos.le] at hpow
  apply (div_le_div_iff₀
    (Real.rpow_pos_of_pos hleftPos δ)
    (Real.rpow_pos_of_pos hrightPos δ)).2
  simpa [mul_comm] using hpow

/-- Uniform shifted-ratio bound on the negative contour used for the
small-scale dual cutoff. -/
theorem exists_norm_smoothAFEZetaChiShiftRatio_pos_le
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ v : ℝ),
      ‖smoothAFEZetaChiShiftRatio (linePt τ)
          (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        K * (1 + |v|) ^ δ / (max 1 |τ|) ^ δ := by
  obtain ⟨K, hK, hchi⟩ :=
    exists_norm_zetaChi_fixed_right_line_le_rpow hδ hδhalf
  refine ⟨K, hK, fun τ v => ?_⟩
  have harg :
      linePt τ + -(((-δ : ℝ) : ℂ) + (v : ℂ) * I) =
        (((1 / 2 + δ : ℝ) : ℂ) +
          ((τ - v : ℝ) : ℂ) * I) := by
    unfold linePt
    push_cast
    ring
  have hbase :
      ‖smoothAFEZetaChiShiftRatio (linePt τ)
          (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        K / (max 1 |τ - v|) ^ δ := by
    unfold smoothAFEZetaChiShiftRatio
    rw [norm_div, norm_zetaChi_line, div_one, harg]
    exact hchi (τ - v)
  have hgeom :=
    one_div_max_one_abs_shift_rpow_le hδ.le τ v
  calc
    ‖smoothAFEZetaChiShiftRatio (linePt τ)
        (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        K / (max 1 |τ - v|) ^ δ := hbase
    _ ≤ K * ((1 + |v|) ^ δ / (max 1 |τ|) ^ δ) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hgeom hK
    _ = K * (1 + |v|) ^ δ / (max 1 |τ|) ^ δ := by ring

end

end RHTower
