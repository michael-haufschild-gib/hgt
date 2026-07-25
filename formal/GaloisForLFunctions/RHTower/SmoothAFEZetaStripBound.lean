import GaloisForLFunctions.RHTower.SmoothAFEZetaInfiniteContour
import GaloisForLFunctions.RHTower.RouteBChiDecay
import GaloisForLFunctions.RHTower.FuchsProlateScale

/-!
# Uniform strip bounds for the smooth-AFE horizontal edges

Horizontal-edge decay needs a zeta bound uniform while the real part ranges
from `-1/2` to `3/2`.  The negative part is reduced by the functional equation
to the already formalized square-root zeta estimate.  This file supplies the
missing bounded-width Gamma-ratio estimate for its `χ` factor.
-/

noncomputable section

namespace RHTower

open Complex Set intervalIntegral MeasureTheory Real Filter Topology

/-- On a bounded positive real-part interval, a vertical Gamma quotient with
width at most `1/2` is uniformly bounded once the height is at least one. -/
theorem norm_Gamma_vertical_ratio_le_exp_two
    {a b y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hwidth : b - a ≤ 1 / 2) (hy : 1 ≤ y) :
    ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
        ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ ≤
      Real.exp 2 := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hΓne : ∀ x : ℝ,
      Complex.Gamma ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro x
    apply Complex.Gamma_ne_zero
    intro m h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_zero, mul_one,
      zero_add, add_zero, Complex.neg_im, Complex.natCast_im, neg_zero] at him
    linarith
  have hga : 0 < ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ :=
    norm_pos_iff.mpr (hΓne a)
  have hgb : 0 < ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ :=
    norm_pos_iff.mpr (hΓne b)
  let C : ℝ := 1 / y ^ 2 + Real.pi / (2 * y)
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hCle : C ≤ 3 := by
    have hySq : 1 ≤ y ^ 2 := by nlinarith
    have hone : 1 / y ^ 2 ≤ 1 := by
      exact (div_le_one (by positivity)).2 hySq
    have hpi : Real.pi / (2 * y) ≤ 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * y)).2
      nlinarith [Real.pi_lt_four]
    dsimp only [C]
    linarith
  have hcontinuous :
      IntervalIntegrable
        (fun x : ℝ =>
          (Complex.digamma ((x : ℂ) + (y : ℂ) * I)).re)
        volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hφ : ContinuousOn
        (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (uIcc a b) := by
      fun_prop
    have hmaps : MapsTo
        (fun x : ℝ => (x : ℂ) + (y : ℂ) * I)
        (uIcc a b) {z : ℂ | 0 < z.im} := by
      intro x _
      simp only [mem_setOf_eq, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.I_im, Complex.ofReal_re, Complex.I_re,
        mul_zero, mul_one, zero_add, add_zero]
      exact hy0
    exact Complex.continuous_re.comp_continuousOn
      (digamma_continuousOn_uhp.comp hφ hmaps)
  have hlower :
      (b - a) * (Real.log y - C) ≤
        ∫ x in a..b,
          (Complex.digamma ((x : ℂ) + (y : ℂ) * I)).re := by
    have hconst :
        ∫ _x in a..b, (Real.log y - C) =
          (b - a) * (Real.log y - C) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hconst]
    apply intervalIntegral.integral_mono_on hab
    · exact intervalIntegral.intervalIntegrable_const
    · exact hcontinuous
    · intro x hx
      rw [mem_Icc] at hx
      exact re_digamma_ge (by linarith [ha, hx.1]) hy0
  have hftc := ftc_log_norm_Gamma (a := a) (b := b) hy0
  have hlogratio :
      (b - a) * (Real.log y - C) ≤
        Real.log ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ -
          Real.log ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by
    rw [← hftc]
    exact hlower
  have hwidth0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have hgap1 :
      Real.log ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ -
          Real.log ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ ≤
        (b - a) * (C - Real.log y) := by
    linarith
  have hgap2 : (b - a) * (C - Real.log y) ≤ (b - a) * C := by
    exact mul_le_mul_of_nonneg_left (by linarith) hwidth0
  have hgap3 : (b - a) * C ≤ (1 / 2 : ℝ) * 3 := by
    exact mul_le_mul hwidth hCle hC0 (by norm_num)
  calc
    ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ =
        Real.exp
          (Real.log ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ -
            Real.log ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖) := by
              rw [Real.exp_sub, Real.exp_log hga, Real.exp_log hgb]
    _ ≤ Real.exp 2 := by
      apply Real.exp_le_exp.mpr
      exact hgap1.trans (hgap2.trans <| by linarith [hgap3])

/-- Uniform linear bound for `χ(σ+it)` on the negative half-strip
`-1/2 ≤ σ ≤ 0`, at positive height.  The exact Gamma recurrence moves the
denominator into the right half-plane, after which the bounded-width ratio
estimate applies. -/
theorem norm_zetaChi_le_negative_half_strip
    {σ t : ℝ} (hσlow : -1 / 2 ≤ σ) (hσhigh : σ ≤ 0)
    (ht : 2 ≤ t) :
    ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      Real.exp 2 * (1 + t) := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  let a : ℝ := (1 - σ) / 2
  let b : ℝ := 1 + σ / 2
  let y : ℝ := t / 2
  have hy : 1 ≤ y := by
    dsimp only [y]
    linarith
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    linarith
  have hab : a ≤ b := by
    dsimp only [a, b]
    linarith
  have hwidth : b - a ≤ 1 / 2 := by
    dsimp only [a, b]
    linarith
  have hratio :
      ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ ≤
        Real.exp 2 :=
    norm_Gamma_vertical_ratio_le_exp_two ha0 hab hwidth hy
  have hnumArg :
      (1 - z) / 2 = (a : ℂ) - (y : ℂ) * I := by
    dsimp only [z, a, y]
    push_cast
    ring
  have hnumNorm :
      ‖Complex.Gamma ((1 - z) / 2)‖ =
        ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by
    rw [hnumArg,
      show (a : ℂ) - (y : ℂ) * I =
        (starRingEnd ℂ) ((a : ℂ) + (y : ℂ) * I) by
          apply Complex.ext <;> simp,
      Complex.Gamma_conj, Complex.norm_conj]
  have hshiftArg :
      z / 2 + 1 = (b : ℂ) + (y : ℂ) * I := by
    dsimp only [z, b, y]
    push_cast
    ring
  have hz0 : z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    dsimp only [z] at him
    simp at him
    linarith
  have hzhalf0 : z / 2 ≠ 0 := div_ne_zero hz0 (by norm_num)
  have hrec := Complex.Gamma_add_one (z / 2) hzhalf0
  have hdenNe : Complex.Gamma (z / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    have him := congrArg Complex.im h
    dsimp only [z] at him
    simp at him
    linarith
  have hshiftNe :
      Complex.Gamma ((b : ℂ) + (y : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hdenNormNe : ‖Complex.Gamma (z / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hdenNe
  have hshiftNormNe :
      ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hshiftNe
  have hrecNorm :
      ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ =
        ‖z / 2‖ * ‖Complex.Gamma (z / 2)‖ := by
    rw [← hshiftArg, hrec, norm_mul]
  have hrawRatio :
      ‖Complex.Gamma ((1 - z) / 2)‖ /
          ‖Complex.Gamma (z / 2)‖ =
        ‖z / 2‖ *
          (‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
            ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖) := by
    rw [hnumNorm]
    rw [hrecNorm] at hshiftNormNe ⊢
    field_simp
  have hσabs : |σ| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hzNorm : ‖z‖ ≤ 1 / 2 + t := by
    dsimp only [z]
    calc
      ‖(σ : ℂ) + (t : ℂ) * I‖ ≤
          ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = |σ| + |t| := by
        simp only [norm_mul, norm_I, Complex.norm_real,
          Real.norm_eq_abs, mul_one]
      _ = |σ| + t := by
        have ht0 : 0 ≤ t := by linarith
        rw [abs_of_nonneg ht0]
      _ ≤ 1 / 2 + t := by linarith
  have hzHalfNorm : ‖z / 2‖ ≤ 1 + t := by
    rw [norm_div, Complex.norm_ofNat]
    have ht0 : 0 ≤ t := by linarith
    nlinarith [norm_nonneg z, hzNorm]
  have hpiFactor :
      Real.pi ^ (σ - 1 / 2) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [Real.pi_gt_three]) (by linarith)
  rw [norm_zetaChi_eq z, mul_div_assoc, hrawRatio]
  have hratioNonneg :
      0 ≤ ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
        ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ := by positivity
  calc
    Real.pi ^ (z.re - 1 / 2) *
          (‖z / 2‖ *
            (‖Complex.Gamma (↑a + ↑y * I)‖ /
              ‖Complex.Gamma (↑b + ↑y * I)‖))
        = Real.pi ^ (σ - 1 / 2) *
          (‖z / 2‖ *
            (‖Complex.Gamma (↑a + ↑y * I)‖ /
              ‖Complex.Gamma (↑b + ↑y * I)‖)) := by
            congr 3
            simp [z]
    _ ≤ 1 * ((1 + t) * Real.exp 2) := by
      gcongr
    _ = Real.exp 2 * (1 + t) := by ring

theorem norm_zetaChi_real_add_im_eq_abs (σ t : ℝ) :
    ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ =
      ‖zetaChi ((σ : ℂ) + ((|t| : ℝ) : ℂ) * I)‖ := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · have harg :
        (σ : ℂ) + (t : ℂ) * I =
          (starRingEnd ℂ) ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [abs_of_nonpos ht, harg, zetaChi_conj, Complex.norm_conj]

theorem norm_zetaChi_le_positive_half_strip
    {σ t : ℝ} (hσlow : 0 < σ) (hσhigh : σ ≤ 1 / 2)
    (ht : 2 ≤ t) :
    ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      Real.exp 2 * (1 + t) := by
  have ht0 : 0 < t := by linarith
  have hy : 1 ≤ t / 2 := by linarith
  let C : ℝ := 1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hCle : C ≤ 3 := by
    have hySq : 1 ≤ (t / 2) ^ 2 := by nlinarith
    have hone : 1 / (t / 2) ^ 2 ≤ 1 := by
      exact (div_le_one (by positivity)).2 hySq
    have hpi : Real.pi / (2 * (t / 2)) ≤ 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * (t / 2))).2
      nlinarith [Real.pi_lt_four]
    dsimp only [C]
    linarith
  have harg :
      (1 / 2 : ℝ) ^ 2 + (t / 2) ^ 2 ≤ (1 + t) ^ 2 := by
    nlinarith
  have hlogarg :
      (1 / 2 : ℝ) *
          Real.log ((1 / 2 : ℝ) ^ 2 + (t / 2) ^ 2) ≤
        Real.log (1 + t) := by
    have hlog := Real.log_le_log (by positivity) harg
    have hlogpow :
        Real.log ((1 + t) ^ 2) = 2 * Real.log (1 + t) := by
      rw [Real.log_pow]
      norm_num
    rw [hlogpow] at hlog
    linarith
  have hlogPi : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogOne : 0 ≤ Real.log (1 + t) :=
    Real.log_nonneg (by linarith)
  have hdelta0 : 0 ≤ 1 / 2 - σ := by linarith
  have hdelta : 1 / 2 - σ ≤ 1 / 2 := by linarith
  have hexponent :
      (1 / 2 - σ) *
          ((1 / 2 : ℝ) *
              Real.log ((1 / 2 : ℝ) ^ 2 + (t / 2) ^ 2) +
            (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))) -
            Real.log Real.pi) ≤
        Real.log (1 + t) + 2 := by
    have hinside :
        (1 / 2 : ℝ) *
              Real.log ((1 / 2 : ℝ) ^ 2 + (t / 2) ^ 2) +
            (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))) -
            Real.log Real.pi ≤
          Real.log (1 + t) + 3 := by
      dsimp only [C] at hCle
      linarith
    calc
      (1 / 2 - σ) *
          ((1 / 2 : ℝ) *
              Real.log ((1 / 2 : ℝ) ^ 2 + (t / 2) ^ 2) +
            (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))) -
            Real.log Real.pi)
          ≤ (1 / 2 - σ) * (Real.log (1 + t) + 3) := by
            gcongr
      _ ≤ (1 / 2 : ℝ) * (Real.log (1 + t) + 3) := by
            gcongr
      _ ≤ Real.log (1 + t) + 2 := by linarith
  have hbase :=
    norm_zetaChi_le_left_line hσlow hσhigh ht0
  refine hbase.trans ?_
  calc
    Real.exp
        ((1 / 2 - σ) *
          ((1 / 2 : ℝ) *
              Real.log ((1 / 2 : ℝ) ^ 2 + (t / 2) ^ 2) +
            (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))) -
            Real.log Real.pi))
        ≤ Real.exp (Real.log (1 + t) + 2) :=
          Real.exp_le_exp.mpr hexponent
    _ = Real.exp 2 * (1 + t) := by
      rw [Real.exp_add, Real.exp_log (by linarith : 0 < 1 + t)]
      ring

/-- Uniform `O(1+|t|)` bound for `χ` throughout
`-1/2 ≤ Re s ≤ 1/2`. -/
theorem norm_zetaChi_le_half_strip
    {σ t : ℝ} (hσlow : -1 / 2 ≤ σ) (hσhigh : σ ≤ 1 / 2)
    (ht : 2 ≤ |t|) :
    ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      Real.exp 2 * (1 + |t|) := by
  calc
    ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ =
        ‖zetaChi ((σ : ℂ) + ((|t| : ℝ) : ℂ) * I)‖ :=
      norm_zetaChi_real_add_im_eq_abs σ t
    _ ≤ Real.exp 2 * (1 + |t|) := by
      rcases le_total σ 0 with hσ0 | hσ0
      · exact norm_zetaChi_le_negative_half_strip hσlow hσ0 ht
      · rcases eq_or_lt_of_le hσ0 with rfl | hσpos
        · exact norm_zetaChi_le_negative_half_strip
            (by norm_num) le_rfl ht
        · exact norm_zetaChi_le_positive_half_strip hσpos hσhigh ht

theorem norm_real_add_im_le_three_halves
    {σ t : ℝ} (hσlow : -3 / 2 ≤ σ) (hσhigh : σ ≤ 3 / 2) :
    ‖(σ : ℂ) + (t : ℂ) * I‖ ≤ 3 / 2 + |t| := by
  have hσabs : |σ| ≤ 3 / 2 :=
    (abs_le).2 ⟨by linarith [hσlow], hσhigh⟩
  calc
    ‖(σ : ℂ) + (t : ℂ) * I‖ ≤
        ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
    _ = |σ| + |t| := by
      simp only [norm_mul, norm_I, Complex.norm_real,
        Real.norm_eq_abs, mul_one]
    _ ≤ 3 / 2 + |t| := by linarith

theorem sqrt_norm_real_add_im_add_two_le
    {σ t : ℝ} (hσlow : -3 / 2 ≤ σ) (hσhigh : σ ≤ 3 / 2) :
    Real.sqrt (‖(σ : ℂ) + (t : ℂ) * I‖ + 2) ≤ 4 + |t| := by
  have hnorm := norm_real_add_im_le_three_halves
    (t := t) hσlow hσhigh
  have hone : 1 ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ + 2 := by
    linarith [norm_nonneg ((σ : ℂ) + (t : ℂ) * I)]
  have hself :
      Real.sqrt (‖(σ : ℂ) + (t : ℂ) * I‖ + 2) ≤
        ‖(σ : ℂ) + (t : ℂ) * I‖ + 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  exact hself.trans <| by linarith

/-- Direct square-root zeta bound uniformly on `1/2 ≤ σ ≤ 3/2`. -/
theorem norm_riemannZeta_le_right_smoothAFE_strip
    {σ t : ℝ} (hσlow : 1 / 2 ≤ σ) (hσhigh : σ ≤ 3 / 2)
    (ht : 1 ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      5 * (4 + |t|) := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hre : z.re = σ := by simp [z]
  have hsep : (1 : ℝ) ≤ ‖z - 1‖ := by
    have him : |t| = |(z - 1).im| := by
      dsimp only [z]
      simp
    calc
      1 ≤ |t| := ht
      _ = |(z - 1).im| := him
      _ ≤ ‖z - 1‖ := Complex.abs_im_le_norm _
  have hbase := norm_riemannZeta_le_sqrt_norm_add_two_half
    (s := z) (by rw [hre]; exact hσlow)
    (d := 1) (by norm_num) hsep
  have hsqrt :
      Real.sqrt (‖z‖ + 2) ≤ 4 + |t| := by
    dsimp only [z]
    exact sqrt_norm_real_add_im_add_two_le
      (by linarith) (by linarith)
  norm_num at hbase
  exact hbase.trans <| by gcongr

/-- Uniform polynomial zeta growth on the complete smooth-AFE strip
`-1/2 ≤ σ ≤ 3/2`. -/
theorem norm_riemannZeta_le_smoothAFE_strip
    {σ t : ℝ} (hσlow : -1 / 2 ≤ σ) (hσhigh : σ ≤ 3 / 2)
    (ht : 2 ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      5 * Real.exp 2 * (1 + |t|) * (4 + |t|) := by
  rcases le_total (1 / 2 : ℝ) σ with hright | hleft
  · have hbase := norm_riemannZeta_le_right_smoothAFE_strip
      hright hσhigh (by linarith)
    have hfactor : 1 ≤ Real.exp 2 * (1 + |t|) := by
      have hexp : 1 ≤ Real.exp 2 := by
        exact Real.one_le_exp (by norm_num)
      nlinarith [abs_nonneg t, Real.exp_pos 2]
    calc
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
          5 * (4 + |t|) := hbase
      _ ≤ 5 * Real.exp 2 * (1 + |t|) * (4 + |t|) := by
        have htail : 0 ≤ 4 + |t| := by positivity
        nlinarith
  · let z : ℂ := (σ : ℂ) + (t : ℂ) * I
    have hz0 : z ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      dsimp only [z] at him
      simp at him
      have ht0 : 0 < |t| := by linarith
      exact ht0.ne' (abs_eq_zero.mpr him)
    have hz1 : z ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      dsimp only [z] at him
      simp at him
      have ht0 : 0 < |t| := by linarith
      exact ht0.ne' (abs_eq_zero.mpr him)
    have hGamma : Complex.Gammaℝ (1 - z) ≠ 0 := by
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      dsimp only [z]
      simp only [Complex.sub_re, Complex.one_re, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, zero_mul, mul_zero, sub_zero, add_zero]
      linarith
    have hreflect := zeta_eq_zetaChi_mul hz0 hz1 hGamma
    have hchi :
        ‖zetaChi z‖ ≤ Real.exp 2 * (1 + |t|) := by
      dsimp only [z]
      exact norm_zetaChi_le_half_strip hσlow hleft ht
    have hrightZeta :
        ‖riemannZeta (1 - z)‖ ≤ 5 * (4 + |t|) := by
      have hreal : (1 - z).re = 1 - σ := by
        simp [z]
      have himag : (1 - z).im = -t := by
        simp [z]
      have hbase := norm_riemannZeta_le_right_smoothAFE_strip
        (σ := 1 - σ) (t := -t)
        (by linarith) (by linarith)
        (by simpa using (show 1 ≤ |t| by linarith))
      rw [show (1 - z) = (((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) by
        apply Complex.ext <;> simp [z]]
      simpa using hbase
    rw [hreflect, norm_mul]
    calc
      ‖zetaChi z‖ * ‖riemannZeta (1 - z)‖ ≤
          (Real.exp 2 * (1 + |t|)) * (5 * (4 + |t|)) := by
        gcongr
      _ = 5 * Real.exp 2 * (1 + |t|) * (4 + |t|) := by ring

theorem linePt_add_horizontal_eq
    (τ u T : ℝ) :
    linePt τ + ((u : ℂ) + (T : ℂ) * I) =
      (((1 / 2 + u : ℝ) : ℂ) + ((τ + T : ℝ) : ℂ) * I) := by
  unfold linePt
  push_cast
  ring

theorem norm_smoothAFEGaussianKernel_horizontal_le
    {u T : ℝ} (huLow : -1 ≤ u) (huHigh : u ≤ 1)
    (hT : 1 ≤ |T|) :
    ‖smoothAFEGaussianKernel ((u : ℂ) + (T : ℂ) * I)‖ ≤
      Real.exp 1 * Real.exp (-(T ^ 2)) := by
  have hre :
      ((((u : ℂ) + (T : ℂ) * I) ^ 2).re) = u ^ 2 - T ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  have huSq : u ^ 2 ≤ 1 := by nlinarith
  have hden :
      1 ≤ ‖(u : ℂ) + (T : ℂ) * I‖ := by
    calc
      1 ≤ |T| := hT
      _ = |(((u : ℂ) + (T : ℂ) * I)).im| := by simp
      _ ≤ ‖(u : ℂ) + (T : ℂ) * I‖ := Complex.abs_im_le_norm _
  unfold smoothAFEGaussianKernel
  rw [norm_div, Complex.norm_exp, hre,
    show u ^ 2 - T ^ 2 = u ^ 2 + (-(T ^ 2)) by ring,
    Real.exp_add]
  calc
    Real.exp (u ^ 2) * Real.exp (-(T ^ 2)) /
          ‖(u : ℂ) + (T : ℂ) * I‖
        ≤ Real.exp (u ^ 2) * Real.exp (-(T ^ 2)) := by
          apply (div_le_iff₀ (zero_lt_one.trans_le hden)).2
          exact le_mul_of_one_le_right (by positivity) hden
    _ ≤ Real.exp 1 * Real.exp (-(T ^ 2)) := by
      gcongr

theorem norm_cpow_horizontal_le_exp_abs_log
    {x u T : ℝ} (hx : 0 < x) (huLow : -1 ≤ u) (huHigh : u ≤ 1) :
    ‖(x : ℂ) ^ ((u : ℂ) + (T : ℂ) * I)‖ ≤
      Real.exp |Real.log x| := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    sub_zero, add_zero]
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  calc
    Real.log x * u ≤ |Real.log x * u| := le_abs_self _
    _ = |Real.log x| * |u| := abs_mul _ _
    _ ≤ |Real.log x| * 1 := by
      gcongr
      exact (abs_le).2 ⟨huLow, huHigh⟩
    _ = |Real.log x| := mul_one _

/-- Uniform horizontal-edge majorant before replacing `|τ+T|` by
`|τ|+|T|`. -/
theorem norm_smoothAFEZetaMellinIntegrand_horizontal_le
    {x : ℝ} (hx : 0 < x) (τ : ℝ) {u T : ℝ}
    (huLow : -1 ≤ u) (huHigh : u ≤ 1)
    (hT : 1 ≤ |T|) (hzHeight : 2 ≤ |τ + T|) :
    ‖smoothAFEZetaMellinIntegrand (linePt τ) x
        ((u : ℂ) + (T : ℂ) * I)‖ ≤
      (5 * Real.exp 2 * Real.exp |Real.log x| * Real.exp 1) *
        ((1 + |τ + T|) * (4 + |τ + T|) *
          Real.exp (-(T ^ 2))) := by
  have hzeta :
      ‖riemannZeta
          (linePt τ + ((u : ℂ) + (T : ℂ) * I))‖ ≤
        5 * Real.exp 2 * (1 + |τ + T|) * (4 + |τ + T|) := by
    rw [linePt_add_horizontal_eq]
    exact norm_riemannZeta_le_smoothAFE_strip
      (by linarith) (by linarith) hzHeight
  have hxpow := norm_cpow_horizontal_le_exp_abs_log
    hx huLow huHigh (T := T)
  have hkernel := norm_smoothAFEGaussianKernel_horizontal_le
    huLow huHigh hT
  rw [smoothAFEZetaMellinIntegrand, norm_mul, norm_mul]
  calc
    ‖riemannZeta (linePt τ + (↑u + ↑T * I))‖ *
          ‖(x : ℂ) ^ ((u : ℂ) + (T : ℂ) * I)‖ *
          ‖smoothAFEGaussianKernel ((u : ℂ) + (T : ℂ) * I)‖
        ≤ (5 * Real.exp 2 * (1 + |τ + T|) * (4 + |τ + T|)) *
            Real.exp |Real.log x| *
            (Real.exp 1 * Real.exp (-(T ^ 2))) := by
          gcongr
    _ = (5 * Real.exp 2 * Real.exp |Real.log x| * Real.exp 1) *
        ((1 + |τ + T|) * (4 + |τ + T|) *
          Real.exp (-(T ^ 2))) := by ring

theorem tendsto_shifted_quadratic_mul_exp_neg_sq
    (A C : ℝ) :
    Tendsto
      (fun T : ℝ =>
        C * ((1 + A + T) * (4 + A + T) * Real.exp (-(T ^ 2))))
      atTop (𝓝 0) := by
  have h0 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero
    0 (b := 1) (by norm_num)
  have h1 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero
    1 (b := 1) (by norm_num)
  have h2 := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero
    2 (b := 1) (by norm_num)
  have hsum :=
    (h2.add (h1.const_mul (5 + 2 * A))).add
      (h0.const_mul ((1 + A) * (4 + A)))
  have hscaled := hsum.const_mul C
  simpa only [one_mul, zero_add, mul_zero] using hscaled.congr'
    (Filter.Eventually.of_forall fun T => by
      ring_nf)

theorem tendsto_smoothAFEZetaMellinIntegrand_horizontal_top
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-1)..1,
          smoothAFEZetaMellinIntegrand (linePt τ) x
            ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
  let B : ℝ :=
    5 * Real.exp 2 * Real.exp |Real.log x| * Real.exp 1
  have hmajor :
      Tendsto
        (fun T : ℝ =>
          (2 * B) *
            ((1 + |τ| + T) * (4 + |τ| + T) *
              Real.exp (-(T ^ 2))))
        atTop (𝓝 0) :=
    tendsto_shifted_quadratic_mul_exp_neg_sq |τ| (2 * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max 1 (|τ| + 2))] with T hT
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTlarge : |τ| + 2 ≤ T := le_trans (le_max_right _ _) hT
  have hTabs : |T| = T := abs_of_nonneg (zero_le_one.trans hT1)
  have hheight : 2 ≤ |τ + T| := by
    have htri : |T| ≤ |τ + T| + |τ| := by
      have := abs_sub_le (τ + T) 0 τ
      simpa only [sub_zero, add_sub_cancel_left, zero_sub, abs_neg] using this
    rw [hTabs] at htri
    linarith
  have hheightUpper : |τ + T| ≤ |τ| + T := by
    calc
      |τ + T| ≤ |τ| + |T| := abs_add_le τ T
      _ = |τ| + T := by rw [hTabs]
  have hpoint : ∀ u ∈ uIoc (-1 : ℝ) 1,
      ‖smoothAFEZetaMellinIntegrand (linePt τ) x
          ((u : ℂ) + (T : ℂ) * I)‖ ≤
        B * ((1 + |τ| + T) * (4 + |τ| + T) *
          Real.exp (-(T ^ 2))) := by
    intro u hu
    have hu' : -1 ≤ u ∧ u ≤ 1 := by
      have h := (by simpa [mem_uIcc] using hu : -1 < u ∧ u ≤ 1)
      exact ⟨h.1.le, h.2⟩
    have hbase := norm_smoothAFEZetaMellinIntegrand_horizontal_le
      hx τ hu'.1 hu'.2 (by rw [hTabs]; exact hT1) hheight
    dsimp only [B]
    have hfirst : 1 + |τ + T| ≤ 1 + |τ| + T := by linarith
    have hsecond : 4 + |τ + T| ≤ 4 + |τ| + T := by linarith
    have hpoly :
        (1 + |τ + T|) * (4 + |τ + T|) ≤
          (1 + |τ| + T) * (4 + |τ| + T) :=
      mul_le_mul hfirst hsecond (by positivity) (by positivity)
    exact hbase.trans <| by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpoly (by positivity))
        (by positivity)
  calc
    ‖∫ u : ℝ in (-1)..1,
        smoothAFEZetaMellinIntegrand (linePt τ) x
          ((u : ℂ) + (T : ℂ) * I)‖
        ≤ B * ((1 + |τ| + T) * (4 + |τ| + T) *
            Real.exp (-(T ^ 2))) * |(1 : ℝ) - (-1)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (2 * B) *
          ((1 + |τ| + T) * (4 + |τ| + T) *
            Real.exp (-(T ^ 2))) := by
      norm_num
      ring

theorem tendsto_smoothAFEZetaMellinIntegrand_horizontal_bottom
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ in (-1)..1,
          smoothAFEZetaMellinIntegrand (linePt τ) x
            ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
  let B : ℝ :=
    5 * Real.exp 2 * Real.exp |Real.log x| * Real.exp 1
  have hmajor :
      Tendsto
        (fun T : ℝ =>
          (2 * B) *
            ((1 + |τ| + T) * (4 + |τ| + T) *
              Real.exp (-(T ^ 2))))
        atTop (𝓝 0) :=
    tendsto_shifted_quadratic_mul_exp_neg_sq |τ| (2 * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max 1 (|τ| + 2))] with T hT
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTlarge : |τ| + 2 ≤ T := le_trans (le_max_right _ _) hT
  have hTabs : |T| = T := abs_of_nonneg (zero_le_one.trans hT1)
  have hheight : 2 ≤ |τ - T| := by
    have htri : |T| ≤ |τ - T| + |τ| := by
      have := abs_sub_le τ 0 (τ - T)
      simpa only [sub_zero, zero_sub, abs_neg, sub_sub_cancel, add_comm] using this
    rw [hTabs] at htri
    linarith
  have hheightUpper : |τ - T| ≤ |τ| + T := by
    calc
      |τ - T| = |τ + (-T)| := by rw [sub_eq_add_neg]
      _ ≤ |τ| + |-T| := abs_add_le τ (-T)
      _ = |τ| + T := by rw [abs_neg, hTabs]
  have hpoint : ∀ u ∈ uIoc (-1 : ℝ) 1,
      ‖smoothAFEZetaMellinIntegrand (linePt τ) x
          ((u : ℂ) - (T : ℂ) * I)‖ ≤
        B * ((1 + |τ| + T) * (4 + |τ| + T) *
          Real.exp (-(T ^ 2))) := by
    intro u hu
    have hu' : -1 ≤ u ∧ u ≤ 1 := by
      have h := (by simpa [mem_uIcc] using hu : -1 < u ∧ u ≤ 1)
      exact ⟨h.1.le, h.2⟩
    have hbase := norm_smoothAFEZetaMellinIntegrand_horizontal_le
      hx τ hu'.1 hu'.2
        (T := -T) (by simpa [hTabs] using hT1)
        (by simpa only [sub_eq_add_neg] using hheight)
    dsimp only [B]
    have hbase' :
        ‖smoothAFEZetaMellinIntegrand (linePt τ) x
            ((u : ℂ) - (T : ℂ) * I)‖ ≤
          (5 * Real.exp 2 * Real.exp |Real.log x| * Real.exp 1) *
            ((1 + |τ - T|) * (4 + |τ - T|) *
              Real.exp (-(T ^ 2))) := by
      simpa [sub_eq_add_neg, ofReal_neg, neg_sq] using hbase
    have hfirst : 1 + |τ - T| ≤ 1 + |τ| + T := by linarith
    have hsecond : 4 + |τ - T| ≤ 4 + |τ| + T := by linarith
    have hpoly :
        (1 + |τ - T|) * (4 + |τ - T|) ≤
          (1 + |τ| + T) * (4 + |τ| + T) :=
      mul_le_mul hfirst hsecond (by positivity) (by positivity)
    exact hbase'.trans <| by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpoly (by positivity))
        (by positivity)
  calc
    ‖∫ u : ℝ in (-1)..1,
        smoothAFEZetaMellinIntegrand (linePt τ) x
          ((u : ℂ) - (T : ℂ) * I)‖
        ≤ B * ((1 + |τ| + T) * (4 + |τ| + T) *
            Real.exp (-(T ^ 2))) * |(1 : ℝ) - (-1)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (2 * B) *
          ((1 + |τ| + T) * (4 + |τ| + T) *
            Real.exp (-(T ^ 2))) := by
      norm_num
      ring

/-- Exact infinite vertical-line contour identity for the Gaussian smooth AFE,
with horizontal decay now discharged unconditionally. -/
theorem smoothAFEZetaMellin_infinite_contour_shift_line
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    I • (∫ v : ℝ,
          smoothAFEZetaMellinIntegrand (linePt τ) x
            (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I • (∫ v : ℝ,
          smoothAFEZetaMellinIntegrand (linePt τ) x
            (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I *
        (riemannZeta (linePt τ) +
          smoothAFEZetaShiftedPoleResidue (linePt τ) x) :=
  smoothAFEZetaMellin_infinite_contour_shift_line_of_horizontal_tendsto
    hx
    (tendsto_smoothAFEZetaMellinIntegrand_horizontal_bottom hx τ)
    (tendsto_smoothAFEZetaMellinIntegrand_horizontal_top hx τ)

end RHTower
