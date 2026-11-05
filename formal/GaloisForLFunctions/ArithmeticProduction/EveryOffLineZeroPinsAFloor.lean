import GaloisForLFunctions.ArithmeticProduction.TheMollifierDefectIsASawtoothForm

/-!
# Every off-line zero pins a floor under every mollifier

A zero of `ζ` is a zero of `ζD` for every Dirichlet polynomial `D`, so the Laplace transform of the sawtooth pullback `G` at a
zero does not depend on `D` except through `D(1)`:

  `∫_0^∞ G(u) e^{−(ρ−½)u} du = 1/ρ − D(1)/(1−ρ)`  (`integral_Ioi_defectPull_mul_cexp`).

Cauchy–Schwarz on the half-line, where `e^{−(ρ−½)u}` is square integrable for `Re ρ > ½`, gives for every Dirichlet polynomial,
of any length and with any real coefficients, with no pole normalization:

  `mollifierDefect ≥ D(1)² + (2β−1) |1/ρ − D(1)/(1−ρ)|² ≥ (2β − 1)|1 − ρ|²/|ρ|⁴`  (`mollifierDefect_floor`).

The second inequality is optimal in `D(1)`.  With `a = (ρ−1)/ρ` the bound is `|a|²(1 − |a|²)`, the distance from the disc function `z` to the
Blaschke multiples of `a` in `H²`.  Compare the classical `d_N` floor `(2β−1)/|ρ|²`, which requires `D(1) = 0`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace GaloisForLFunctions.ArithmeticProduction

/-- Cauchy–Schwarz for complex integrands. -/
theorem norm_sq_integral_mul_le {μ : Measure ℝ} {f g : ℝ → ℂ} (hfm : AEStronglyMeasurable f μ)
    (hgm : AEStronglyMeasurable g μ) (hf : Integrable (fun u => ‖f u‖ ^ 2) μ)
    (hg : Integrable (fun u => ‖g u‖ ^ 2) μ) :
    ‖∫ u, f u * g u ∂μ‖ ^ 2 ≤ (∫ u, ‖f u‖ ^ 2 ∂μ) * ∫ u, ‖g u‖ ^ 2 ∂μ := by
  have hmul : Integrable (fun u => ‖f u‖ * ‖g u‖) μ := by
    refine Integrable.mono' (hf.add hg) (hfm.norm.mul hgm.norm)
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    show ‖f u‖ * ‖g u‖ ≤ ‖f u‖ ^ 2 + ‖g u‖ ^ 2
    nlinarith [sq_nonneg (‖f u‖ - ‖g u‖), sq_nonneg (‖f u‖ + ‖g u‖)]
  set A := ∫ u, ‖f u‖ ^ 2 ∂μ
  set B := ∫ u, ‖g u‖ ^ 2 ∂μ
  set C := ∫ u, ‖f u‖ * ‖g u‖ ∂μ
  have hC0 : 0 ≤ C := integral_nonneg fun u => by positivity
  have hle : ‖∫ u, f u * g u ∂μ‖ ≤ C := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => norm_mul _ _)
  have hquad : ∀ x : ℝ, 0 ≤ A * (x * x) + (-(2 * C)) * x + B := by
    intro x
    have hint : Integrable (fun u => (x * ‖f u‖ - ‖g u‖) ^ 2) μ := by
      have h1 := (hf.const_mul (x ^ 2)).sub (hmul.const_mul (2 * x))
      have h2 := h1.add hg
      refine h2.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have h0 : 0 ≤ ∫ u, (x * ‖f u‖ - ‖g u‖) ^ 2 ∂μ := integral_nonneg fun u => sq_nonneg _
    have hexp : ∫ u, (x * ‖f u‖ - ‖g u‖) ^ 2 ∂μ = A * (x * x) + (-(2 * C)) * x + B := by
      have h1 : ∀ u, (x * ‖f u‖ - ‖g u‖) ^ 2 =
          x ^ 2 * ‖f u‖ ^ 2 - 2 * x * (‖f u‖ * ‖g u‖) + ‖g u‖ ^ 2 := fun u => by ring
      simp_rw [h1]
      rw [integral_add ((hf.const_mul _).sub (hmul.const_mul _)) hg,
        integral_sub (hf.const_mul _) (hmul.const_mul _), integral_const_mul, integral_const_mul]
      ring
    rw [hexp] at h0
    exact h0
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  have h1 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  nlinarith

/-- `∫_ℝ {e^u/n} e^{−su} du = n^{−s}(−ζ(s)/s)` on `0 < Re s < 1`. -/
theorem integral_fract_mul_cexp {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ∫ u : ℝ, ((Int.fract (Real.exp u / n) : ℝ) : ℂ) * Complex.exp (-s * u) =
      (n : ℂ) ^ (-s) * (-(riemannZeta s / s)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm := _root_.RHTower.mellin_fract_inv_natCast_mul hn h0 h1
  rw [mellin_eq_fourier, Real.fourier_real_eq] at hm
  rw [← hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  have hinv : ((n : ℝ) * Real.exp (-v))⁻¹ = Real.exp v / n := by
    rw [mul_inv, ← Real.exp_neg, neg_neg]
    field_simp
  rw [hinv, Circle.smul_def, Complex.real_smul, smul_eq_mul, Real.fourierChar_apply]
  have hexp : Complex.exp (-s * v) =
      Complex.exp (((2 * Real.pi * (-(v * (s.im / (2 * Real.pi)))) : ℝ) : ℂ) * I) *
        ((Real.exp (-s.re * v) : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.exp_add]
    congr 1
    conv_lhs => rw [← Complex.re_add_im s]
    field_simp
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [hexp]
  ring

/-- The integrand `e^{−u/2}{e^u/n} e^{−(s−½)u}` is integrable on `0 < Re s < 1`. -/
theorem integrable_fractLogPullDilate_mul_cexp {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1) :
    Integrable fun u : ℝ =>
      _root_.RHTower.fractLogPullDilate n u * Complex.exp (-(s - 1 / 2) * u) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set c : ℝ := min s.re (1 - s.re) with hc
  have hc0 : 0 < c := lt_min h0 (by linarith)
  have hb : Integrable fun u : ℝ => Real.exp (-c * |u|) := by
    refine (GaloisForLFunctions.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hc0).congr
      (Filter.Eventually.of_forall fun u => by simp)
  refine Integrable.mono' hb
    (((_root_.RHTower.measurable_fractLogPullDilate n).mul (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => ?_)
  have hnorm : ‖_root_.RHTower.fractLogPullDilate n u * Complex.exp (-(s - 1 / 2) * u)‖ =
      Real.exp (-s.re * u) * Int.fract (Real.exp u / n) := by
    rw [norm_mul, _root_.RHTower.norm_fractLogPullDilate, Complex.norm_exp]
    have hre : (-(s - 1 / 2) * (u : ℂ)).re = -(s.re - 1 / 2) * u := by
      simp [Complex.mul_re]
    rw [hre]
    have hsplit : Real.exp (-s.re * u) = Real.exp (-(u / 2)) * Real.exp (-(s.re - 1 / 2) * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    ring
  rw [hnorm]
  have hfr0 := Int.fract_nonneg (Real.exp u / n)
  have hfr1 := (Int.fract_lt_one (Real.exp u / n)).le
  have hfr2 : Int.fract (Real.exp u / n) ≤ Real.exp u :=
    (_root_.RHTower.fract_div_natCast_le hn (Real.exp_pos u).le)
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    calc Real.exp (-s.re * u) * Int.fract (Real.exp u / n)
        ≤ Real.exp (-s.re * u) * 1 := mul_le_mul_of_nonneg_left hfr1 (Real.exp_pos _).le
      _ = Real.exp (-s.re * u) := mul_one _
      _ ≤ Real.exp (-c * u) := Real.exp_le_exp.mpr (by
          have : c ≤ s.re := min_le_left _ _
          nlinarith)
  · rw [abs_of_nonpos hu]
    calc Real.exp (-s.re * u) * Int.fract (Real.exp u / n)
        ≤ Real.exp (-s.re * u) * Real.exp u :=
          mul_le_mul_of_nonneg_left hfr2 (Real.exp_pos _).le
      _ = Real.exp ((1 - s.re) * u) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (-c * -u) := Real.exp_le_exp.mpr (by
          have : c ≤ 1 - s.re := min_le_right _ _
          nlinarith)

/-- The Laplace transform of the sawtooth pullback over the whole line, at a zero of `ζ`. -/
theorem integral_defectPull_mul_cexp {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {ρ : ℂ}
    (hρ0 : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    ∫ u : ℝ, defectPull S a u * Complex.exp (-(ρ - 1 / 2) * u) = 1 / ρ := by
  have hρpos : 0 < ρ.re := by linarith
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hρpos
    exact lt_irrefl _ hρpos
  -- the target
  have htarget : ∫ u : ℝ, targetPull u * Complex.exp (-(ρ - 1 / 2) * u) = 1 / ρ := by
    have hpt : ∀ u : ℝ, targetPull u * Complex.exp (-(ρ - 1 / 2) * u) =
        (Ici (0 : ℝ)).indicator (fun v : ℝ => Complex.exp (-ρ * v)) u := by
      intro u
      by_cases hu : 0 ≤ u
      · simp only [targetPull, if_pos hu, indicator, mem_Ici]
        push_cast
        rw [← Complex.exp_add]
        congr 1
        ring
      · simp [targetPull, indicator, hu]
    simp_rw [hpt]
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_exp_mul_complex_Ioi (by simpa using hρpos) 0]
    simp only [ofReal_zero, mul_zero, Complex.exp_zero]
    rw [neg_div_neg_eq]
  -- the sawtooth
  have hsum : ∫ u : ℝ, _root_.RHTower.fractGramPull S a u * Complex.exp (-(ρ - 1 / 2) * u) = 0 := by
    unfold _root_.RHTower.fractGramPull
    simp_rw [Finset.sum_mul]
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero fun n hn => ?_
      have hpt : ∀ u : ℝ, (a n : ℂ) * _root_.RHTower.fractLogPullDilate n u *
          Complex.exp (-(ρ - 1 / 2) * u) =
          (a n : ℂ) * (((Int.fract (Real.exp u / n) : ℝ) : ℂ) * Complex.exp (-ρ * u)) := by
        intro u
        unfold _root_.RHTower.fractLogPullDilate
        have hsplit : Complex.exp (-ρ * u) =
            ((Real.exp (-(u / 2)) : ℝ) : ℂ) * Complex.exp (-(ρ - 1 / 2) * u) := by
          push_cast
          rw [← Complex.exp_add]
          congr 1
          ring
        rw [hsplit]
        push_cast
        ring
      simp_rw [hpt]
      rw [integral_const_mul, integral_fract_mul_cexp (hS n hn) hρpos hρ1, hz]
      simp
    · intro n hn
      have h := (integrable_fractLogPullDilate_mul_cexp (hS n hn) hρpos hρ1).const_mul (a n : ℂ)
      refine h.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only
      ring
  have hint1 : Integrable fun u : ℝ => targetPull u * Complex.exp (-(ρ - 1 / 2) * u) := by
    have hpt : (fun u : ℝ => targetPull u * Complex.exp (-(ρ - 1 / 2) * u)) =
        (Ici (0 : ℝ)).indicator (fun v : ℝ => Complex.exp (-ρ * v)) := by
      funext u
      by_cases hu : 0 ≤ u
      · simp only [targetPull, if_pos hu, indicator, mem_Ici]
        push_cast
        rw [← Complex.exp_add]
        congr 1
        ring
      · simp [targetPull, indicator, hu]
    rw [hpt, integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_complex_Ioi (by simpa using hρpos) 0
  have hint2 : Integrable fun u : ℝ =>
      _root_.RHTower.fractGramPull S a u * Complex.exp (-(ρ - 1 / 2) * u) := by
    unfold _root_.RHTower.fractGramPull
    simp_rw [Finset.sum_mul]
    refine integrable_finset_sum _ fun n hn => ?_
    have h := (integrable_fractLogPullDilate_mul_cexp (hS n hn) hρpos hρ1).const_mul (a n : ℂ)
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only
    ring
  unfold defectPull
  simp_rw [add_mul]
  rw [integral_add hint1 hint2, htarget, hsum, add_zero]

/-- The pullback on the negative half-line. -/
theorem defectPull_of_neg {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {u : ℝ} (hu : u < 0) :
    defectPull S a u = ((Real.exp (u / 2) * valueAtOne S a : ℝ) : ℂ) := by
  have hlt : Real.exp u < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hu
  rw [defectPull_eq_ofReal, sawtoothDefect_of_lt_one hS a (Real.exp_pos u).le hlt, ← mul_assoc]
  congr 3
  rw [← Real.exp_add]
  congr 1
  ring

/-- **The Laplace transform on the positive half-line.** -/
theorem integral_Ioi_defectPull_mul_cexp {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {ρ : ℂ}
    (hρ0 : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    ∫ u in Ioi (0 : ℝ), defectPull S a u * Complex.exp (-(ρ - 1 / 2) * u) =
      1 / ρ - valueAtOne S a / (1 - ρ) := by
  have hne : 1 - ρ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hfull := integral_defectPull_mul_cexp hS a hρ0 hρ1 hz
  have hint : Integrable fun u : ℝ => defectPull S a u * Complex.exp (-(ρ - 1 / 2) * u) := by
    unfold defectPull
    simp_rw [add_mul]
    refine Integrable.add ?_ ?_
    · have hpt : (fun u : ℝ => targetPull u * Complex.exp (-(ρ - 1 / 2) * u)) =
          (Ici (0 : ℝ)).indicator (fun v : ℝ => Complex.exp (-ρ * v)) := by
        funext u
        by_cases hu : 0 ≤ u
        · simp only [targetPull, if_pos hu, indicator, mem_Ici]
          push_cast
          rw [← Complex.exp_add]
          congr 1
          ring
        · simp [targetPull, indicator, hu]
      rw [hpt, integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
      exact integrableOn_exp_mul_complex_Ioi (by simpa using (by linarith : 0 < ρ.re)) 0
    · unfold _root_.RHTower.fractGramPull
      simp_rw [Finset.sum_mul]
      refine integrable_finset_sum _ fun n hn => ?_
      have h := (integrable_fractLogPullDilate_mul_cexp (hS n hn) (by linarith) hρ1).const_mul
        (a n : ℂ)
      refine h.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only
      ring
  have hneg : ∫ u in Iio (0 : ℝ), defectPull S a u * Complex.exp (-(ρ - 1 / 2) * u) =
      valueAtOne S a / (1 - ρ) := by
    have hpt : ∀ u ∈ Iio (0 : ℝ), defectPull S a u * Complex.exp (-(ρ - 1 / 2) * u) =
        (valueAtOne S a : ℂ) * Complex.exp ((1 - ρ) * u) := by
      intro u hu
      rw [defectPull_of_neg hS a hu]
      push_cast
      have hsplit : Complex.exp ((1 - ρ) * u) =
          Complex.exp (u / 2) * Complex.exp (-(ρ - 1 / 2) * u) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [hsplit]
      ring
    rw [setIntegral_congr_fun measurableSet_Iio hpt, integral_const_mul]
    have hI := _root_.integral_exp_mul_complex_Iic (a := 1 - ρ) (by simp; linarith) 0
    rw [integral_Iio_eq_integral_Iic ] at *
    rw [hI]
    simp [div_eq_mul_inv]
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (f := fun u : ℝ => defectPull S a u * Complex.exp (-(ρ - 1 / 2) * u)) (b := 0)
    hint.integrableOn hint.integrableOn
  rw [hfull, integral_Iic_eq_integral_Iio, hneg] at hsplit
  rw [← hsplit]
  ring

/-- **The floor, before optimizing `D(1)`.** -/
theorem mollifierDefect_ge_laplace {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {ρ : ℂ}
    (hρ0 : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    valueAtOne S a ^ 2 + (2 * ρ.re - 1) * ‖1 / ρ - valueAtOne S a / (1 - ρ)‖ ^ 2 ≤
      mollifierDefect S a := by
  have hA : 0 < 2 * ρ.re - 1 := by linarith
  have hG := integrable_norm_sq_defectPull hS a
  have hGm := (integrable_defectPull hS a).aestronglyMeasurable
  set A := 2 * ρ.re - 1 with hAdef
  -- Cauchy-Schwarz on the half-line
  have hnormexp : ∀ u : ℝ, ‖Complex.exp (-(ρ - 1 / 2) * u)‖ ^ 2 = Real.exp (-A * u) := by
    intro u
    rw [Complex.norm_exp, ← Real.exp_nat_mul]
    congr 1
    simp [Complex.mul_re, hAdef]
    ring
  have hhint : Integrable (fun u : ℝ => ‖Complex.exp (-(ρ - 1 / 2) * u)‖ ^ 2)
      (volume.restrict (Ioi 0)) := by
    simp_rw [hnormexp]
    exact exp_neg_integrableOn_Ioi 0 hA
  have hCS := norm_sq_integral_mul_le (μ := volume.restrict (Ioi (0 : ℝ))) hGm.restrict
    (Continuous.aestronglyMeasurable (by fun_prop)) hG.integrableOn hhint
  rw [integral_Ioi_defectPull_mul_cexp hS a hρ0 hρ1 hz] at hCS
  have hhval : ∫ u in Ioi (0 : ℝ), ‖Complex.exp (-(ρ - 1 / 2) * u)‖ ^ 2 = A⁻¹ := by
    simp_rw [hnormexp]
    rw [integral_exp_neg_mul_Ioi hA]
    simp
  rw [hhval] at hCS
  -- the two half-lines
  have hdisj : Disjoint (Iio (0 : ℝ)) (Ioi 0) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    exact lt_asymm hu hu'
  have hsub : ∫ u in Iio (0 : ℝ) ∪ Ioi 0, ‖defectPull S a u‖ ^ 2 ≤ mollifierDefect S a :=
    setIntegral_le_integral hG (Filter.Eventually.of_forall fun u => by positivity)
  rw [setIntegral_union hdisj measurableSet_Ioi hG.integrableOn hG.integrableOn] at hsub
  have hneg : ∫ u in Iio (0 : ℝ), ‖defectPull S a u‖ ^ 2 = valueAtOne S a ^ 2 := by
    have hpt : ∀ u ∈ Iio (0 : ℝ), ‖defectPull S a u‖ ^ 2 = valueAtOne S a ^ 2 * Real.exp u := by
      intro u hu
      rw [defectPull_of_neg hS a hu, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
        ← Real.exp_nat_mul]
      have : ((2 : ℕ) : ℝ) * (u / 2) = u := by push_cast; ring
      rw [this]
      ring
    rw [setIntegral_congr_fun measurableSet_Iio hpt, integral_const_mul,
      ← integral_Iic_eq_integral_Iio, integral_exp_Iic_zero, mul_one]
  rw [hneg] at hsub
  have hmul : A * ‖1 / ρ - valueAtOne S a / (1 - ρ)‖ ^ 2 ≤
      ∫ u in Ioi (0 : ℝ), ‖defectPull S a u‖ ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hCS hA.le
    have h2 : A * ((∫ u in Ioi (0 : ℝ), ‖defectPull S a u‖ ^ 2) * A⁻¹) =
        ∫ u in Ioi (0 : ℝ), ‖defectPull S a u‖ ^ 2 := by
      field_simp
    linarith
  linarith

/-- **The floor.**  For every Dirichlet polynomial, of any length, with any real coefficients, and every zero with `½ < Re ρ < 1`,
the mollifier defect is at least `(2β − 1)|1 − ρ|²/|ρ|⁴`. -/
theorem mollifierDefect_floor {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {ρ : ℂ}
    (hρ0 : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    (2 * ρ.re - 1) * ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 4 ≤ mollifierDefect S a := by
  have hbase := mollifierDefect_ge_laplace hS a hρ0 hρ1 hz
  set w := valueAtOne S a
  set A := 2 * ρ.re - 1 with hAdef
  have hA : 0 < A := by rw [hAdef]; linarith
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hρ0
    norm_num at hρ0
  have hne : 1 - ρ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  have h1pos : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hne
  -- `|ρ|² = |1 − ρ|² + A`
  have hnorms : ‖ρ‖ ^ 2 = ‖1 - ρ‖ ^ 2 + A := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hAdef]
    simp
    ring
  set a₁ := ‖1 / ρ - (w : ℂ) / (1 - ρ)‖ with ha₁
  set ε := ‖1 - ρ‖⁻¹ with hε
  have hε0 : 0 < ε := by positivity
  have htri : ‖ρ‖⁻¹ ≤ a₁ + |w| * ε := by
    have h1 : (1 : ℂ) / ρ = (1 / ρ - (w : ℂ) / (1 - ρ)) + (w : ℂ) / (1 - ρ) := by ring
    have h2 := norm_add_le (1 / ρ - (w : ℂ) / (1 - ρ)) ((w : ℂ) / (1 - ρ))
    rw [← h1, norm_div, norm_one, one_div, norm_div, Complex.norm_real, Real.norm_eq_abs] at h2
    rw [ha₁, hε]
    calc ‖ρ‖⁻¹ ≤ _ := h2
      _ = _ := by rw [div_eq_mul_inv]
  have hsq : ‖ρ‖⁻¹ ^ 2 ≤ (a₁ + |w| * ε) ^ 2 := pow_le_pow_left₀ (by positivity) htri 2
  -- Cauchy-Schwarz in the plane
  have hplane : (a₁ + |w| * ε) ^ 2 * A ≤ (w ^ 2 + A * a₁ ^ 2) * (1 + A * ε ^ 2) := by
    have h0 : (w ^ 2 + A * a₁ ^ 2) * (1 + A * ε ^ 2) - (a₁ + |w| * ε) ^ 2 * A =
        (|w| - A * a₁ * ε) ^ 2 := by
      have hw : w ^ 2 = |w| ^ 2 := (sq_abs w).symm
      rw [hw]
      ring
    nlinarith [sq_nonneg (|w| - A * a₁ * ε)]
  have h1Aε : 1 + A * ε ^ 2 = ‖ρ‖ ^ 2 * ε ^ 2 := by
    have hε1 : ‖1 - ρ‖ ^ 2 * ε ^ 2 = 1 := by
      rw [hε, ← mul_pow, mul_inv_cancel₀ h1pos.ne', one_pow]
    rw [hnorms]
    nlinarith
  have hkey : A * ‖ρ‖⁻¹ ^ 2 ≤ (w ^ 2 + A * a₁ ^ 2) * (‖ρ‖ ^ 2 * ε ^ 2) := by
    rw [← h1Aε]
    calc A * ‖ρ‖⁻¹ ^ 2 ≤ A * (a₁ + |w| * ε) ^ 2 := mul_le_mul_of_nonneg_left hsq hA.le
      _ = (a₁ + |w| * ε) ^ 2 * A := by ring
      _ ≤ _ := hplane
  have hval : (2 * ρ.re - 1) * ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 4 = A * ‖ρ‖⁻¹ ^ 2 / (‖ρ‖ ^ 2 * ε ^ 2) := by
    rw [← hAdef, hε]
    field_simp
  rw [hval, div_le_iff₀ (by positivity)]
  refine hkey.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have : w ^ 2 + A * a₁ ^ 2 = w ^ 2 + (2 * ρ.re - 1) * ‖1 / ρ - (w : ℂ) / (1 - ρ)‖ ^ 2 := rfl
  rw [this]
  exact hbase

end GaloisForLFunctions.ArithmeticProduction
