import GaloisForLFunctions.ArithmeticProduction.EveryOffLineZeroPinsAFloor
import GaloisForLFunctions.ArithmeticProduction.TheLinearMollifierIsTheChebyshevError

/-!
# Prefix cancellation amplifies the off-line zero floor

In `EveryOffLineZeroPinsAFloor`, splitting the Laplace transform of the sawtooth pullback at
`u = 0` (`x = 1`) yields the length-independent floor
`(2 Re ρ − 1) ‖1 − ρ‖² / ‖ρ‖⁴ ≤ mollifierDefect S a` for every real Dirichlet polynomial.

Whenever the restricted divisor sums `∑_{d ∈ S, d ∣ n} a_d` match `δ_{n,1}` on an initial segment
`1 ≤ n ≤ y₁`, the sawtooth function `sawtoothDefect S a x` remains exact linear `x · D(1)` all the
way up to `x = y₁` (`u = log y₁`).  Splitting the Laplace integral at `u = log y₁` instead of
`u = 0` and minimizing the resulting quadratic form in `|D(1)| · y₁^{1 − Re ρ}` amplifies the floor
by the exact power `y₁^{2 Re ρ − 1}` (`mollifierDefect_floor_mul_rpow_of_prefix_cancel`):

  `((2 Re ρ − 1) ‖1 − ρ‖² / ‖ρ‖⁴) · y₁^{2 Re ρ − 1} ≤ mollifierDefect S a`.

Consequently:
* For the sharp Möbius truncation `M_y(s) = ∑_{d ≤ y} μ(d) d^{−s}`, any sparse subsequence bound
  `mollifierDefect(Icc 1 y, μ) ≤ C_η y^{2β + η}` (`∃ᶠ y in atTop`) confines every zeta zero to
  `Re ρ ≤ ½ + β` (`xiZeroHalfPlaneBound_of_frequently_sharpDefect_le`), and sparse subpolynomial
  growth implies `RiemannHypothesis` (`riemannHypothesis_of_frequently_sharpDefect_subpolynomial`).
* Plancherel bounds every unweighted second moment `∫_1^T ‖ζ(½+it) D(½+it)‖² dt` linearly in
  `T` plus `(¼ + T²) · mollifierDefect S a`
  (`integral_normSq_zeta_realDirichletPoly_le_of_mollifierDefect`).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace GaloisForLFunctions.ArithmeticProduction

open BiScaleUncertainty.ChebyshevGauge BiScaleUncertainty.SignedPrimePolar

/-! ### Prefix-cancelled sawtooth linearity -/

/-- **General hyperbola identity.** For any finite support `S ⊂ ℕ₊` and `X : ℕ`,
`∑_{d ∈ S} a_d ⌊X/d⌋ = ∑_{1 ≤ n ≤ X} ∑_{d ∈ S, d ∣ n} a_d`. -/
theorem sum_mul_nat_div_of_support {S : Finset ℕ} (hS : ∀ d ∈ S, 1 ≤ d) (a : ℕ → ℝ) (X : ℕ) :
    ∑ d ∈ S, a d * ((X / d : ℕ) : ℝ) =
      ∑ n ∈ Finset.Icc 1 X, divisorSum S a n := by
  have h1 : ∀ d ∈ S, ((X / d : ℕ) : ℝ) =
      ∑ n ∈ Finset.Icc 1 X, (if d ∣ n then (1 : ℝ) else 0) := by
    intro d hd
    have hd0 : 0 < d := hS d hd
    rw [sum_Icc_ite_dvd hd0 X (fun _ => 1)]
    simp
  rw [Finset.sum_congr rfl fun d hd => by rw [h1 d hd]]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold divisorSum
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

/-- Fractional-part sum on a general finite support `S` decomposed into linear slope minus
hyperbola sum. -/
theorem sum_mul_fract_eq_of_support (S : Finset ℕ) (a : ℕ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ∑ d ∈ S, a d * Int.fract (x / d) =
      x * valueAtOne S a - ∑ d ∈ S, a d * ((⌊x⌋₊ / d : ℕ) : ℝ) := by
  unfold valueAtOne
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hfloor : ((⌊x / d⌋ : ℤ) : ℝ) = ((⌊x⌋₊ / d : ℕ) : ℝ) := by
    rw [← natCast_floor_eq_intCast_floor (div_nonneg hx hd0), Nat.floor_div_natCast]
  rw [Int.fract, hfloor]
  ring

/-- **Sawtooth linearity up to the cancellation horizon.** If `∑_{d ∈ S, d ∣ n} a_d = δ_{n,1}` for
all `1 ≤ n ≤ y₁`, then `sawtoothDefect S a x = x · D(1)` across the entire interval `[0, y₁]`. -/
theorem sawtoothDefect_eq_mul_valueAtOne_of_prefix_cancel {S : Finset ℕ}
    (hS : ∀ d ∈ S, 1 ≤ d) {a : ℕ → ℝ} {y₁ : ℕ}
    (hcancel : ∀ n ∈ Finset.Icc 1 y₁, divisorSum S a n = if n = 1 then 1 else 0)
    {x : ℝ} (hx0 : 0 ≤ x) (hxy₁ : x ≤ y₁) :
    sawtoothDefect S a x = x * valueAtOne S a := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · exact sawtoothDefect_of_lt_one hS a hx0 hx1
  · unfold sawtoothDefect
    rw [if_pos hx1, sum_mul_fract_eq_of_support S a hx0, sum_mul_nat_div_of_support hS a ⌊x⌋₊]
    have hfl1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx1
    have hfly₁ : ⌊x⌋₊ ≤ y₁ := Nat.floor_le_of_le hxy₁
    have hcongr : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, divisorSum S a n =
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if n = 1 then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
      exact hcancel n (Finset.mem_Icc.mpr ⟨hn1, hnx.trans hfly₁⟩)
    rw [hcongr, sum_Icc_ite_eq_one hfl1]
    ring

/-- Under prefix cancellation up to `y₁ ≥ 1`, `defectPull S a u = D(1) e^{u/2}` for all
`u ≤ log y₁`. -/
theorem defectPull_of_le_log_of_prefix_cancel {S : Finset ℕ}
    (hS : ∀ d ∈ S, 1 ≤ d) {a : ℕ → ℝ} {y₁ : ℕ} (hy₁ : 1 ≤ y₁)
    (hcancel : ∀ n ∈ Finset.Icc 1 y₁, divisorSum S a n = if n = 1 then 1 else 0)
    {u : ℝ} (hu : u ≤ Real.log y₁) :
    defectPull S a u = ((Real.exp (u / 2) * valueAtOne S a : ℝ) : ℂ) := by
  have hy₁0 : (0 : ℝ) < y₁ := by exact_mod_cast hy₁
  have hexp_le : Real.exp u ≤ y₁ := by
    calc Real.exp u ≤ Real.exp (Real.log y₁) := Real.exp_le_exp.mpr hu
      _ = y₁ := Real.exp_log hy₁0
  have hval : Real.exp (-(u / 2)) * (Real.exp u * valueAtOne S a) =
      Real.exp (u / 2) * valueAtOne S a := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [defectPull_eq_ofReal,
    sawtoothDefect_eq_mul_valueAtOne_of_prefix_cancel hS hcancel (Real.exp_pos u).le hexp_le,
    hval]

/-! ### Shifted Laplace identity and prefix-amplified zero floor -/

/-- **Shifted Laplace transform above `log y₁`.** At a zero `ρ` of `ζ` in `½ < Re ρ < 1`, prefix
cancellation up to `y₁` evaluates the lower tail `u ≤ log y₁` explicitly. -/
theorem integral_Ioi_log_defectPull_mul_cexp_of_prefix_cancel {S : Finset ℕ}
    (hS : ∀ d ∈ S, 1 ≤ d) {a : ℕ → ℝ} {y₁ : ℕ} (hy₁ : 1 ≤ y₁)
    (hcancel : ∀ n ∈ Finset.Icc 1 y₁, divisorSum S a n = if n = 1 then 1 else 0)
    {ρ : ℂ} (hρ0 : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    ∫ u in Ioi (Real.log y₁), defectPull S a u * Complex.exp (-(ρ - 1 / 2) * u) =
      1 / ρ - (valueAtOne S a : ℂ) * Complex.exp ((1 - ρ) * Real.log y₁) / (1 - ρ) := by
  set L : ℝ := Real.log y₁
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
      refine integrable_finsetSum _ fun n hn => ?_
      have h := (integrable_fractLogPullDilate_mul_cexp (hS n hn) (by linarith) hρ1).const_mul
        (a n : ℂ)
      refine h.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only
      ring
  have hlow : ∫ u in Iic L, defectPull S a u * Complex.exp (-(ρ - 1 / 2) * u) =
      (valueAtOne S a : ℂ) * Complex.exp ((1 - ρ) * L) / (1 - ρ) := by
    have hpt : ∀ u ∈ Iic L, defectPull S a u * Complex.exp (-(ρ - 1 / 2) * u) =
        (valueAtOne S a : ℂ) * Complex.exp ((1 - ρ) * u) := by
      intro u hu
      rw [defectPull_of_le_log_of_prefix_cancel hS hy₁ hcancel hu]
      push_cast
      have hsplit : Complex.exp ((1 - ρ) * u) =
          Complex.exp (u / 2) * Complex.exp (-(ρ - 1 / 2) * u) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [hsplit]
      ring
    have hre : 0 < (1 - ρ).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    rw [setIntegral_congr_fun measurableSet_Iic hpt, integral_const_mul,
      integral_exp_mul_complex_Iic hre L, mul_div_assoc]
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (f := fun u : ℝ => defectPull S a u * Complex.exp (-(ρ - 1 / 2) * u)) (b := L)
    hint.integrableOn hint.integrableOn
  rw [hfull, hlow] at hsplit
  rw [← hsplit]
  ring

/-- **Prefix-cancelled Laplace lower bound before optimizing `D(1)`.** -/
theorem mollifierDefect_ge_laplace_of_prefix_cancel {S : Finset ℕ}
    (hS : ∀ d ∈ S, 1 ≤ d) {a : ℕ → ℝ} {y₁ : ℕ} (hy₁ : 1 ≤ y₁)
    (hcancel : ∀ n ∈ Finset.Icc 1 y₁, divisorSum S a n = if n = 1 then 1 else 0)
    {ρ : ℂ} (hρ0 : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    (y₁ : ℝ) * valueAtOne S a ^ 2 +
        (2 * ρ.re - 1) * (y₁ : ℝ) ^ (2 * ρ.re - 1) *
          ‖1 / ρ - (valueAtOne S a : ℂ) * Complex.exp ((1 - ρ) * Real.log y₁) / (1 - ρ)‖ ^ 2 ≤
      mollifierDefect S a := by
  set L : ℝ := Real.log y₁ with hLdef
  set A : ℝ := 2 * ρ.re - 1 with hAdef
  have hA : 0 < A := by rw [hAdef]; linarith
  have hy₁1 : (1 : ℝ) ≤ y₁ := by exact_mod_cast hy₁
  have hy₁0 : (0 : ℝ) < y₁ := by linarith
  have hL0 : 0 ≤ L := Real.log_nonneg hy₁1
  have hG := integrable_norm_sq_defectPull hS a
  have hGm := (integrable_defectPull hS a).aestronglyMeasurable
  -- Cauchy–Schwarz on `(L, ∞)`
  have hnormexp : ∀ u : ℝ, ‖Complex.exp (-(ρ - 1 / 2) * u)‖ ^ 2 = Real.exp (-A * u) := by
    intro u
    have hre : (-(ρ - 1 / 2) * (u : ℂ)).re = -(ρ.re - 1 / 2) * u := by
      simp [Complex.mul_re]
    rw [Complex.norm_exp, ← Real.exp_nat_mul, hre]
    congr 1
    rw [hAdef]
    push_cast
    ring
  have hhint : Integrable (fun u : ℝ => ‖Complex.exp (-(ρ - 1 / 2) * u)‖ ^ 2)
      (volume.restrict (Ioi L)) := by
    simp_rw [hnormexp]
    exact exp_neg_integrableOn_Ioi L hA
  have hCS := norm_sq_integral_mul_le (μ := volume.restrict (Ioi L))
    (g := fun u : ℝ => Complex.exp (-(ρ - 1 / 2) * u)) hGm.restrict
    (Continuous.aestronglyMeasurable (by fun_prop)) hG.integrableOn hhint
  rw [integral_Ioi_log_defectPull_mul_cexp_of_prefix_cancel hS hy₁ hcancel hρ0 hρ1 hz] at hCS
  have hhval : ∫ u in Ioi L, ‖Complex.exp (-(ρ - 1 / 2) * u)‖ ^ 2 = Real.exp (-A * L) / A := by
    simp_rw [hnormexp]
    rw [integral_exp_mul_Ioi (by linarith : -A < 0) L, neg_div_neg_eq]
  rw [hhval] at hCS
  have hy₁A : (y₁ : ℝ) ^ A = Real.exp (A * L) := by
    rw [hLdef, Real.rpow_def_of_pos hy₁0, mul_comm]
  have htail : A * (y₁ : ℝ) ^ A *
      ‖1 / ρ - (valueAtOne S a : ℂ) * Complex.exp ((1 - ρ) * L) / (1 - ρ)‖ ^ 2 ≤
      ∫ u in Ioi L, ‖defectPull S a u‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hCS (show 0 ≤ A * Real.exp (A * L) by positivity)
    have hcancel_exp : A * Real.exp (A * L) *
        ((∫ u in Ioi L, ‖defectPull S a u‖ ^ 2) * (Real.exp (-A * L) / A)) =
        ∫ u in Ioi L, ‖defectPull S a u‖ ^ 2 := by
      have hexp_mul : Real.exp (A * L) * Real.exp (-A * L) = 1 := by
        rw [← Real.exp_add]
        simp
      have hAne : A ≠ 0 := hA.ne'
      calc A * Real.exp (A * L) *
            ((∫ u in Ioi L, ‖defectPull S a u‖ ^ 2) * (Real.exp (-A * L) / A))
          = (∫ u in Ioi L, ‖defectPull S a u‖ ^ 2) *
              ((Real.exp (A * L) * Real.exp (-A * L)) * (A / A)) := by ring
        _ = ∫ u in Ioi L, ‖defectPull S a u‖ ^ 2 := by rw [hexp_mul, div_self hAne, mul_one, mul_one]
    rw [hy₁A]
    linarith
  -- Lower parts `(-∞, 0) ∪ [0, L]` and upper tail `(L, ∞)`
  have hdisj1 : Disjoint (Iio (0 : ℝ)) (Icc 0 L) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    exact absurd hu'.1 (not_le.mpr hu)
  have hdisj2 : Disjoint (Iio (0 : ℝ) ∪ Icc 0 L) (Ioi L) := by
    rw [Set.disjoint_left]
    rintro u (hu | hu) hu'
    · have h1 : u < 0 := hu
      have h2 : L < u := hu'
      linarith
    · exact absurd hu.2 (not_le.mpr hu')
  have hsub : ∫ u in (Iio (0 : ℝ) ∪ Icc 0 L) ∪ Ioi L, ‖defectPull S a u‖ ^ 2 ≤
      mollifierDefect S a :=
    setIntegral_le_integral hG (Filter.Eventually.of_forall fun u => by positivity)
  rw [setIntegral_union hdisj2 measurableSet_Ioi hG.integrableOn hG.integrableOn,
    setIntegral_union hdisj1 measurableSet_Icc hG.integrableOn hG.integrableOn] at hsub
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
  have hband : ∫ u in Icc 0 L, ‖defectPull S a u‖ ^ 2 =
      valueAtOne S a ^ 2 * ((y₁ : ℝ) - 1) := by
    have hpt : ∀ u ∈ Icc 0 L, ‖defectPull S a u‖ ^ 2 = valueAtOne S a ^ 2 * Real.exp u := by
      intro u hu
      rw [defectPull_of_le_log_of_prefix_cancel hS hy₁ hcancel hu.2,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, ← Real.exp_nat_mul]
      have : ((2 : ℕ) : ℝ) * (u / 2) = u := by push_cast; ring
      rw [this]
      ring
    rw [setIntegral_congr_fun measurableSet_Icc hpt, integral_const_mul,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL0, integral_exp,
      hLdef, Real.exp_log hy₁0, Real.exp_zero]
  rw [hneg, hband] at hsub
  linarith

/-- **Prefix-amplified sawtooth zero floor.** For any finite support `S ⊂ ℕ₊`, horizon `y₁ ≥ 1`,
real weight `a` satisfying `∑_{d ∈ S, d ∣ n} a_d = δ_{n,1}` on `1 ≤ n ≤ y₁`, and zeta zero `ρ`
with `½ < Re ρ < 1`,
`((2 Re ρ − 1) ‖1 − ρ‖² / ‖ρ‖⁴) · y₁^{2 Re ρ − 1} ≤ mollifierDefect S a`. -/
theorem mollifierDefect_floor_mul_rpow_of_prefix_cancel {S : Finset ℕ}
    (hS : ∀ d ∈ S, 1 ≤ d) {a : ℕ → ℝ} {y₁ : ℕ} (hy₁ : 1 ≤ y₁)
    (hcancel : ∀ n ∈ Finset.Icc 1 y₁, divisorSum S a n = if n = 1 then 1 else 0)
    {ρ : ℂ} (hρ0 : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    ((2 * ρ.re - 1) * ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 4) * (y₁ : ℝ) ^ (2 * ρ.re - 1) ≤
      mollifierDefect S a := by
  have hbase := mollifierDefect_ge_laplace_of_prefix_cancel hS hy₁ hcancel hρ0 hρ1 hz
  set w := valueAtOne S a
  set L : ℝ := Real.log y₁ with hLdef
  set A : ℝ := 2 * ρ.re - 1 with hAdef
  have hA : 0 < A := by rw [hAdef]; linarith
  have hy₁0 : (0 : ℝ) < y₁ := by exact_mod_cast hy₁
  have hρne : ρ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hρ0; norm_num at hρ0
  have hne : 1 - ρ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  have h1pos : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hne
  have hnorms : ‖ρ‖ ^ 2 = ‖1 - ρ‖ ^ 2 + A := by
    have h1 : (1 - ρ).re = 1 - ρ.re := by simp
    have h2 : (1 - ρ).im = -ρ.im := by simp
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, h1, h2, hAdef]
    ring
  set w₁ : ℝ := |w| * Real.exp ((1 - ρ.re) * L) with hw₁
  set a₁ : ℝ := ‖1 / ρ - (w : ℂ) * Complex.exp ((1 - ρ) * L) / (1 - ρ)‖ with ha₁
  set ε : ℝ := ‖1 - ρ‖⁻¹ with hε
  have htri : ‖ρ‖⁻¹ ≤ a₁ + w₁ * ε := by
    have h1 : (1 : ℂ) / ρ =
        (1 / ρ - (w : ℂ) * Complex.exp ((1 - ρ) * L) / (1 - ρ)) +
          (w : ℂ) * Complex.exp ((1 - ρ) * L) / (1 - ρ) := by ring
    have h2 := norm_add_le (1 / ρ - (w : ℂ) * Complex.exp ((1 - ρ) * L) / (1 - ρ))
      ((w : ℂ) * Complex.exp ((1 - ρ) * L) / (1 - ρ))
    have h3 : ‖(1 : ℂ) / ρ‖ = ‖ρ‖⁻¹ := by rw [norm_div, norm_one, one_div]
    have hre_exp : ((1 - ρ) * (L : ℂ)).re = (1 - ρ.re) * L := by simp [Complex.mul_re]
    have h4 : ‖(w : ℂ) * Complex.exp ((1 - ρ) * L) / (1 - ρ)‖ = w₁ * ε := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre_exp,
        div_eq_mul_inv, hw₁, hε]
    rw [← h1, h3, h4] at h2
    exact h2
  have hsq : ‖ρ‖⁻¹ ^ 2 ≤ (a₁ + w₁ * ε) ^ 2 := pow_le_pow_left₀ (by positivity) htri 2
  have hplane : (a₁ + w₁ * ε) ^ 2 * A ≤ (w₁ ^ 2 + A * a₁ ^ 2) * (1 + A * ε ^ 2) := by
    have h0 : (w₁ ^ 2 + A * a₁ ^ 2) * (1 + A * ε ^ 2) - (a₁ + w₁ * ε) ^ 2 * A =
        (w₁ - A * a₁ * ε) ^ 2 := by ring
    linarith [sq_nonneg (w₁ - A * a₁ * ε)]
  have h1Aε : 1 + A * ε ^ 2 = ‖ρ‖ ^ 2 * ε ^ 2 := by
    have hε1 : ‖1 - ρ‖ ^ 2 * ε ^ 2 = 1 := by
      rw [hε, ← mul_pow, mul_inv_cancel₀ h1pos.ne', one_pow]
    rw [hnorms, add_mul, hε1]
  have hkey : A * ‖ρ‖⁻¹ ^ 2 ≤ (w₁ ^ 2 + A * a₁ ^ 2) * (‖ρ‖ ^ 2 * ε ^ 2) := by
    rw [← h1Aε]
    calc A * ‖ρ‖⁻¹ ^ 2 ≤ A * (a₁ + w₁ * ε) ^ 2 := mul_le_mul_of_nonneg_left hsq hA.le
      _ = (a₁ + w₁ * ε) ^ 2 * A := by ring
      _ ≤ _ := hplane
  have hy₁w : (y₁ : ℝ) ^ A * w₁ ^ 2 = (y₁ : ℝ) * w ^ 2 := by
    rw [hw₁, mul_pow, sq_abs, hLdef, Real.rpow_def_of_pos hy₁0, ← Real.exp_nat_mul]
    have hexp : Real.exp (Real.log y₁ * A) * Real.exp (((2 : ℕ) : ℝ) * ((1 - ρ.re) * Real.log y₁)) =
        (y₁ : ℝ) := by
      rw [← Real.exp_add]
      have hlin : Real.log y₁ * A + ((2 : ℕ) : ℝ) * ((1 - ρ.re) * Real.log y₁) = Real.log y₁ := by
        rw [hAdef]; push_cast; ring
      rw [hlin, Real.exp_log hy₁0]
    calc Real.exp (Real.log y₁ * A) * (w ^ 2 * Real.exp (((2 : ℕ) : ℝ) * ((1 - ρ.re) * Real.log y₁)))
        = (Real.exp (Real.log y₁ * A) * Real.exp (((2 : ℕ) : ℝ) * ((1 - ρ.re) * Real.log y₁))) *
            w ^ 2 := by ring
      _ = (y₁ : ℝ) * w ^ 2 := by rw [hexp]
  have hscale : (y₁ : ℝ) ^ A * (w₁ ^ 2 + A * a₁ ^ 2) ≤ mollifierDefect S a := by
    have h1 : (y₁ : ℝ) ^ A * (w₁ ^ 2 + A * a₁ ^ 2) =
        (y₁ : ℝ) * w ^ 2 + A * (y₁ : ℝ) ^ A * a₁ ^ 2 := by
      rw [mul_add, hy₁w]
      ring
    linarith
  have hval : ((2 * ρ.re - 1) * ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 4) * (y₁ : ℝ) ^ (2 * ρ.re - 1) =
      (A * ‖ρ‖⁻¹ ^ 2 * (y₁ : ℝ) ^ A) / (‖ρ‖ ^ 2 * ε ^ 2) := by
    rw [← hAdef, hε]
    field_simp
  rw [hval, div_le_iff₀ (by positivity)]
  calc A * ‖ρ‖⁻¹ ^ 2 * (y₁ : ℝ) ^ A
      ≤ ((w₁ ^ 2 + A * a₁ ^ 2) * (‖ρ‖ ^ 2 * ε ^ 2)) * (y₁ : ℝ) ^ A :=
        mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hy₁0.le A)
    _ = ((y₁ : ℝ) ^ A * (w₁ ^ 2 + A * a₁ ^ 2)) * (‖ρ‖ ^ 2 * ε ^ 2) := by ring
    _ ≤ mollifierDefect S a * (‖ρ‖ ^ 2 * ε ^ 2) :=
        mul_le_mul_of_nonneg_right hscale (by positivity)

/-! ### Sharp Möbius specialization and sparse subsequence criteria -/

/-- **Amplified zero floor for the sharp Möbius truncation `M_y(s) = ∑_{d ≤ y} μ(d) d^{−s}`.** -/
theorem mollifierDefect_sharpCoeff_floor {y : ℕ} (hy : 1 ≤ y) {ρ : ℂ}
    (hρ0 : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    ((2 * ρ.re - 1) * ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 4) * (y : ℝ) ^ (2 * ρ.re - 1) ≤
      mollifierDefect (Finset.Icc 1 y) sharpCoeff := by
  have hS : ∀ d ∈ Finset.Icc 1 y, 1 ≤ d := fun d hd => (Finset.mem_Icc.mp hd).1
  refine mollifierDefect_floor_mul_rpow_of_prefix_cancel hS hy ?_ hρ0 hρ1 hz
  intro n hn
  obtain ⟨hn1, hny⟩ := Finset.mem_Icc.mp hn
  have hfil : (Finset.Icc 1 y).filter (· ∣ n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn1, (Nat.le_of_dvd hn1 hd).trans hny⟩, hd⟩
  unfold divisorSum
  rw [hfil, sum_divisors_sharpCoeff]

/-- **Sparse sharp-defect criterion for zero-free half-planes.** Unlike the linear-mollifier
criterion `xiZeroHalfPlaneBound_of_linearDefectRate` (which requires a bound along all dyadic
scales to eliminate `κ_y`), prefix cancellation of `μ` eliminates any offset: a bound along a
single unbounded sequence of cutoffs `y` (`∃ᶠ y in atTop`) already confines every zero of `ξ` to
`Re ρ ≤ ½ + β`. -/
theorem xiZeroHalfPlaneBound_of_frequently_sharpDefect_le {β : ℝ} (hβ0 : 0 ≤ β)
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ y : ℕ in atTop,
        mollifierDefect (Finset.Icc 1 y) sharpCoeff ≤ C * (y : ℝ) ^ (2 * β + η)) :
    _root_.RHTower.XiZeroHalfPlaneBound β := by
  intro ρ hρ
  by_contra hlt
  push Not at hlt
  have hz : riemannZeta ρ = 0 :=
    (_root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hρ).1
  have hρ1 : ρ.re < 1 := by
    by_contra h1
    exact _root_.RHTower.xi_ne_zero_of_one_le_re (not_lt.mp h1) hρ
  have hρ0 : 1 / 2 < ρ.re := by linarith
  set η : ℝ := ρ.re - (1 / 2 + β) with hηdef
  have hη0 : 0 < η := by rw [hηdef]; linarith
  obtain ⟨C, hC0, hfreq⟩ := h η hη0
  set c₀ : ℝ := (2 * ρ.re - 1) * ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 4 with hc₀def
  have hρne : ρ ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hρ0; norm_num at hρ0
  have h1ne : 1 - ρ ≠ 0 := by intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hc₀_pos : 0 < c₀ := by
    rw [hc₀def]
    have : 0 < 2 * ρ.re - 1 := by linarith
    have : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr h1ne
    have : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
    positivity
  have hbig : ∀ᶠ y : ℕ in atTop, 1 ≤ y ∧ C < c₀ * (y : ℝ) ^ η := by
    refine (eventually_ge_atTop 1).and ?_
    have htend : Tendsto (fun y : ℕ => c₀ * (y : ℝ) ^ η) atTop atTop :=
      ((tendsto_rpow_atTop hη0).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc₀_pos
    exact htend.eventually_gt_atTop C
  obtain ⟨y, hy_def, hy1, hy_gt⟩ := (hfreq.and_eventually hbig).exists
  have hypos : (0 : ℝ) < y := by exact_mod_cast hy1
  have hfl := mollifierDefect_sharpCoeff_floor hy1 hρ0 hρ1 hz
  rw [← hc₀def] at hfl
  have hexp_eq : 2 * ρ.re - 1 = (2 * β + η) + η := by rw [hηdef]; ring
  have hrpow : (y : ℝ) ^ (2 * ρ.re - 1) = (y : ℝ) ^ (2 * β + η) * (y : ℝ) ^ η := by
    rw [hexp_eq, Real.rpow_add hypos]
  have hpos_base : 0 < (y : ℝ) ^ (2 * β + η) := Real.rpow_pos_of_pos hypos _
  have hcontra : C * (y : ℝ) ^ (2 * β + η) < c₀ * (y : ℝ) ^ (2 * ρ.re - 1) := by
    rw [hrpow, show c₀ * ((y : ℝ) ^ (2 * β + η) * (y : ℝ) ^ η) =
      (c₀ * (y : ℝ) ^ η) * (y : ℝ) ^ (2 * β + η) by ring]
    exact mul_lt_mul_of_pos_right hy_gt hpos_base
  linarith

/-- **Sparse subpolynomial sharp-Möbius defect implies RH.** -/
theorem riemannHypothesis_of_frequently_sharpDefect_subpolynomial
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ y : ℕ in atTop,
        mollifierDefect (Finset.Icc 1 y) sharpCoeff ≤ C * (y : ℝ) ^ η) :
    RiemannHypothesis := by
  refine _root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr
    (xiZeroHalfPlaneBound_of_frequently_sharpDefect_le le_rfl fun η hη => ?_)
  simpa using h η hη

/-! ### Plancherel bridge to unweighted critical-line second moments -/

/-- The Cauchy-weighted critical-line integrand `‖1 − ζ(½+it) D(½+it)‖² / (¼ + t²)` is globally
integrable on `ℝ`. -/
theorem integrable_defectLineWeight {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) :
    Integrable fun t : ℝ =>
      ‖1 - riemannZeta (1 / 2 + t * I) * _root_.RHTower.realDirichletPoly S a (1 / 2 + t * I)‖ ^ 2 /
        (1 / 4 + t ^ 2) := by
  have hφ := integrable_defectPull hS a
  have hφ2 := memLp_two_defectPull hS a
  set u : Lp ℂ 2 (volume : Measure ℝ) := hφ2.toLp (defectPull S a)
  have hcoe : (u : ℝ → ℂ) =ᵐ[volume] defectPull S a := hφ2.coeFn_toLp
  have hint : Integrable (u : ℝ → ℂ) := hφ.congr hcoe.symm
  have hF : ((𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 (defectPull S a) := by
    refine (GaloisForLFunctions.HTGeometry.coeFn_fourierTransform_eq_fourierIntegral u hint).trans ?_
    filter_upwards with ξ
    exact Real.fourier_congr_ae hcoe ξ
  have hmemF : MemLp (𝓕 (defectPull S a)) 2 := (Lp.memLp (𝓕 u)).ae_eq hF
  have hFint : Integrable fun ξ : ℝ => ‖𝓕 (defectPull S a) ξ‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm
      (Real.continuous_fourierIntegral hφ).aestronglyMeasurable).mp hmemF
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcomp : Integrable fun t : ℝ => ‖𝓕 (defectPull S a) (t / (2 * Real.pi))‖ ^ 2 :=
    hFint.comp_div hπ
  refine hcomp.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [fourier_defectPull hS, norm_div, div_pow, _root_.RHTower.norm_half_add_mul_I,
    Real.sq_sqrt (by positivity)]

/-- **Plancherel interval bridge.** For every `T ≥ 1` and real Dirichlet polynomial `D` supported
on positive integers, the unweighted critical-line second moment `∫_1^T ‖ζ(½+it) D(½+it)‖² dt` is
controlled by `2(T − 1) + 4π(¼ + T²) · mollifierDefect S a`. -/
theorem integral_normSq_zeta_realDirichletPoly_le_of_mollifierDefect {S : Finset ℕ}
    (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in (1 : ℝ)..T,
        ‖riemannZeta (1 / 2 + t * I) * _root_.RHTower.realDirichletPoly S a (1 / 2 + t * I)‖ ^ 2 ≤
      2 * (T - 1) + 4 * Real.pi * (1 / 4 + T ^ 2) * mollifierDefect S a := by
  set g : ℝ → ℝ := fun t =>
    ‖1 - riemannZeta (1 / 2 + t * I) * _root_.RHTower.realDirichletPoly S a (1 / 2 + t * I)‖ ^ 2 /
      (1 / 4 + t ^ 2) with hgdef
  have hg_int : Integrable g := integrable_defectLineWeight hS a
  have hπ : 0 < 2 * Real.pi := by positivity
  have hg_total : ∫ t : ℝ, g t = 2 * Real.pi * mollifierDefect S a := by
    have heq := mollifierDefect_eq hS a
    rw [← hgdef] at heq
    calc ∫ t : ℝ, g t = 2 * Real.pi * ((2 * Real.pi)⁻¹ * ∫ t : ℝ, g t) := by
          rw [← mul_assoc, mul_inv_cancel₀ hπ.ne', one_mul]
      _ = 2 * Real.pi * mollifierDefect S a := by rw [heq]
  have hf_cont : ContinuousOn
      (fun t : ℝ => ‖riemannZeta (1 / 2 + t * I) *
        _root_.RHTower.realDirichletPoly S a (1 / 2 + t * I)‖ ^ 2) (Icc 1 T) := by
    intro t _
    have hne : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    have hcζ : ContinuousAt (fun t : ℝ => riemannZeta (1 / 2 + (t : ℂ) * I)) t :=
      ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => 1 / 2 + (t : ℂ) * I)
        (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)
    have hcD : Continuous fun t : ℝ => _root_.RHTower.realDirichletPoly S a (1 / 2 + (t : ℂ) * I) := by
      unfold _root_.RHTower.realDirichletPoly
      refine continuous_finset_sum S fun n hn => ?_
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show 0 < n from hS n hn).ne'
      refine continuous_const.mul ?_
      exact Continuous.const_cpow (by fun_prop) (Or.inl hn0)
    exact ((hcζ.mul hcD.continuousAt).norm.pow 2).continuousWithinAt
  have hrhs_int : IntervalIntegrable (fun t : ℝ => 2 + 2 * (1 / 4 + T ^ 2) * g t) volume 1 T :=
    intervalIntegrable_const.add ((hg_int.const_mul (2 * (1 / 4 + T ^ 2))).intervalIntegrable 1 T)
  have hmono : ∫ t in (1 : ℝ)..T,
      ‖riemannZeta (1 / 2 + t * I) * _root_.RHTower.realDirichletPoly S a (1 / 2 + t * I)‖ ^ 2 ≤
      ∫ t in (1 : ℝ)..T, (2 + 2 * (1 / 4 + T ^ 2) * g t) := by
    refine intervalIntegral.integral_mono_on hT (hf_cont.intervalIntegrable_of_Icc hT) hrhs_int
      fun t ht => ?_
    set z : ℂ := riemannZeta (1 / 2 + t * I) * _root_.RHTower.realDirichletPoly S a (1 / 2 + t * I)
    have htri : ‖z‖ ≤ 1 + ‖1 - z‖ := by
      have h1 : z = 1 - (1 - z) := by ring
      have h2 := norm_sub_le (1 : ℂ) (1 - z)
      rw [← h1, norm_one] at h2
      exact h2
    have hsq1 : ‖z‖ ^ 2 ≤ 2 + 2 * ‖1 - z‖ ^ 2 := by
      have h3 := pow_le_pow_left₀ (norm_nonneg z) htri 2
      nlinarith [sq_nonneg (1 - ‖1 - z‖)]
    have ht_sq : 1 / 4 + t ^ 2 ≤ 1 / 4 + T ^ 2 := by
      have : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by linarith [ht.1]) ht.2 2
      linarith
    have hden_pos : 0 < 1 / 4 + t ^ 2 := by positivity
    have h1z : ‖1 - z‖ ^ 2 ≤ (1 / 4 + T ^ 2) * g t := by
      simp only [hgdef]
      have heq : ‖1 - z‖ ^ 2 = (1 / 4 + t ^ 2) * (‖1 - z‖ ^ 2 / (1 / 4 + t ^ 2)) := by
        field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right ht_sq (div_nonneg (sq_nonneg _) hden_pos.le)
    linarith
  have heval : ∫ t in (1 : ℝ)..T, (2 + 2 * (1 / 4 + T ^ 2) * g t) =
      2 * (T - 1) + 2 * (1 / 4 + T ^ 2) * ∫ t in (1 : ℝ)..T, g t := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
        ((hg_int.const_mul _).intervalIntegrable 1 T),
      intervalIntegral.integral_const, smul_eq_mul, mul_comm (T - 1) 2,
      intervalIntegral.integral_const_mul]
  have hsub_int : ∫ t in (1 : ℝ)..T, g t ≤ ∫ t : ℝ, g t := by
    rw [intervalIntegral.integral_of_le hT]
    exact setIntegral_le_integral hg_int (Filter.Eventually.of_forall fun t => by
      simp only [hgdef]; positivity)
  calc ∫ t in (1 : ℝ)..T,
        ‖riemannZeta (1 / 2 + t * I) * _root_.RHTower.realDirichletPoly S a (1 / 2 + t * I)‖ ^ 2
      ≤ ∫ t in (1 : ℝ)..T, (2 + 2 * (1 / 4 + T ^ 2) * g t) := hmono
    _ = 2 * (T - 1) + 2 * (1 / 4 + T ^ 2) * ∫ t in (1 : ℝ)..T, g t := heval
    _ ≤ 2 * (T - 1) + 2 * (1 / 4 + T ^ 2) * ∫ t : ℝ, g t :=
        add_le_add_left (mul_le_mul_of_nonneg_left hsub_int (by positivity)) _
    _ = 2 * (T - 1) + 4 * Real.pi * (1 / 4 + T ^ 2) * mollifierDefect S a := by
        rw [hg_total]; ring

end GaloisForLFunctions.ArithmeticProduction
