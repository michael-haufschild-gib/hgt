import GaloisForLFunctions.RHTower.SquarefreeCountingAsymptotic
import GaloisForLFunctions.RHTower.Sieve.SquarefreeCount
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor

/-!
# Mellin response of the squarefree counting discrepancy

The literal discrepancy `sum_{n ≤ x} μ(n)^2 - (6/π²)x`, restricted to `x > 1`, has an
absolutely convergent Mellin moment throughout `Re s > 1/2`. Its pole-cleared identity
retains the lower endpoint and extends the classical squarefree Dirichlet quotient.
The associated dilation response equals one exactly at reflected zeta zeros in the
open subcritical strip. No cancellation bound for a Liouville source is asserted.
-/

open Filter Topology MeasureTheory Set Asymptotics Complex
open scoped BigOperators

namespace RHTower.SquarefreeDiscrepancy
noncomputable section

/-- Full squarefree count at a real cutoff, with the natural floor convention. -/
def count (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2

/-- The full counting discrepancy from its exact asymptotic density. -/
def error (x : ℝ) : ℝ := count x - Sieve.squarefreeDensity * x

/-- Complex discrepancy restricted to the integration range above one. -/
def kernel : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun x => (error x : ℂ))

/-- Mellin moment with the Dirichlet-series sign convention. -/
def moment (s : ℂ) : ℂ := mellin kernel (-s)

private theorem density_nonneg : 0 ≤ Sieve.squarefreeDensity := by
  rw [Sieve.squarefreeDensity_eq]
  positivity

private theorem density_le_one : Sieve.squarefreeDensity ≤ 1 := by
  rw [Sieve.squarefreeDensity_eq]
  have hp := Real.pi_gt_three
  have hp2 : 0 < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  rw [div_le_iff₀ hp2]
  nlinarith

/-- The integer-cutoff square-root estimate, including the real-cutoff endpoint error. -/
theorem abs_error_le {x : ℝ} (hx : 1 ≤ x) :
    |error x| ≤ 4 * Real.sqrt x := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
  have hfloor := Nat.floor_le hx0
  have hgap := Nat.lt_floor_add_one x
  have hcount := RHTower.abs_sum_moebius_sq_sub_le hN
  rw [← Sieve.squarefreeDensity_eq] at hcount
  have hsqrt : Real.sqrt (⌊x⌋₊ : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hfloor
  have hsqrt1 : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
  have hdiff : |Sieve.squarefreeDensity * ((⌊x⌋₊ : ℝ) - x)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg density_nonneg, abs_of_nonpos (sub_nonpos.mpr hfloor)]
    have hnonneg : 0 ≤ -((⌊x⌋₊ : ℝ) - x) := by linarith
    calc
      Sieve.squarefreeDensity * -((⌊x⌋₊ : ℝ) - x)
          ≤ 1 * -((⌊x⌋₊ : ℝ) - x) := mul_le_mul_of_nonneg_right density_le_one hnonneg
      _ ≤ 1 := by linarith
  calc
    |error x| = |(count x - Sieve.squarefreeDensity * (⌊x⌋₊ : ℝ)) +
        Sieve.squarefreeDensity * ((⌊x⌋₊ : ℝ) - x)| := by congr 1; dsimp [error]; ring
    _ ≤ |count x - Sieve.squarefreeDensity * (⌊x⌋₊ : ℝ)| +
        |Sieve.squarefreeDensity * ((⌊x⌋₊ : ℝ) - x)| := abs_add_le _ _
    _ ≤ 3 * Real.sqrt (⌊x⌋₊ : ℝ) + 1 := add_le_add hcount hdiff
    _ ≤ 4 * Real.sqrt x := by linarith

/-- Global envelope of the restricted discrepancy. -/
theorem norm_kernel_le (x : ℝ) : ‖kernel x‖ ≤ 4 * Real.sqrt x := by
  by_cases hx : 1 < x
  · simpa [kernel, hx, Real.norm_eq_abs] using abs_error_le hx.le
  · simp [kernel, hx, Real.sqrt_nonneg]

/-- Floor-count jumps preserve measurability of the full discrepancy. -/
theorem measurable_error : Measurable error := by
  have hc : Measurable count :=
    (measurable_of_countable
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℝ)^2)).comp
        Nat.measurable_floor
  exact hc.sub (measurable_const.mul measurable_id)

/-- The restricted complex discrepancy is measurable. -/
theorem measurable_kernel : Measurable kernel :=
  (Complex.continuous_ofReal.measurable.comp measurable_error).indicator measurableSet_Ioi

/-- The discrepancy is locally integrable despite its counting jumps. -/
theorem locallyIntegrableOn_kernel : LocallyIntegrableOn kernel (Ioi 0) := by
  have hcont : Continuous (fun x : ℝ => 4 * Real.sqrt x) := continuous_const.mul Real.continuous_sqrt
  refine (hcont.continuousOn.locallyIntegrableOn measurableSet_Ioi).mono
    measurable_kernel.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ 4 * Real.sqrt x by positivity)]
  exact norm_kernel_le x

/-- Square-root growth at infinity of the restricted discrepancy. -/
theorem kernel_isBigO_atTop : kernel =O[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx _)]
  simpa only [Real.sqrt_eq_rpow] using norm_kernel_le x

/-- Restriction above one makes the kernel vanish in a neighborhood of zero. -/
theorem kernel_isBigO_zero (b : ℝ) :
    kernel =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-b)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with x hx
  simp only [kernel, indicator_of_notMem (show x ∉ Ioi (1 : ℝ) by exact not_lt.mpr hx.le), norm_zero]
  positivity

/-- The actual discrepancy moment is holomorphic to the right of the half-line. -/
theorem differentiableAt_moment {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ moment s := by
  have hm : DifferentiableAt ℂ (mellin kernel) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_kernel
      (a := -(1/2 : ℝ)) (b := -s.re - 1)
      (by simpa using kernel_isBigO_atTop) (by simpa using neg_lt_neg hs)
      (kernel_isBigO_zero _) (by simp)
  exact hm.comp s differentiableAt_id.neg

private theorem weighted_kernel_eq_indicator (s : ℂ) :
    (fun x : ℝ => (x : ℂ) ^ (-s - 1) * kernel x) =
      (Ioi (1 : ℝ)).indicator (fun x => (error x : ℂ) * (x : ℂ) ^ (-(s + 1))) := by
  funext x
  by_cases hx : 1 < x
  · simp [kernel, hx, show -s - 1 = -(s + 1) by ring, mul_comm]
  · simp [kernel, hx]

/-- Integral expression retaining the exact lower endpoint. -/
theorem moment_eq_integral (s : ℂ) :
    moment s = ∫ x in Ioi (1 : ℝ), (error x : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  change (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-s - 1) * kernel x) = _
  rw [weighted_kernel_eq_indicator, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))]

/-- Absolute integrability of the literal discrepancy moment. -/
theorem integrable_moment {s : ℂ} (hs : 1/2 < s.re) :
    IntegrableOn (fun x : ℝ => (error x : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have h : MellinConvergent kernel (-s) :=
    mellinConvergent_of_isBigO_rpow locallyIntegrableOn_kernel
      (a := -(1/2 : ℝ)) (b := -s.re - 1)
      (by simpa using kernel_isBigO_atTop) (by simpa using neg_lt_neg hs)
      (kernel_isBigO_zero _) (by simp)
  change IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * kernel x) (Ioi 0) at h
  rw [weighted_kernel_eq_indicator, integrableOn_indicator_iff measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))] at h
  exact h

private theorem square_coeff_le_one (n : ℕ) :
    ((ArithmeticFunction.moebius n : ℤ) : ℝ)^2 ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

private theorem coeff_sum_bigO :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius n : ℤ) : ℝ)^2) =O[atTop]
        (fun N : ℕ => (N : ℝ)^(1 : ℝ)) := by
  refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun N => ?_)
  rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun n _ => sq_nonneg _), abs_of_nonneg (Nat.cast_nonneg N),
    one_mul]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) :=
      Finset.sum_le_sum fun n _ => square_coeff_le_one n
    _ = (N : ℝ) := by simp

private theorem moment_eq_absConv {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s / riemannZeta (2*s) =
      s * (moment s + (Sieve.squarefreeDensity : ℂ) / (s - 1)) := by
  have hrep := LSeries_eq_mul_integral_of_nonneg
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)^2)
    zero_le_one hs coeff_sum_bigO (fun n => sq_nonneg _)
  have hseries :
      LSeries (fun n => ((((ArithmeticFunction.moebius n : ℤ) : ℝ)^2 : ℝ) : ℂ)) s =
        riemannZeta s / riemannZeta (2*s) := by
    simpa only [ArithmeticFunction.pmul_apply, Int.cast_mul, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_intCast, pow_two] using RHTower.LSeries_squarefree_eq_riemannZeta_div hs
  rw [hseries] at hrep
  have hrep' : riemannZeta s / riemannZeta (2*s) =
      s * ∫ x in Ioi (1 : ℝ), (count x : ℂ) * (x : ℂ)^(-(s+1)) := by
    simpa [count] using hrep
  have hsneg : (-s).re < -1 := by simpa using neg_lt_neg hs
  have hpow : ∀ x : ℝ, 1 < x →
      (x : ℂ)^(-s) = (x : ℂ)*(x : ℂ)^(-(s+1)) := by
    intro x hx
    calc
      _ = (x : ℂ)^(1 + (-(s+1))) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ (by exact_mod_cast (show x ≠ 0 by linarith)),
        Complex.cpow_one]
  have hsplit : (∫ x in Ioi (1 : ℝ), (count x : ℂ) * (x : ℂ)^(-(s+1))) =
      moment s + (Sieve.squarefreeDensity : ℂ) / (s - 1) := by
    calc
      _ = ∫ x in Ioi (1 : ℝ),
          (error x : ℂ)*(x : ℂ)^(-(s+1)) +
            (Sieve.squarefreeDensity : ℂ)*(x : ℂ)^(-s) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rw [hpow x hx]
        simp only [error, Complex.ofReal_sub, Complex.ofReal_mul]
        ring
      _ = moment s + (Sieve.squarefreeDensity : ℂ)*
          (∫ x in Ioi (1 : ℝ), (x : ℂ)^(-s)) := by
        rw [integral_add (integrable_moment (by linarith))
          ((integrableOn_Ioi_cpow_of_lt hsneg zero_lt_one).const_mul _),
          integral_const_mul, ← moment_eq_integral]
      _ = _ := by
        rw [integral_Ioi_cpow_of_lt hsneg zero_lt_one]
        simp only [Complex.ofReal_one, Complex.one_cpow]
        rw [show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
        ring
  rw [hrep', hsplit]

private theorem convex_halfPlane : Convex ℝ {s : ℂ | 1/2 < s.re} := by
  intro x hx y hy a b ha hb hab
  change (1/2 : ℝ) < x.re at hx
  change (1/2 : ℝ) < y.re at hy
  change (1/2 : ℝ) < (a • x + b • y).re
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  have hax : 0 ≤ a * (x.re - 1/2) := mul_nonneg ha (by linarith)
  have hby : 0 ≤ b * (y.re - 1/2) := mul_nonneg hb (by linarith)
  rcases lt_or_eq_of_le ha with ha0 | ha0
  · have hax' : 0 < a * (x.re - 1/2) := mul_pos ha0 (by linarith)
    nlinarith
  · have hb0 : 0 < b := by linarith
    have hby' : 0 < b * (y.re - 1/2) := mul_pos hb0 (by linarith)
    nlinarith

/-- Pole-cleared squarefree Mellin identity, valid also at the zeta pole. -/
theorem moment_identity {s : ℂ} (hs : 1/2 < s.re) :
    (s-1)*s*moment s*riemannZeta (2*s) =
      zetaResidueUnit s - (Sieve.squarefreeDensity : ℂ)*s*riemannZeta (2*s) := by
  let U : Set ℂ := {s | 1/2 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hm : AnalyticOnNhd ℂ moment U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    exact (differentiableAt_moment hz).differentiableWithinAt
  have hz : AnalyticOnNhd ℂ (fun z => riemannZeta (2*z)) U := by
    intro z hz
    have hn : 2*z ≠ 1 := by
      intro h
      have he := congrArg Complex.re h
      simp only [two_mul, Complex.add_re, Complex.one_re] at he
      change 1/2 < z.re at hz
      linarith
    exact (analyticOn_riemannZeta (2*z) hn).comp (by fun_prop)
  have hl : AnalyticOnNhd ℂ
      (fun z => (z-1)*z*moment z*riemannZeta (2*z)) U := by
    intro z hzU
    exact (((analyticAt_id.sub analyticAt_const).mul analyticAt_id).mul
      (hm z hzU)).mul (hz z hzU)
  have hr : AnalyticOnNhd ℂ
      (fun z => zetaResidueUnit z - (Sieve.squarefreeDensity : ℂ)*z*riemannZeta (2*z)) U := by
    intro z hzU
    exact (analyticAt_zetaResidueUnit z).sub
      ((analyticAt_const.mul analyticAt_id).mul (hz z hzU))
  have hevent :
      (fun z => (z-1)*z*moment z*riemannZeta (2*z)) =ᶠ[𝓝 (2 : ℂ)]
        (fun z => zetaResidueUnit z - (Sieve.squarefreeDensity : ℂ)*z*riemannZeta (2*z)) := by
    have hgt : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with z hz1
    have hn : z ≠ 1 := by intro h; subst z; norm_num at hz1
    have hd : z - 1 ≠ 0 := sub_ne_zero.mpr hn
    have hz2 : riemannZeta (2*z) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simp only [two_mul, Complex.add_re]; linarith)
    have h := congrArg (fun w : ℂ => w*(z-1)*riemannZeta (2*z)) (moment_eq_absConv hz1)
    field_simp [hd, hz2] at h
    rw [zetaResidueUnit, Function.update_of_ne hn]
    linear_combination -h
  exact hl.eqOn_of_preconnected_of_eventuallyEq hr convex_halfPlane.isPreconnected
    (show (2 : ℂ) ∈ U by norm_num [U]) hevent hs

/-- The exact squarefree zeta quotient with the density pole subtracted. -/
theorem moment_eq_quotient {s : ℂ} (hs : 1/2 < s.re) (hs1 : s ≠ 1) :
    moment s = riemannZeta s / (s*riemannZeta (2*s)) -
      (Sieve.squarefreeDensity : ℂ)/(s-1) := by
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  have hd : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  have hz : riemannZeta (2*s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp only [two_mul, Complex.add_re]; linarith)
  have h := moment_identity hs
  rw [zetaResidueUnit, Function.update_of_ne hs1] at h
  rw [eq_sub_iff_add_eq, eq_div_iff (mul_ne_zero hs0 hz)]
  apply mul_left_cancel₀ hd
  calc
    (s-1)*((moment s + (Sieve.squarefreeDensity : ℂ)/(s-1))*(s*riemannZeta (2*s))) =
        (s-1)*s*moment s*riemannZeta (2*s) +
          (Sieve.squarefreeDensity : ℂ)*s*riemannZeta (2*s) := by
      field_simp [hd]
    _ = (s-1)*riemannZeta s := by linear_combination h

/-- Response of the actual squarefree discrepancy to a dilation power. -/
def response (a : ℂ) : ℂ := a / (Sieve.squarefreeDensity : ℂ) * moment (1-a)

private theorem density_pos : 0 < Sieve.squarefreeDensity := by
  rw [Sieve.squarefreeDensity_eq]
  positivity

/-- Exact response of the signed discrepancy to a subcritical complex power. -/
theorem response_eq {a : ℂ} (ha0 : 0 < a.re) (ha : a.re < 1/2) :
    response a = 1 + a*riemannZeta (1-a) /
      ((Sieve.squarefreeDensity : ℂ)*(1-a)*riemannZeta (2*(1-a))) := by
  have hn0 : a ≠ 0 := by intro h; subst a; norm_num at ha0
  have hn1 : 1-a ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  have hrho : (Sieve.squarefreeDensity : ℂ) ≠ 0 := by exact_mod_cast density_pos.ne'
  have hs : 1/2 < (1-a).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hs1 : 1-a ≠ 1 := by intro h; apply hn0; linear_combination -h
  have hz : riemannZeta (2*(1-a)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp only [two_mul, Complex.add_re]; linarith)
  rw [response, moment_eq_quotient hs hs1]
  rw [show 1-a-1 = -a by ring]
  field_simp [hrho, hn0, hn1, hz]
  ring

/-- Unit response modes are precisely reflected off-line zeta zeros. -/
theorem response_eq_one_iff {a : ℂ} (ha0 : 0 < a.re) (ha : a.re < 1/2) :
    response a = 1 ↔ riemannZeta (1-a) = 0 := by
  have hn0 : a ≠ 0 := by intro h; subst a; norm_num at ha0
  have hn1 : 1-a ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  have hrho : (Sieve.squarefreeDensity : ℂ) ≠ 0 := by exact_mod_cast density_pos.ne'
  have hz : riemannZeta (2*(1-a)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      simp only [two_mul, Complex.add_re, Complex.sub_re, Complex.one_re]
      linarith)
  rw [response_eq ha0 ha]
  simp only [add_eq_left, div_eq_zero_iff, mul_eq_zero, hn0, hn1, hrho, hz,
    or_false, false_or]

end
end RHTower.SquarefreeDiscrepancy
