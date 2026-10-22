import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Connes--Consani's bounded-variation Fourier truncation lemma

This file formalizes Lemma `fouriertruncated1` from Connes--Consani,
*Spectral triples and zeta-cycles* (2021).  A positive-half-line function is encoded by its
zero extension to `ℝ`; no conclusion about its Poisson sum or multiplicative periodization is
included in the input class.

The hard estimate is the Riemann-sum cancellation bound

`|∑ n, f (u * (n + 1))| ≤ Var(f)`.

It is proved from bounded variation and the zero integral by comparing finite left Riemann sums
with interval integrals and then passing to the infinite sum.  This is the Stieltjes argument in
the paper, recast using mathlib's total-variation API.
-/

open Filter MeasureTheory Set Topology
open scoped FourierTransform
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Exact input class of Connes--Consani Lemma `fouriertruncated1`, represented by the zero
extension from `(0, ∞)` to `ℝ`.  `rapidDecay` is the paper's rapid decay at infinity and
`smallQuadratic` is its `O(u²)` condition at zero. -/
structure CCMFourierTruncatedInput where
  toFun : ℝ → ℝ
  zero_of_nonpos : ∀ ⦃x : ℝ⦄, x ≤ 0 → toFun x = 0
  boundedVariation : BoundedVariationOn toFun Set.univ
  smallQuadratic : ∃ C : ℝ, 0 ≤ C ∧
    ∀ ⦃x : ℝ⦄, 0 < x → x ≤ 1 → |toFun x| ≤ C * x ^ 2
  rapidDecay : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ ⦃x : ℝ⦄, 1 ≤ x → |toFun x| ≤ C / x ^ N
  integrableOn_pos : IntegrableOn toFun (Ioi 0)
  integral_zero : ∫ x in Ioi 0, toFun x = 0

instance : CoeFun CCMFourierTruncatedInput fun _ => ℝ → ℝ :=
  ⟨CCMFourierTruncatedInput.toFun⟩

theorem CCMFourierTruncatedInput.zero (f : CCMFourierTruncatedInput) : f 0 = 0 :=
  f.zero_of_nonpos le_rfl

/-- Total variation constant used in the paper's Riemann-sum estimate. -/
def ccmFourierTruncatedVariation (f : CCMFourierTruncatedInput) : ℝ :=
  (eVariationOn f Set.univ).toReal

theorem ccmFourierTruncatedVariation_nonneg (f : CCMFourierTruncatedInput) :
    0 ≤ ccmFourierTruncatedVariation f :=
  ENNReal.toReal_nonneg

theorem abs_ccmFourierTruncatedInput_le_variation
    (f : CCMFourierTruncatedInput) (x : ℝ) :
    |f x| ≤ ccmFourierTruncatedVariation f := by
  rw [← Real.dist_0_eq_abs, ← f.zero]
  exact f.boundedVariation.dist_le (mem_univ x) (mem_univ 0)

/-- The raw positive Riemann sum `∑_{n≥1} f(nu)`. -/
def ccmFourierTruncatedPoissonValue (f : CCMFourierTruncatedInput) (u : ℝ) : ℝ :=
  ∑' n : ℕ, f (u * ((n : ℝ) + 1))

/-- Rapid decay makes the positive Riemann sum absolutely convergent at every positive scale. -/
theorem ccmFourierTruncatedPoisson_summable
    (f : CCMFourierTruncatedInput) {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℕ => f (u * ((n : ℝ) + 1)) := by
  obtain ⟨C, hC, hdecay⟩ := f.rapidDecay 2
  have hmajorant : Summable fun n : ℕ =>
      (C / u ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
    have hp : Summable fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2) := by
      have hp0 : Summable fun n : ℕ => 1 / ((n : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)
      simpa [Function.comp_def] using hp0.comp_injective Nat.succ_injective
    exact hp.mul_left (C / u ^ 2)
  refine hmajorant.of_norm_bounded_eventually_nat ?_
  filter_upwards [eventually_ge_atTop (Nat.ceil (1 / u))] with n hn
  have hun : 1 ≤ u * ((n : ℝ) + 1) := by
    have hceil : 1 / u ≤ (Nat.ceil (1 / u) : ℝ) := Nat.le_ceil _
    have hnreal : (Nat.ceil (1 / u) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    calc
      1 = u * (1 / u) := by field_simp
      _ ≤ u * (Nat.ceil (1 / u) : ℝ) := mul_le_mul_of_nonneg_left hceil hu.le
      _ ≤ u * ((n : ℝ) + 1) := by nlinarith
  have h := hdecay hun
  rw [Real.norm_eq_abs]
  refine h.trans ?_
  field_simp
  exact le_rfl

theorem ccmFourierTruncatedPoissonValue_zero
    (f : CCMFourierTruncatedInput) :
    ccmFourierTruncatedPoissonValue f 0 = 0 := by
  simp [ccmFourierTruncatedPoissonValue, f.zero]

theorem CCMFourierTruncatedInput.intervalIntegrable_of_nonneg
    (f : CCMFourierTruncatedInput) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact f.integrableOn_pos.mono_set fun x hx => lt_of_le_of_lt ha hx.1

/-- Error of one left Riemann rectangle, bounded by the variation on that rectangle. -/
theorem ccmFourierTruncated_single_interval_error
    (f : CCMFourierTruncatedInput) {u : ℝ} (hu : 0 < u) (n : ℕ) :
    |u * f (u * (n : ℝ)) -
        ∫ x in (u * (n : ℝ))..(u * ((n : ℝ) + 1)), f x| ≤
      u * (eVariationOn f (Icc (u * (n : ℝ)) (u * ((n : ℝ) + 1)))).toReal := by
  let a : ℝ := u * (n : ℝ)
  let b : ℝ := u * ((n : ℝ) + 1)
  have ha : 0 ≤ a := mul_nonneg hu.le (Nat.cast_nonneg n)
  have hab : a ≤ b := by dsimp [a, b]; nlinarith
  have hba : b - a = u := by dsimp [a, b]; ring
  have hint : IntervalIntegrable f volume a b :=
    f.intervalIntegrable_of_nonneg ha hab
  have hconst : IntervalIntegrable (fun _ : ℝ => f a) volume a b :=
    intervalIntegrable_const
  have hlocal : BoundedVariationOn f (Icc a b) :=
    f.boundedVariation.mono (subset_univ _)
  have heq :
      u * f a - ∫ x in a..b, f x =
        ∫ x in a..b, (f a - f x) := by
    rw [intervalIntegral.integral_sub hconst hint,
      intervalIntegral.integral_const, hba, smul_eq_mul]
  change |u * f a - ∫ x in a..b, f x| ≤
    u * (eVariationOn f (Icc a b)).toReal
  rw [heq, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := (eVariationOn f (Icc a b)).toReal)
    (f := fun x => f a - f x) fun x hx => ?_).trans_eq ?_
  · have hx' : x ∈ Icc a b := by
      rw [uIoc_of_le hab] at hx
      exact Ioc_subset_Icc_self hx
    simpa [Real.norm_eq_abs, Real.dist_eq] using
      hlocal.dist_le (left_mem_Icc.mpr hab) hx'
  · rw [hba, abs_of_pos hu]
    exact mul_comm _ _

/-- Finite left Riemann sums differ from the corresponding interval integral by at most
`u * Var(f)`, uniformly in the number of rectangles. -/
theorem ccmFourierTruncated_finite_riemann_error
    (f : CCMFourierTruncatedInput) {u : ℝ} (hu : 0 < u) (N : ℕ) :
    |u * (∑ n ∈ Finset.range N, f (u * (n : ℝ))) -
        ∫ x in (0 : ℝ)..(u * (N : ℝ)), f x| ≤
      u * ccmFourierTruncatedVariation f := by
  let a : ℕ → ℝ := fun n => u * (n : ℝ)
  have ha_mono : Monotone a := by
    intro m n hmn
    dsimp [a]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) hu.le
  have hint (n : ℕ) : IntervalIntegrable f volume (a n) (a (n + 1)) := by
    apply f.intervalIntegrable_of_nonneg
    · exact mul_nonneg hu.le (Nat.cast_nonneg n)
    · exact ha_mono n.le_succ
  have hintegral :
      ∑ n ∈ Finset.range N, ∫ x in a n..a (n + 1), f x =
        ∫ x in a 0..a N, f x := by
    rw [← Nat.Ico_zero_eq_range]
    exact intervalIntegral.sum_integral_adjacent_intervals_Ico (m := 0) (n := N)
      (Nat.zero_le N) fun n hn => hint n
  have hsum_eq :
      u * (∑ n ∈ Finset.range N, f (a n)) - ∫ x in a 0..a N, f x =
        ∑ n ∈ Finset.range N,
          (u * f (a n) - ∫ x in a n..a (n + 1), f x) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hintegral]
  have hvariation_finite (n : ℕ) :
      eVariationOn f (Icc (a n) (a (n + 1))) ≠ ⊤ :=
    f.boundedVariation.mono (subset_univ _)
  have hvariation_sum :
      (∑ n ∈ Finset.range N,
          (eVariationOn f (Icc (a n) (a (n + 1)))).toReal) =
        (eVariationOn f (Icc (a 0) (a N))).toReal := by
    rw [← ENNReal.toReal_sum fun n hn => hvariation_finite n,
      eVariationOn.sum' f ha_mono]
  have hvariation_le :
      (∑ n ∈ Finset.range N,
          (eVariationOn f (Icc (a n) (a (n + 1)))).toReal) ≤
        ccmFourierTruncatedVariation f := by
    rw [hvariation_sum, ccmFourierTruncatedVariation]
    exact ENNReal.toReal_mono f.boundedVariation
      (eVariationOn.mono f (subset_univ _))
  simp only [a, Nat.cast_zero, mul_zero] at hsum_eq ⊢
  rw [hsum_eq, ← Real.norm_eq_abs]
  calc
    ‖∑ n ∈ Finset.range N,
        (u * f (a n) - ∫ x in a n..a (n + 1), f x)‖
        ≤ ∑ n ∈ Finset.range N,
            ‖u * f (a n) - ∫ x in a n..a (n + 1), f x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N,
          u * (eVariationOn f (Icc (a n) (a (n + 1)))).toReal := by
      apply Finset.sum_le_sum
      intro n hn
      simpa [a, Nat.cast_add, Nat.cast_one] using
        ccmFourierTruncated_single_interval_error f hu n
    _ = u * ∑ n ∈ Finset.range N,
          (eVariationOn f (Icc (a n) (a (n + 1)))).toReal := by
      rw [Finset.mul_sum]
    _ ≤ u * ccmFourierTruncatedVariation f :=
      mul_le_mul_of_nonneg_left hvariation_le hu.le

/-- The Stieltjes/Riemann-sum cancellation estimate of `fouriertruncated1(i)`.  The bound is
uniform in the positive scale `u`. -/
theorem abs_ccmFourierTruncatedPoissonValue_le_variation
    (f : CCMFourierTruncatedInput) {u : ℝ} (hu : 0 < u) :
    |ccmFourierTruncatedPoissonValue f u| ≤ ccmFourierTruncatedVariation f := by
  have hshift : Summable fun n : ℕ => f (u * ((n : ℝ) + 1)) :=
    ccmFourierTruncatedPoisson_summable f hu
  have hsum0 : Summable fun n : ℕ => f (u * (n : ℝ)) := by
    apply (summable_nat_add_iff 1).1
    simpa [Nat.cast_add, Nat.cast_one] using hshift
  have htsum0 :
      (∑' n : ℕ, f (u * (n : ℝ))) = ccmFourierTruncatedPoissonValue f u := by
    rw [hsum0.tsum_eq_zero_add]
    simp only [Nat.cast_zero, mul_zero, f.zero, zero_add,
      Nat.cast_add, Nat.cast_one, ccmFourierTruncatedPoissonValue]
  have hsum_lim :
      Tendsto (fun N : ℕ => u * ∑ n ∈ Finset.range N, f (u * (n : ℝ))) atTop
        (𝓝 (u * ccmFourierTruncatedPoissonValue f u)) := by
    rw [← htsum0]
    exact hsum0.hasSum.tendsto_sum_nat.const_mul u
  have hscale_top : Tendsto (fun N : ℕ => u * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hu
  have hintegral_lim :
      Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..(u * (N : ℝ)), f x) atTop
        (𝓝 (∫ x in Ioi 0, f x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 f.integrableOn_pos hscale_top
  have herror_lim :
      Tendsto
        (fun N : ℕ =>
          |u * (∑ n ∈ Finset.range N, f (u * (n : ℝ))) -
            ∫ x in (0 : ℝ)..(u * (N : ℝ)), f x|)
        atTop (𝓝 |u * ccmFourierTruncatedPoissonValue f u|) := by
    convert (hsum_lim.sub hintegral_lim).abs using 1
    rw [f.integral_zero, sub_zero]
  have hscaled :
      |u * ccmFourierTruncatedPoissonValue f u| ≤
        u * ccmFourierTruncatedVariation f := by
    exact le_of_tendsto herror_lim
      (Eventually.of_forall fun N => ccmFourierTruncated_finite_riemann_error f hu N)
  rw [abs_mul, abs_of_pos hu] at hscaled
  exact (mul_le_mul_iff_of_pos_left hu).mp hscaled

/-- The paper's half-density Riemann-sum boundary `𝓔(f)(u)`. -/
def ccmFourierTruncatedE (f : CCMFourierTruncatedInput) (u : ℝ) : ℝ :=
  Real.sqrt u * ccmFourierTruncatedPoissonValue f u

theorem ccmFourierTruncatedE_zero (f : CCMFourierTruncatedInput) :
    ccmFourierTruncatedE f 0 = 0 := by
  simp [ccmFourierTruncatedE]

/-- `fouriertruncated1(i)`, small end: `𝓔(f)(u) = O(u^(1/2))`, with the exact total-variation
constant. -/
theorem abs_ccmFourierTruncatedE_le_sqrt_mul_variation
    (f : CCMFourierTruncatedInput) {u : ℝ} (hu : 0 < u) :
    |ccmFourierTruncatedE f u| ≤
      Real.sqrt u * ccmFourierTruncatedVariation f := by
  rw [ccmFourierTruncatedE, abs_mul, abs_of_nonneg (Real.sqrt_nonneg u)]
  exact mul_le_mul_of_nonneg_left
    (abs_ccmFourierTruncatedPoissonValue_le_variation f hu)
    (Real.sqrt_nonneg u)

/-- Shifted `p`-series constant used to sum the paper's rapid-decay estimate. -/
def ccmFourierTruncatedPSeries (N : ℕ) : ℝ :=
  ∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ N)

theorem ccmFourierTruncatedPSeries_summable {N : ℕ} (hN : 2 ≤ N) :
    Summable fun n : ℕ => 1 / (((n : ℝ) + 1) ^ N) := by
  have hp0 : Summable fun n : ℕ => 1 / ((n : ℝ) ^ N) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  simpa [Function.comp_def] using hp0.comp_injective Nat.succ_injective

theorem ccmFourierTruncatedPSeries_nonneg (N : ℕ) :
    0 ≤ ccmFourierTruncatedPSeries N := by
  exact tsum_nonneg fun n => by positivity

/-- `fouriertruncated1(i)`, large-end estimate for the unweighted Riemann sum. -/
theorem ccmFourierTruncatedPoisson_rapidDecay
    (f : CCMFourierTruncatedInput) (N : ℕ) (hN : 2 ≤ N) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ⦃u : ℝ⦄, 1 ≤ u →
      |ccmFourierTruncatedPoissonValue f u| ≤ D / u ^ N := by
  obtain ⟨C, hC, hdecay⟩ := f.rapidDecay N
  let P : ℝ := ccmFourierTruncatedPSeries N
  refine ⟨C * P, mul_nonneg hC (ccmFourierTruncatedPSeries_nonneg N), ?_⟩
  intro u hu
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hsum : Summable fun n : ℕ => f (u * ((n : ℝ) + 1)) :=
    ccmFourierTruncatedPoisson_summable f hu0
  have hp : Summable fun n : ℕ => 1 / (((n : ℝ) + 1) ^ N) :=
    ccmFourierTruncatedPSeries_summable hN
  have hmajorant : Summable fun n : ℕ =>
      (C / u ^ N) * (1 / (((n : ℝ) + 1) ^ N)) :=
    hp.mul_left (C / u ^ N)
  have hterm (n : ℕ) :
      ‖f (u * ((n : ℝ) + 1))‖ ≤
        (C / u ^ N) * (1 / (((n : ℝ) + 1) ^ N)) := by
    have hun : 1 ≤ u * ((n : ℝ) + 1) := by
      have hn : 1 ≤ (n : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith
    rw [Real.norm_eq_abs]
    refine (hdecay hun).trans_eq ?_
    rw [mul_pow]
    field_simp
  calc
    |ccmFourierTruncatedPoissonValue f u|
        = ‖∑' n : ℕ, f (u * ((n : ℝ) + 1))‖ := by
          rw [ccmFourierTruncatedPoissonValue, Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ, ‖f (u * ((n : ℝ) + 1))‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, (C / u ^ N) * (1 / (((n : ℝ) + 1) ^ N)) :=
      hsum.norm.tsum_le_tsum hterm hmajorant
    _ = (C / u ^ N) * P := by
      rw [tsum_mul_left]
      rfl
    _ = (C * P) / u ^ N := by
      dsimp [P]
      field_simp

/-- `fouriertruncated1(i)`, large end: the half-density boundary has rapid decay. -/
theorem ccmFourierTruncatedE_rapidDecay
    (f : CCMFourierTruncatedInput) (M : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ⦃u : ℝ⦄, 1 ≤ u →
      |ccmFourierTruncatedE f u| ≤ D / u ^ M := by
  obtain ⟨D, hD, hpoisson⟩ :=
    ccmFourierTruncatedPoisson_rapidDecay f (M + 2) (by omega)
  refine ⟨D, hD, ?_⟩
  intro u hu
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hsqrt : Real.sqrt u ≤ u ^ 2 := by
    have hsu : Real.sqrt u ≤ u := Real.sqrt_le_self_iff.mpr (Or.inr hu)
    have huu : u ≤ u ^ 2 := by nlinarith
    exact hsu.trans huu
  rw [ccmFourierTruncatedE, abs_mul, abs_of_nonneg (Real.sqrt_nonneg u)]
  calc
    Real.sqrt u * |ccmFourierTruncatedPoissonValue f u|
        ≤ Real.sqrt u * (D / u ^ (M + 2)) :=
      mul_le_mul_of_nonneg_left (hpoisson hu) (Real.sqrt_nonneg u)
    _ ≤ u ^ 2 * (D / u ^ (M + 2)) :=
      mul_le_mul_of_nonneg_right hsqrt (div_nonneg hD (pow_nonneg hu0.le _))
    _ = D / u ^ M := by
      rw [pow_add]
      field_simp

theorem CCMFourierTruncatedInput.measurable (f : CCMFourierTruncatedInput) :
    Measurable f := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    f.boundedVariation.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hp' : Monotone p := by simpa only [monotoneOn_univ] using hp
  have hq' : Monotone q := by simpa only [monotoneOn_univ] using hq
  rw [hpq]
  exact hp'.measurable.sub hq'.measurable

theorem measurable_ccmFourierTruncatedPoissonValue
    (f : CCMFourierTruncatedInput) :
    Measurable (ccmFourierTruncatedPoissonValue f) := by
  apply Measurable.tsum
  intro n
  exact f.measurable.comp
    (measurable_id.mul measurable_const)

theorem measurable_ccmFourierTruncatedE (f : CCMFourierTruncatedInput) :
    Measurable (ccmFourierTruncatedE f) :=
  measurable_id.sqrt.mul (measurable_ccmFourierTruncatedPoissonValue f)

/-- Additive logarithmic form of the half-density boundary. -/
def ccmFourierTruncatedLogBoundary (f : CCMFourierTruncatedInput) (t : ℝ) : ℝ :=
  ccmFourierTruncatedE f (Real.exp t)

theorem measurable_ccmFourierTruncatedLogBoundary (f : CCMFourierTruncatedInput) :
    Measurable (ccmFourierTruncatedLogBoundary f) :=
  (measurable_ccmFourierTruncatedE f).comp Real.measurable_exp

/-- The rough CCM half-density boundary is genuinely `L¹` on logarithmic scale.  This is the
measure-theoretic fact needed to compute its periodization coefficients without an illicit
exchange of the critical-line Dirichlet series with an integral. -/
theorem integrable_ccmFourierTruncatedLogBoundary
    (f : CCMFourierTruncatedInput) :
    Integrable (ccmFourierTruncatedLogBoundary f) := by
  have hmeas : AEStronglyMeasurable (ccmFourierTruncatedLogBoundary f) volume :=
    (measurable_ccmFourierTruncatedLogBoundary f).aestronglyMeasurable
  have hneg : IntegrableOn (ccmFourierTruncatedLogBoundary f) (Iic 0) := by
    have hmajor : IntegrableOn
        (fun t : ℝ => ccmFourierTruncatedVariation f * Real.exp ((1 / 2 : ℝ) * t))
        (Iic 0) :=
      (integrableOn_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) 0).const_mul
        (ccmFourierTruncatedVariation f)
    refine Integrable.mono' hmajor hmeas.restrict ?_
    filter_upwards with t
    rw [Real.norm_eq_abs]
    have hbound := abs_ccmFourierTruncatedE_le_sqrt_mul_variation f (Real.exp_pos t)
    rw [ccmFourierTruncatedLogBoundary]
    calc
      |ccmFourierTruncatedE f (Real.exp t)|
          ≤ Real.sqrt (Real.exp t) * ccmFourierTruncatedVariation f := hbound
      _ = ccmFourierTruncatedVariation f * Real.exp ((1 / 2 : ℝ) * t) := by
        rw [← Real.exp_half]
        ring
  have hpos : IntegrableOn (ccmFourierTruncatedLogBoundary f) (Ioi 0) := by
    obtain ⟨D, hD, hrapid⟩ := ccmFourierTruncatedE_rapidDecay f 1
    have hmajor : IntegrableOn
        (fun t : ℝ => D * Real.exp ((-1 : ℝ) * t)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0).const_mul D
    refine Integrable.mono' hmajor hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, ccmFourierTruncatedLogBoundary]
    have hexp : 1 ≤ Real.exp t := Real.one_le_exp ht.le
    calc
      |ccmFourierTruncatedE f (Real.exp t)| ≤ D / Real.exp t := by
        simpa using hrapid hexp
      _ = D * Real.exp ((-1 : ℝ) * t) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        congr 1
        ring
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hneg.union hpos

theorem integrable_ccmFourierTruncatedLogBoundaryComplex
    (f : CCMFourierTruncatedInput) :
    Integrable (fun t => (ccmFourierTruncatedLogBoundary f t : ℂ)) :=
  (integrable_ccmFourierTruncatedLogBoundary f).ofReal

/-- Additive form of the paper's multiplicative periodization `Σ_μ 𝓔(f)`, with `μ = exp L`. -/
def ccmFourierTruncatedPeriodization
    (f : CCMFourierTruncatedInput) (L t : ℝ) : ℝ :=
  ∑' k : ℤ, ccmFourierTruncatedLogBoundary f (t + (k : ℝ) * L)

/-- Complexification identifies the paper's rough periodization with the generic `L¹`
circumference periodization. -/
theorem ofReal_ccmFourierTruncatedPeriodization
    (f : CCMFourierTruncatedInput) (L t : ℝ) :
    (ccmFourierTruncatedPeriodization f L t : ℂ) =
      l1PeriodizationAtScale
        (fun s => (ccmFourierTruncatedLogBoundary f s : ℂ)) L t := by
  rw [ccmFourierTruncatedPeriodization, l1PeriodizationAtScale]
  exact Complex.ofReal_tsum _

/-- Every coefficient of the literal BV periodization is the Fourier transform of its logarithmic
boundary.  This is unconditional and uses only `L¹`, not hidden continuity or termwise Mellin
manipulation on the critical line. -/
theorem fourierCoeffOn_ccmFourierTruncatedPeriodization
    (f : CCMFourierTruncatedInput) {L : ℝ} (hL : 0 < L) (m : ℤ) :
    fourierCoeffOn hL (fun t => (ccmFourierTruncatedPeriodization f L t : ℂ)) m =
      (1 / L) •
        𝓕 (fun t => (ccmFourierTruncatedLogBoundary f t : ℂ))
          ((1 / L) * (m : ℝ)) := by
  rw [show (fun t => (ccmFourierTruncatedPeriodization f L t : ℂ)) =
      l1PeriodizationAtScale
        (fun t => (ccmFourierTruncatedLogBoundary f t : ℂ)) L by
    funext t
    exact ofReal_ccmFourierTruncatedPeriodization f L t]
  exact fourierCoeffOn_l1PeriodizationAtScale
    (integrable_ccmFourierTruncatedLogBoundaryComplex f) hL m

theorem measurable_ccmFourierTruncatedPeriodization
    (f : CCMFourierTruncatedInput) (L : ℝ) :
    Measurable (ccmFourierTruncatedPeriodization f L) := by
  apply Measurable.tsum
  intro k
  exact (measurable_ccmFourierTruncatedLogBoundary f).comp
    (measurable_id.add (measurable_const.mul measurable_const))

/-- Geometric majorant for the positive logarithmic lattice tail. -/
theorem ccmFourierTruncatedLogBoundary_pos_tail
    (f : CCMFourierTruncatedInput) {L : ℝ} (hL : 0 < L) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ n : ℕ,
      |ccmFourierTruncatedLogBoundary f (t + (n : ℝ) * L)| ≤
        D * (Real.exp (-L)) ^ n := by
  obtain ⟨D, hD, hrapid⟩ := ccmFourierTruncatedE_rapidDecay f 1
  refine ⟨D, hD, fun {t} ht n => ?_⟩
  have hx : 1 ≤ Real.exp (t + (n : ℝ) * L) := by
    rw [Real.one_le_exp_iff]
    positivity
  rw [ccmFourierTruncatedLogBoundary]
  refine (hrapid hx).trans ?_
  rw [pow_one, div_eq_mul_inv, ← Real.exp_neg]
  refine mul_le_mul_of_nonneg_left ?_ hD
  rw [← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- Geometric majorant for the negative logarithmic lattice tail on a fundamental interval. -/
theorem ccmFourierTruncatedLogBoundary_neg_tail
    (f : CCMFourierTruncatedInput) {L t : ℝ} (_hL : 0 < L) (_ht0 : 0 ≤ t)
    (htL : t ≤ L) :
    ∀ n : ℕ,
      |ccmFourierTruncatedLogBoundary f
          (t + ((-((n : ℤ) + 1) : ℤ) : ℝ) * L)| ≤
        ccmFourierTruncatedVariation f * (Real.exp (-L / 2)) ^ n := by
  intro n
  let x : ℝ := t + ((-((n : ℤ) + 1) : ℤ) : ℝ) * L
  have hxexp : 0 < Real.exp x := Real.exp_pos x
  have hsmall := abs_ccmFourierTruncatedE_le_sqrt_mul_variation f hxexp
  rw [ccmFourierTruncatedLogBoundary]
  refine hsmall.trans ?_
  rw [← Real.exp_half]
  have hexp : Real.exp (x / 2) ≤ Real.exp (-(n : ℝ) * L / 2) := by
    apply Real.exp_le_exp.mpr
    dsimp [x]
    push_cast
    nlinarith
  calc
    Real.exp (x / 2) * ccmFourierTruncatedVariation f
        ≤ Real.exp (-(n : ℝ) * L / 2) * ccmFourierTruncatedVariation f :=
      mul_le_mul_of_nonneg_right hexp (ccmFourierTruncatedVariation_nonneg f)
    _ = ccmFourierTruncatedVariation f * Real.exp (-(n : ℝ) * L / 2) :=
      mul_comm _ _
    _ = ccmFourierTruncatedVariation f * (Real.exp (-L / 2)) ^ n := by
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- `fouriertruncated1(ii)`: both halves of `Σ_μ 𝓔(f)` converge by explicit geometric
majorants, uniformly on the logarithmic fundamental interval `[0,L]`. -/
theorem ccmFourierTruncatedPeriodization_geometric
    (f : CCMFourierTruncatedInput) {L : ℝ} (hL : 0 < L) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ L →
        (Summable fun k : ℤ =>
          ccmFourierTruncatedLogBoundary f (t + (k : ℝ) * L)) ∧
        |ccmFourierTruncatedPeriodization f L t| ≤ D := by
  obtain ⟨A, hA, hpos⟩ := ccmFourierTruncatedLogBoundary_pos_tail f hL
  let r : ℝ := Real.exp (-L)
  let s : ℝ := Real.exp (-L / 2)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hs0 : 0 ≤ s := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    change Real.exp (-L) < 1
    rw [Real.exp_lt_one_iff]
    linarith
  have hs1 : s < 1 := by
    change Real.exp (-L / 2) < 1
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeo_r : Summable fun n : ℕ => A * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left A
  have hgeo_s : Summable fun n : ℕ => ccmFourierTruncatedVariation f * s ^ n :=
    (summable_geometric_of_lt_one hs0 hs1).mul_left
      (ccmFourierTruncatedVariation f)
  let D : ℝ := (∑' n : ℕ, A * r ^ n) +
    ∑' n : ℕ, ccmFourierTruncatedVariation f * s ^ n
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg (tsum_nonneg fun _ => mul_nonneg hA (pow_nonneg hr0 _))
      (tsum_nonneg fun _ => mul_nonneg (ccmFourierTruncatedVariation_nonneg f)
        (pow_nonneg hs0 _))
  refine ⟨D, hD, fun {t} ht0 htL => ?_⟩
  let g : ℤ → ℝ := fun k =>
    ccmFourierTruncatedLogBoundary f (t + (k : ℝ) * L)
  have hpos_bound (n : ℕ) : ‖g (n : ℤ)‖ ≤ A * r ^ n := by
    rw [Real.norm_eq_abs]
    simpa [g, r] using hpos ht0 n
  have hneg_bound (n : ℕ) : ‖g (-((n : ℤ) + 1))‖ ≤
      ccmFourierTruncatedVariation f * s ^ n := by
    rw [Real.norm_eq_abs]
    simpa [g, s] using
      ccmFourierTruncatedLogBoundary_neg_tail f hL ht0 htL n
  have hpos_sum : Summable fun n : ℕ => g (n : ℤ) :=
    hgeo_r.of_norm_bounded hpos_bound
  have hneg_sum : Summable fun n : ℕ => g (-((n : ℤ) + 1)) :=
    hgeo_s.of_norm_bounded hneg_bound
  have hg : Summable g := Summable.of_nat_of_neg_add_one hpos_sum hneg_sum
  refine ⟨hg, ?_⟩
  rw [ccmFourierTruncatedPeriodization, ← Real.norm_eq_abs]
  change ‖∑' k : ℤ, g k‖ ≤ D
  calc
    ‖∑' k : ℤ, g k‖ ≤ ∑' k : ℤ, ‖g k‖ :=
      norm_tsum_le_tsum_norm hg.norm
    _ = (∑' n : ℕ, ‖g (n : ℤ)‖) + ∑' n : ℕ, ‖g (-((n : ℤ) + 1))‖ :=
      tsum_of_nat_of_neg_add_one hpos_sum.norm hneg_sum.norm
    _ ≤ (∑' n : ℕ, A * r ^ n) +
        ∑' n : ℕ, ccmFourierTruncatedVariation f * s ^ n := by
      exact add_le_add
        (hpos_sum.norm.tsum_le_tsum hpos_bound hgeo_r)
        (hneg_sum.norm.tsum_le_tsum hneg_bound hgeo_s)
    _ = D := rfl

theorem ccmFourierTruncatedPeriodization_periodic
    (f : CCMFourierTruncatedInput) (L t : ℝ) :
    ccmFourierTruncatedPeriodization f L (t + L) =
      ccmFourierTruncatedPeriodization f L t := by
  rw [ccmFourierTruncatedPeriodization, ccmFourierTruncatedPeriodization,
    ← (Equiv.subRight (1 : ℤ)).tsum_eq]
  apply tsum_congr
  intro k
  congr 1
  simp only [Equiv.subRight_apply]
  push_cast
  ring

/-- The bounded measurable quotient function asserted by `fouriertruncated1(ii)`. -/
def ccmFourierTruncatedQuotient
    (f : CCMFourierTruncatedInput) (L : ℝ) (hL : 0 < L) : AddCircle L → ℝ := by
  letI : Fact (0 < L) := ⟨hL⟩
  exact AddCircle.liftIoc L 0 (ccmFourierTruncatedPeriodization f L)

theorem measurable_ccmFourierTruncatedQuotient
    (f : CCMFourierTruncatedInput) {L : ℝ} (hL : 0 < L) :
    Measurable (ccmFourierTruncatedQuotient f L hL) := by
  letI : Fact (0 < L) := ⟨hL⟩
  rw [ccmFourierTruncatedQuotient]
  change Measurable
    (Set.restrict (Ioc (0 : ℝ) (0 + L)) (ccmFourierTruncatedPeriodization f L) ∘
      AddCircle.equivIoc L 0)
  exact ((measurable_ccmFourierTruncatedPeriodization f L).comp measurable_subtype_coe).comp
    (AddCircle.measurableEquivIoc L 0).measurable

/-- Full unconditional Lean form of Connes--Consani Lemma `fouriertruncated1`: the raw source
has the stated small/large estimates, while its multiplicative periodization converges
geometrically and descends to a bounded measurable function on `ℝ₊*/exp(L)^ℤ`. -/
theorem connesConsani_fouriertruncated1
    (f : CCMFourierTruncatedInput) {L : ℝ} (hL : 0 < L) :
    (∀ ⦃u : ℝ⦄, 0 < u →
      |ccmFourierTruncatedE f u| ≤
        Real.sqrt u * ccmFourierTruncatedVariation f) ∧
    (∀ M : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ ⦃u : ℝ⦄, 1 ≤ u →
      |ccmFourierTruncatedE f u| ≤ D / u ^ M) ∧
    ∃ D : ℝ, 0 ≤ D ∧
      Measurable (ccmFourierTruncatedQuotient f L hL) ∧
      (∀ x : AddCircle L, |ccmFourierTruncatedQuotient f L hL x| ≤ D) := by
  letI : Fact (0 < L) := ⟨hL⟩
  refine ⟨fun {_} hu => abs_ccmFourierTruncatedE_le_sqrt_mul_variation f hu,
    ccmFourierTruncatedE_rapidDecay f, ?_⟩
  obtain ⟨D, hD, hgeom⟩ := ccmFourierTruncatedPeriodization_geometric f hL
  refine ⟨D, hD, measurable_ccmFourierTruncatedQuotient f hL, fun x => ?_⟩
  let t : Ioc (0 : ℝ) (0 + L) := AddCircle.equivIoc L 0 x
  have ht0 : 0 ≤ (t : ℝ) := t.property.1.le
  have htL : (t : ℝ) ≤ L := by simpa using t.property.2
  have hbound := (hgeom ht0 htL).2
  rw [ccmFourierTruncatedQuotient]
  change |ccmFourierTruncatedPeriodization f L
    ((AddCircle.equivIoc L 0 x : Ioc (0 : ℝ) (0 + L)) : ℝ)| ≤ D
  exact hbound

end

end RHTower
