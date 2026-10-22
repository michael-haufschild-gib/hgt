import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinLiteralMaassWhittakerWord

/-!
# Complex constant powers against literal completed Eisenstein Whittaker tails

Analytic-family boundary products multiply nonconstant completed Eisenstein modes by constant-term
powers `Y^w` with arbitrary complex exponent.  Qualitative cusp convergence alone cannot absorb
this unbounded multiplier.  The corpus complex-cpow norm identity gives the exact repair.

Choose `M = ceil |Re w|`.  On `Y >= 1`, the quotient `Y^w / Y^M` has norm at most one, while
raising the integer height degree from `m` to `m + M` absorbs `Y^M` exactly inside the literal
Whittaker series.  Hence every complex-power-weighted constituent still vanishes.  Distributing
over the exact two-step Maass shift words proves the same result for both the weight `+4` and
weight `-4` nonconstant tails.

This closes all constant-by-nonconstant cusp sectors in the balanced-spin Stokes product.  It is a
necessary bridge, not a claim of standalone scientific novelty.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [MIXED CONSTANT/WHITTAKER TAIL]`
-/

open Complex Real Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A constant-term complex power multiplying one literal square-root-normalized Whittaker tail. -/
def d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail
    (u nu w : ℂ) (indexDegree heightDegree : ℕ) (Y : ℝ) : ℂ :=
  (Y : ℂ) ^ w *
    d4BMCompletedEisensteinSqrtPolynomialBesselJetTail
      u nu indexDegree heightDegree Y

/-- Increasing the height degree factors an exact natural power out of the Whittaker series. -/
theorem d4BM_sqrtWhittakerTail_heightDegree_add
    (u nu : ℂ) (indexDegree heightDegree extraDegree : ℕ) (Y : ℝ) :
    d4BMCompletedEisensteinSqrtPolynomialBesselJetTail
        u nu indexDegree (heightDegree + extraDegree) Y =
      (Y : ℂ) ^ extraDegree *
        d4BMCompletedEisensteinSqrtPolynomialBesselJetTail
          u nu indexDegree heightDegree Y := by
  rw [d4BMCompletedEisensteinSqrtPolynomialBesselJetTail,
    d4BMCompletedEisensteinSqrtPolynomialBesselJetTail, ← tsum_mul_left]
  apply tsum_congr
  intro N
  rw [pow_add]
  ring

/-- On the positive cusp, a complex-power-weighted tail is a bounded quotient times a tail with
higher natural height degree. -/
theorem d4BM_complexPowerSqrtWhittakerTail_eq_boundedQuotient
    (u nu w : ℂ) (indexDegree heightDegree extraDegree : ℕ)
    {Y : ℝ} (hY : 0 < Y) :
    d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail
        u nu w indexDegree heightDegree Y =
      (((Y : ℂ) ^ w) / ((Y : ℂ) ^ extraDegree)) *
        d4BMCompletedEisensteinSqrtPolynomialBesselJetTail
          u nu indexDegree (heightDegree + extraDegree) Y := by
  rw [d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail,
    d4BM_sqrtWhittakerTail_heightDegree_add]
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  field_simp

/-- Multiplication by an eventually norm-one-bounded complex factor preserves convergence to
zero. -/
theorem d4BM_tendsto_eventually_norm_le_one_mul_zero
    {f g : ℝ → ℂ} {l : Filter ℝ}
    (hf : ∀ᶠ Y in l, ‖f Y‖ ≤ 1) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun Y => f Y * g Y) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun Y => norm_nonneg (f Y * g Y))
    _ (by simpa using hg.norm)
  filter_upwards [hf] with Y hY
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_right hY (norm_nonneg (g Y))

/-- Every arbitrary-complex-power-weighted literal Whittaker constituent vanishes at the cusp. -/
theorem tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    (u nu w : ℂ) (indexDegree heightDegree : ℕ) :
    Tendsto
      (d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail
        u nu w indexDegree heightDegree) atTop (𝓝 0) := by
  let M : ℕ := Nat.ceil |w.re|
  have hbound : ∀ᶠ Y : ℝ in atTop,
      ‖((Y : ℂ) ^ w) / ((Y : ℂ) ^ M)‖ ≤ 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    have hY0 : 0 < Y := zero_lt_one.trans_le hY
    have hw : w.re ≤ (M : ℝ) := by
      dsimp [M]
      exact le_trans (le_abs_self w.re) (Nat.le_ceil |w.re|)
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hY0,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hY0.le,
      ← Real.rpow_natCast]
    rw [div_le_one (Real.rpow_pos_of_pos hY0 _)]
    exact Real.rpow_le_rpow_of_exponent_le hY hw
  have htail :=
    tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero
      u nu indexDegree (heightDegree + M)
  have hprod := d4BM_tendsto_eventually_norm_le_one_mul_zero hbound htail
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  exact (d4BM_complexPowerSqrtWhittakerTail_eq_boundedQuotient
    u nu w indexDegree heightDegree M hY).symm

/-- Arbitrary complex constant power multiplying the full positive-frequency raising word. -/
def d4BMComplexPowerRaiseTwoRaiseZeroWhittakerTail
    (u nu w : ℂ) (Y : ℝ) : ℂ :=
  (Y : ℂ) ^ w * d4BMPositiveFrequencyRaiseTwoRaiseZeroWhittakerTail u nu Y

/-- Arbitrary complex constant power multiplying the full positive-frequency lowering word. -/
def d4BMComplexPowerLowerNegTwoLowerZeroWhittakerTail
    (u nu w : ℂ) (Y : ℝ) : ℂ :=
  (Y : ℂ) ^ w * d4BMPositiveFrequencyLowerNegTwoLowerZeroWhittakerTail u nu Y

/-- Every complex-power-weighted full weight `+4` nonconstant tail vanishes at the cusp. -/
theorem tendsto_d4BMComplexPowerRaiseTwoRaiseZeroWhittakerTail_atTop_zero
    (u nu w : ℂ) :
    Tendsto (d4BMComplexPowerRaiseTwoRaiseZeroWhittakerTail u nu w) atTop (𝓝 0) := by
  have h00 := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u nu w 0 0
  have h10 := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u nu w 1 1
  have h1p := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u (nu + 1) w 1 1
  have h1m := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u (nu - 1) w 1 1
  have h20 := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u nu w 2 2
  have h2p := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u (nu + 1) w 2 2
  have h2m := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u (nu - 1) w 2 2
  have h2pp := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u (nu + 2) w 2 2
  have h2mm := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u (nu - 2) w 2 2
  have hword := (((((h00.const_mul (3 / 4 : ℂ)).sub
      (h10.const_mul (3 * (2 * Real.pi : ℂ)))).sub
      ((h1p.add h1m).const_mul ((3 / 2 : ℂ) * (2 * Real.pi : ℂ)))).add
      (h20.const_mul ((3 / 2 : ℂ) * (2 * Real.pi : ℂ) ^ 2))).add
      ((h2p.add h2m).const_mul ((2 * Real.pi : ℂ) ^ 2))).add
      ((h2pp.add h2mm).const_mul ((1 / 4 : ℂ) * (2 * Real.pi : ℂ) ^ 2))
  simp only [mul_zero, add_zero, sub_zero] at hword
  convert hword using 1
  funext Y
  simp only [d4BMComplexPowerRaiseTwoRaiseZeroWhittakerTail,
    d4BMPositiveFrequencyRaiseTwoRaiseZeroWhittakerTail,
    d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail]
  ring

/-- Every complex-power-weighted full weight `-4` nonconstant tail vanishes at the cusp. -/
theorem tendsto_d4BMComplexPowerLowerNegTwoLowerZeroWhittakerTail_atTop_zero
    (u nu w : ℂ) :
    Tendsto (d4BMComplexPowerLowerNegTwoLowerZeroWhittakerTail u nu w) atTop (𝓝 0) := by
  have h00 := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u nu w 0 0
  have h10 := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u nu w 1 1
  have h1p := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u (nu + 1) w 1 1
  have h1m := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u (nu - 1) w 1 1
  have h20 := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u nu w 2 2
  have h2p := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u (nu + 1) w 2 2
  have h2m := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u (nu - 1) w 2 2
  have h2pp := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u (nu + 2) w 2 2
  have h2mm := tendsto_d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail_atTop_zero
    u (nu - 2) w 2 2
  have hword := (((((h00.const_mul (3 / 4 : ℂ)).add
      (h10.const_mul (3 * (2 * Real.pi : ℂ)))).sub
      ((h1p.add h1m).const_mul ((3 / 2 : ℂ) * (2 * Real.pi : ℂ)))).add
      (h20.const_mul ((3 / 2 : ℂ) * (2 * Real.pi : ℂ) ^ 2))).sub
      ((h2p.add h2m).const_mul ((2 * Real.pi : ℂ) ^ 2))).add
      ((h2pp.add h2mm).const_mul ((1 / 4 : ℂ) * (2 * Real.pi : ℂ) ^ 2))
  simp only [mul_zero, add_zero, sub_zero] at hword
  convert hword using 1
  funext Y
  simp only [d4BMComplexPowerLowerNegTwoLowerZeroWhittakerTail,
    d4BMPositiveFrequencyLowerNegTwoLowerZeroWhittakerTail,
    d4BMCompletedEisensteinComplexPowerSqrtWhittakerTail]
  ring

end

end RHTower
