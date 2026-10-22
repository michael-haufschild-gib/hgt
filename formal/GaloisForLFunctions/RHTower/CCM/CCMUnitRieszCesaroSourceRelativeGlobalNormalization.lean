import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszCesaroSourceRelativeReporter

/-!
# Source-relative CCM-FU global normalization

Literal positive source wall must not be replaced by zero before completion. This module proves
that full finite reporter converges to canonical limiting completed symbol and that two exact
lower-wall corrections—the escaped value/first jet and fixed-head response—both vanish cofinally.
Consequently source-relative finite reporter converges coefficient-faithfully for every real
critical-Mellin exponent in a > -1/2.

Result is unconditional and source-side. It solves real-mode global normalization, not remaining
complex-mode/arithmetic interchange needed for RH.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

private theorem integral_pow_three_mul_exp
    {c t : ℝ} (hc : c ≠ 0) :
    (∫ s in (0 : ℝ)..t, s ^ (3 : ℕ) * Real.exp (c * s)) =
      Real.exp (c * t) *
          (t ^ (3 : ℕ) / c - 3 * t ^ (2 : ℕ) / c ^ (2 : ℕ) + 6 * t / c ^ (3 : ℕ) - 6 / c ^ (4 : ℕ)) +
        6 / c ^ (4 : ℕ) := by
  let F : ℝ → ℝ := fun s =>
    Real.exp (c * s) *
      (s ^ (3 : ℕ) / c - 3 * s ^ (2 : ℕ) / c ^ (2 : ℕ) + 6 * s / c ^ (3 : ℕ) - 6 / c ^ (4 : ℕ))
  have hF (s : ℝ) : HasDerivAt F (s ^ (3 : ℕ) * Real.exp (c * s)) s := by
    have he : HasDerivAt (fun x : ℝ => Real.exp (c * x))
        (c * Real.exp (c * s)) s := by
      simpa only [Function.comp_def, mul_one, mul_comm] using
        (Real.hasDerivAt_exp (c * s)).comp s ((hasDerivAt_id s).const_mul c)
    have hp : HasDerivAt
        (fun x : ℝ => x ^ (3 : ℕ) / c - 3 * x ^ (2 : ℕ) / c ^ (2 : ℕ) + 6 * x / c ^ (3 : ℕ) - 6 / c ^ (4 : ℕ))
        (3 * s ^ (2 : ℕ) / c - 6 * s / c ^ (2 : ℕ) + 6 / c ^ (3 : ℕ)) s := by
      have hraw0 := ((((hasDerivAt_pow 3 s).const_mul (1 / c)).sub
          ((hasDerivAt_pow 2 s).const_mul (3 / c ^ (2 : ℕ)))).add
          ((hasDerivAt_id s).const_mul (6 / c ^ (3 : ℕ)))).sub
          (hasDerivAt_const s (6 / c ^ (4 : ℕ)))
      have hraw := hraw0.congr_deriv (show
          1 / c * (3 * s ^ (3 - 1)) -
                3 / c ^ (2 : ℕ) * (2 * s ^ (2 - 1)) + 6 / c ^ (3 : ℕ) * 1 - 0 =
            3 * s ^ (2 : ℕ) / c - 6 * s / c ^ (2 : ℕ) + 6 / c ^ (3 : ℕ) by norm_num; ring)
      apply hraw.congr_of_eventuallyEq
      filter_upwards with x
      simp only [Pi.add_apply, Pi.sub_apply, id_eq]
      ring
    change HasDerivAt
      (fun x : ℝ => Real.exp (c * x) *
        (x ^ (3 : ℕ) / c - 3 * x ^ (2 : ℕ) / c ^ (2 : ℕ) + 6 * x / c ^ (3 : ℕ) - 6 / c ^ (4 : ℕ)))
      (s ^ (3 : ℕ) * Real.exp (c * s)) s
    convert he.mul hp using 1
    all_goals try rfl
    field_simp [hc]
    ring
  have hint : IntervalIntegrable (fun s : ℝ => s ^ (3 : ℕ) * Real.exp (c * s)) volume 0 t :=
    ((continuous_id.pow 3).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hF s) hint
  dsimp only [F] at hftc
  norm_num [Real.exp_zero] at hftc
  linarith

private theorem tendsto_cubicExponentialTerminal
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ =>
      Real.exp (-(c * t)) / t ^ (3 : ℕ) *
        ∫ s in (0 : ℝ)..t, s ^ (3 : ℕ) * Real.exp (c * s))
      atTop (nhds (1 / c)) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hscale : Tendsto (fun t : ℝ => c * t) atTop atTop :=
    Filter.tendsto_atTop_atTop_of_monotone
      (fun x y hxy => by nlinarith)
      (fun y => ⟨y / c, by field_simp; nlinarith⟩)
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(c * t))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have h1 : Tendsto (fun t : ℝ => 3 / (c ^ (2 : ℕ) * t)) atTop (nhds 0) := by
    convert hinv.const_mul (3 / c ^ (2 : ℕ)) using 1
    all_goals ring_nf
  have h2 : Tendsto (fun t : ℝ => 6 / (c ^ (3 : ℕ) * t ^ (2 : ℕ))) atTop (nhds 0) := by
    convert (hinv.pow 2).const_mul (6 / c ^ (3 : ℕ)) using 1
    all_goals ring_nf
  have h3 : Tendsto (fun t : ℝ => 6 / (c ^ (4 : ℕ) * t ^ (3 : ℕ))) atTop (nhds 0) := by
    convert (hinv.pow 3).const_mul (6 / c ^ (4 : ℕ)) using 1
    all_goals ring_nf
  have h4 : Tendsto (fun t : ℝ =>
      6 * Real.exp (-(c * t)) / (c ^ (4 : ℕ) * t ^ (3 : ℕ))) atTop (nhds 0) := by
    convert (hexp.mul (hinv.pow 3)).const_mul (6 / c ^ (4 : ℕ)) using 1
    · funext t
      ring
    · ring
  have hsum : Tendsto (fun t : ℝ =>
      1 / c - 3 / (c ^ (2 : ℕ) * t) + 6 / (c ^ (3 : ℕ) * t ^ (2 : ℕ)) -
        6 / (c ^ (4 : ℕ) * t ^ (3 : ℕ)) +
          6 * Real.exp (-(c * t)) / (c ^ (4 : ℕ) * t ^ (3 : ℕ)))
      atTop (nhds (1 / c)) := by
    convert (((tendsto_const_nhds.sub h1).add h2).sub h3).add h4 using 1
    all_goals ring_nf
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [integral_pow_three_mul_exp hc0]
  have ht0 : t ≠ 0 := ne_of_gt ht
  have he : Real.exp (-(c * t)) * Real.exp (c * t) = 1 := by
    rw [← Real.exp_add, show -(c * t) + c * t = (0 : ℝ) by ring, Real.exp_zero]
  field_simp [hc0, ht0]
  linear_combination
    -(c * t * (c * t * (c * t - 3) + 6) - 6) * he

private def cubicExponentialTerminal (c t : ℝ) : ℝ :=
  Real.exp (-(c * t)) / t ^ (3 : ℕ) *
    ∫ s in (0 : ℝ)..t, s ^ (3 : ℕ) * Real.exp (c * s)

private theorem tendsto_cubicExponentialTerminal'
    {c : ℝ} (hc : 0 < c) :
    Tendsto (cubicExponentialTerminal c) atTop (nhds (1 / c)) := by
  exact tendsto_cubicExponentialTerminal hc

private def cubicExponentialFixedHead (b c t : ℝ) : ℝ :=
  Real.exp (-(c * t)) / t ^ (3 : ℕ) *
    ∫ s in (0 : ℝ)..b, s ^ (3 : ℕ) * Real.exp (c * s)

private theorem tendsto_cubicExponentialFixedHead_zero
    (b : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (cubicExponentialFixedHead b c) atTop (nhds 0) := by
  have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hscale : Tendsto (fun t : ℝ => c * t) atTop atTop :=
    Filter.tendsto_atTop_atTop_of_monotone
      (fun x y hxy => by nlinarith)
      (fun y => ⟨y / c, by field_simp; nlinarith⟩)
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(c * t))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  let I : ℝ := ∫ s in (0 : ℝ)..b, s ^ (3 : ℕ) * Real.exp (c * s)
  have hraw := (hexp.mul (hinv.pow 3)).const_mul I
  change Tendsto (fun t : ℝ => Real.exp (-(c * t)) / t ^ (3 : ℕ) * I) atTop (nhds 0)
  convert hraw using 1
  · funext t
    ring
  · simp

private theorem weighted_unitRieszCesaroTest_eq_twoChannels
    (t a s : ℝ) :
    Real.exp (-(a * (t - s))) * unitRieszCesaroTest t s =
      (3 / 32 : ℝ) *
        (Real.exp (-((a + 1) * t)) *
            (s ^ (3 : ℕ) * Real.exp ((a + 1 / 2) * s)) -
          Real.exp (-((a + 3 / 2) * t)) *
            (s ^ (3 : ℕ) * Real.exp ((a + 1) * s))) := by
  rw [unitRieszCesaroTest]
  have hslow :
      Real.exp (-(a * (t - s))) * Real.exp (-t + s / 2) =
        Real.exp (-((a + 1) * t)) * Real.exp ((a + 1 / 2) * s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hfast :
      Real.exp (-(a * (t - s))) * Real.exp (-3 * t / 2 + s) =
        Real.exp (-((a + 3 / 2) * t)) * Real.exp ((a + 1) * s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (-(a * (t - s))) *
        ((3 / 32 : ℝ) * (s ^ (3 : ℕ) *
          (Real.exp (-t + s / 2) - Real.exp (-3 * t / 2 + s)))) =
      (3 / 32 : ℝ) * s ^ (3 : ℕ) *
        (Real.exp (-(a * (t - s))) * Real.exp (-t + s / 2) -
          Real.exp (-(a * (t - s))) * Real.exp (-3 * t / 2 + s)) by ring,
    hslow, hfast]
  ring

private theorem integral_weighted_unitRieszCesaroTest_eq_twoChannels
    (r t a : ℝ) :
    (∫ s in (0 : ℝ)..r,
        Real.exp (-(a * (t - s))) * unitRieszCesaroTest t s) =
      (3 / 32 : ℝ) *
        (Real.exp (-((a + 1) * t)) *
            (∫ s in (0 : ℝ)..r, s ^ (3 : ℕ) * Real.exp ((a + 1 / 2) * s)) -
          Real.exp (-((a + 3 / 2) * t)) *
            (∫ s in (0 : ℝ)..r, s ^ (3 : ℕ) * Real.exp ((a + 1) * s))) := by
  have hslowInt : IntervalIntegrable
      (fun s : ℝ => s ^ (3 : ℕ) * Real.exp ((a + 1 / 2) * s)) volume 0 r :=
    ((continuous_id.pow 3).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hfastInt : IntervalIntegrable
      (fun s : ℝ => s ^ (3 : ℕ) * Real.exp ((a + 1) * s)) volume 0 r :=
    ((continuous_id.pow 3).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  calc
    _ = ∫ s in (0 : ℝ)..r, (3 / 32 : ℝ) *
        (Real.exp (-((a + 1) * t)) *
            (s ^ (3 : ℕ) * Real.exp ((a + 1 / 2) * s)) -
          Real.exp (-((a + 3 / 2) * t)) *
            (s ^ (3 : ℕ) * Real.exp ((a + 1) * s))) := by
      apply intervalIntegral.integral_congr
      intro s _
      exact weighted_unitRieszCesaroTest_eq_twoChannels t a s
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          (hslowInt.const_mul _) (hfastInt.const_mul _),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

/-- Fixed lower-source head retained by literal positive-wall normalization. -/
def unitRieszCesaroSourceRelativeHeadCorrection (b t a : ℝ) : ℝ :=
  Real.exp (t / 2) / t ^ (3 : ℕ) * a ^ (2 : ℕ) *
    ∫ s in (0 : ℝ)..b,
      Real.exp (-(a * (t - s))) * unitRieszCesaroTest t s

private theorem unitRieszCesaroSourceRelativeHeadCorrection_eq_fixedHeads
    (b t a : ℝ) :
    unitRieszCesaroSourceRelativeHeadCorrection b t a =
      (3 / 32 : ℝ) * a ^ (2 : ℕ) *
        (cubicExponentialFixedHead b (a + 1 / 2) t -
          cubicExponentialFixedHead b (a + 1) t) := by
  rw [unitRieszCesaroSourceRelativeHeadCorrection,
    integral_weighted_unitRieszCesaroTest_eq_twoChannels]
  have hslowShift :
      Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-((a + 1) * t)) =
        Real.exp (-((a + 1 / 2) * t)) / t ^ (3 : ℕ) := by
    rw [show Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-((a + 1) * t)) =
        (Real.exp (t / 2) * Real.exp (-((a + 1) * t))) / t ^ (3 : ℕ) by ring,
      ← Real.exp_add]
    congr 2
    ring
  have hfastShift :
      Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-((a + 3 / 2) * t)) =
        Real.exp (-((a + 1) * t)) / t ^ (3 : ℕ) := by
    rw [show Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-((a + 3 / 2) * t)) =
        (Real.exp (t / 2) * Real.exp (-((a + 3 / 2) * t))) / t ^ (3 : ℕ) by ring,
      ← Real.exp_add]
    congr 2
    ring
  simp only [cubicExponentialFixedHead]
  rw [show Real.exp (t / 2) / t ^ (3 : ℕ) * a ^ (2 : ℕ) *
        ((3 / 32 : ℝ) *
          (Real.exp (-((a + 1) * t)) *
              (∫ s in (0 : ℝ)..b, s ^ (3 : ℕ) * Real.exp ((a + 1 / 2) * s)) -
            Real.exp (-((a + 3 / 2) * t)) *
              (∫ s in (0 : ℝ)..b, s ^ (3 : ℕ) * Real.exp ((a + 1) * s)))) =
      (3 / 32 : ℝ) * a ^ (2 : ℕ) *
        ((Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-((a + 1) * t))) *
            (∫ s in (0 : ℝ)..b, s ^ (3 : ℕ) * Real.exp ((a + 1 / 2) * s)) -
          (Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-((a + 3 / 2) * t))) *
            (∫ s in (0 : ℝ)..b, s ^ (3 : ℕ) * Real.exp ((a + 1) * s))) by ring,
    hslowShift, hfastShift]

/-- Fixed lower-source head correction vanishes throughout the real critical-Mellin half-plane. -/
theorem tendsto_unitRieszCesaroSourceRelativeHeadCorrection_zero
    (b : ℝ) {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    Tendsto (fun t : ℝ => unitRieszCesaroSourceRelativeHeadCorrection b t a)
      atTop (nhds 0) := by
  have hslow : Tendsto (cubicExponentialFixedHead b (a + 1 / 2)) atTop (nhds 0) :=
    tendsto_cubicExponentialFixedHead_zero b (by linarith)
  have hfast : Tendsto (cubicExponentialFixedHead b (a + 1)) atTop (nhds 0) :=
    tendsto_cubicExponentialFixedHead_zero b (by linarith)
  have hcombo := (hslow.sub hfast).const_mul ((3 / 32 : ℝ) * a ^ (2 : ℕ))
  have hcombo' : Tendsto (fun t : ℝ =>
      (3 / 32 : ℝ) * a ^ (2 : ℕ) *
        (cubicExponentialFixedHead b (a + 1 / 2) t -
          cubicExponentialFixedHead b (a + 1) t)) atTop (nhds 0) := by
    simpa using hcombo
  apply hcombo'.congr'
  filter_upwards with t
  exact (unitRieszCesaroSourceRelativeHeadCorrection_eq_fixedHeads b t a).symm

private theorem unitRieszCesaroFiniteCompletedReporterSymbol_eq_terminals
    {t : ℝ} (ht : 0 < t) (a : ℝ) :
    unitRieszCesaroFiniteCompletedReporterSymbol t a =
      -(3 / 32 : ℝ) * a ^ (2 : ℕ) *
        (cubicExponentialTerminal (a + 1 / 2) t -
          cubicExponentialTerminal (a + 1) t) := by
  rw [unitRieszCesaroFiniteCompletedReporterSymbol_eq ht]
  rw [integral_weighted_unitRieszCesaroTest_eq_twoChannels]
  have hslowShift :
      Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-((a + 1) * t)) =
        Real.exp (-((a + 1 / 2) * t)) / t ^ (3 : ℕ) := by
    rw [show Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-((a + 1) * t)) =
        (Real.exp (t / 2) * Real.exp (-((a + 1) * t))) / t ^ (3 : ℕ) by ring,
      ← Real.exp_add]
    congr 2
    ring
  have hfastShift :
      Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-((a + 3 / 2) * t)) =
        Real.exp (-((a + 1) * t)) / t ^ (3 : ℕ) := by
    rw [show Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-((a + 3 / 2) * t)) =
        (Real.exp (t / 2) * Real.exp (-((a + 3 / 2) * t))) / t ^ (3 : ℕ) by ring,
      ← Real.exp_add]
    congr 2
    ring
  simp only [cubicExponentialTerminal]
  rw [show -(Real.exp (t / 2) / t ^ (3 : ℕ)) * a ^ (2 : ℕ) *
        ((3 / 32 : ℝ) *
          (Real.exp (-((a + 1) * t)) *
              (∫ s in (0 : ℝ)..t, s ^ (3 : ℕ) * Real.exp ((a + 1 / 2) * s)) -
            Real.exp (-((a + 3 / 2) * t)) *
              (∫ s in (0 : ℝ)..t, s ^ (3 : ℕ) * Real.exp ((a + 1) * s)))) =
      -(3 / 32 : ℝ) * a ^ (2 : ℕ) *
        ((Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-((a + 1) * t))) *
            (∫ s in (0 : ℝ)..t, s ^ (3 : ℕ) * Real.exp ((a + 1 / 2) * s)) -
          (Real.exp (t / 2) / t ^ (3 : ℕ) * Real.exp (-((a + 3 / 2) * t))) *
            (∫ s in (0 : ℝ)..t, s ^ (3 : ℕ) * Real.exp ((a + 1) * s))) by ring,
    hslowShift, hfastShift]

/-- Full finite-aperture reporter converges to its canonical limiting completed symbol. -/
theorem tendsto_unitRieszCesaroFiniteCompletedReporterSymbol
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    Tendsto (fun t : ℝ => unitRieszCesaroFiniteCompletedReporterSymbol t a)
      atTop (nhds (unitRieszCesaroCompletedReporterSymbol a)) := by
  have hslowPos : 0 < a + 1 / 2 := by linarith
  have hfastPos : 0 < a + 1 := by linarith
  have hslow := tendsto_cubicExponentialTerminal' hslowPos
  have hfast := tendsto_cubicExponentialTerminal' hfastPos
  have hcombo : Tendsto (fun t : ℝ =>
      -(3 / 32 : ℝ) * a ^ (2 : ℕ) *
        (cubicExponentialTerminal (a + 1 / 2) t -
          cubicExponentialTerminal (a + 1) t)) atTop
      (nhds (-(3 / 32 : ℝ) * a ^ (2 : ℕ) *
        (1 / (a + 1 / 2) - 1 / (a + 1)))) := by
    exact (hslow.sub hfast).const_mul (-(3 / 32 : ℝ) * a ^ (2 : ℕ))
  have hlimit :
      -(3 / 32 : ℝ) * a ^ (2 : ℕ) * (1 / (a + 1 / 2) - 1 / (a + 1)) =
        unitRieszCesaroCompletedReporterSymbol a := by
    have hs0 : a + 1 / 2 ≠ 0 := ne_of_gt hslowPos
    have hf0 : a + 1 ≠ 0 := ne_of_gt hfastPos
    have htwo : 2 * a + 1 ≠ 0 := by linarith
    have htwo' : 1 + a * 2 ≠ 0 := by linarith
    have hdiff : 1 / (a + 1 / 2) - 1 / (a + 1) =
        1 / ((a + 1) * (2 * a + 1)) := by
      field_simp [hs0, hf0, htwo, htwo']
      have hunit : (1 + a * 2) * (1 + a * 2)⁻¹ = (1 : ℝ) :=
        mul_inv_cancel₀ htwo'
      linear_combination hunit
    rw [hdiff, unitRieszCesaroCompletedReporterSymbol_eq ha]
    ring
  rw [← hlimit]
  apply hcombo.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (unitRieszCesaroFiniteCompletedReporterSymbol_eq_terminals ht a).symm

/-- Literal positive-wall reporter equals full finite reporter plus exactly two lower-wall terms. -/
theorem unitRieszCesaroSourceRelativeCompletedReporterSymbol_eq_finite_add_lowerWall
    {t : ℝ} (ht : 0 < t) (b a : ℝ) :
    unitRieszCesaroSourceRelativeCompletedReporterSymbol b t a =
      unitRieszCesaroFiniteCompletedReporterSymbol t a +
        unitRieszCesaroSourceRelativeEscapedJet b t a +
          unitRieszCesaroSourceRelativeHeadCorrection b t a := by
  let f : ℝ → ℝ := fun s =>
    Real.exp (-(a * (t - s))) * unitRieszCesaroTest t s
  have hf : Continuous f :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (-(a * (t - s))))).mul
      (continuous_unitRieszCesaroTest t)
  have h0b : IntervalIntegrable f volume 0 b := hf.intervalIntegrable _ _
  have hbt : IntervalIntegrable f volume b t := hf.intervalIntegrable _ _
  rw [unitRieszCesaroSourceRelativeCompletedReporterSymbol_eq_escapedJet_sub ht,
    unitRieszCesaroFiniteCompletedReporterSymbol_eq ht,
    unitRieszCesaroSourceRelativeHeadCorrection]
  change unitRieszCesaroSourceRelativeEscapedJet b t a -
      Real.exp (t / 2) / t ^ (3 : ℕ) * a ^ (2 : ℕ) * (∫ s in b..t, f s) =
    -(Real.exp (t / 2) / t ^ (3 : ℕ)) * a ^ (2 : ℕ) * (∫ s in (0 : ℝ)..t, f s) +
      unitRieszCesaroSourceRelativeEscapedJet b t a +
        Real.exp (t / 2) / t ^ (3 : ℕ) * a ^ (2 : ℕ) * (∫ s in (0 : ℝ)..b, f s)
  rw [← intervalIntegral.integral_add_adjacent_intervals h0b hbt]
  ring

/-- Exact cofinal normalization: retaining the positive source wall changes no limiting symbol. -/
theorem tendsto_unitRieszCesaroSourceRelativeCompletedReporterSymbol
    (b : ℝ) {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    Tendsto (fun t : ℝ =>
      unitRieszCesaroSourceRelativeCompletedReporterSymbol b t a)
      atTop (nhds (unitRieszCesaroCompletedReporterSymbol a)) := by
  have hfinite := tendsto_unitRieszCesaroFiniteCompletedReporterSymbol ha
  have hjet := tendsto_unitRieszCesaroSourceRelativeEscapedJet_zero b ha
  have hhead := tendsto_unitRieszCesaroSourceRelativeHeadCorrection_zero b ha
  have hsum := (hfinite.add hjet).add hhead
  have hsum' : Tendsto (fun t : ℝ =>
      unitRieszCesaroFiniteCompletedReporterSymbol t a +
        unitRieszCesaroSourceRelativeEscapedJet b t a +
          unitRieszCesaroSourceRelativeHeadCorrection b t a) atTop
      (nhds (unitRieszCesaroCompletedReporterSymbol a)) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (unitRieszCesaroSourceRelativeCompletedReporterSymbol_eq_finite_add_lowerWall
    ht b a).symm

/-- Closed source-relative global-normalization statement for every real critical-Mellin mode. -/
def CCMUnitRieszCesaroSourceRelativeGlobalNormalization : Prop :=
  ∀ b a : ℝ, -(1 / 2 : ℝ) < a →
    Tendsto (fun t : ℝ =>
      unitRieszCesaroSourceRelativeCompletedReporterSymbol b t a)
      atTop (nhds (unitRieszCesaroCompletedReporterSymbol a))

/-- Source-relative CCM-FU normalization is unconditional and coefficient-faithful. -/
theorem ccmUnitRieszCesaroSourceRelativeGlobalNormalization :
    CCMUnitRieszCesaroSourceRelativeGlobalNormalization := by
  intro b a ha
  exact tendsto_unitRieszCesaroSourceRelativeCompletedReporterSymbol b ha


end GaloisForLFunctions.RHTower
