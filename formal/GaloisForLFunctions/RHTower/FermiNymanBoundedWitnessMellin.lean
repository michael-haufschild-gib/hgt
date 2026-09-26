import GaloisForLFunctions.RHTower.FermiNymanBeurlingWitnessSignature
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding

/-!
# Mellin analysis of bounded witnesses of the alternating Nyman–Beurling system

Let `w` be continuous and bounded (`|w| ≤ M`) on `(0,1]` with `∫_0^1 φ_a(t) w(t) dt = 0` for every
`a ≥ 1`, where `φ_a(t) = {1/(at)} − 2{1/(2at)} = φ_1(at)`.  With

* `W(z) = ∫_0^1 t^{z−1} w(t) dt` (analytic on `Re z > 0`, `|W(z)| ≤ M/Re z`),
* the correlation `F(a) = ∫_0^1 φ_1(at) w(t) dt` (`|F| ≤ 3M`, `F = 0` on `[1, ∞)`),
* `Φ₀(s) = ∫_0^∞ a^{s−1} F(a) da` (analytic on `Re s > 0`, `|Φ₀(s)| ≤ 3M/Re s`),

Fubini and the scaling rule of the Mellin transform give on the strip `0 < Re s < 1`

`Φ₀(s) = M[φ_1](s) · W(1 − s) = −(1 − 2^{1−s}) ζ(s) W(1 − s)/s`.

This is the input for the rigidity of bounded witnesses: `(1 − 2^{−z}) W(z)` continues to an entire
function whose only possible obstruction is a zero of `ζ` on `Re s = 1`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.NymanMellin

/-- A bounded witness: continuous, bounded by `M` on `(0,1]`, orthogonal to every `φ_a`, `a ≥ 1`. -/
structure IsBoundedFermiWitness (w : ℝ → ℂ) (M : ℝ) : Prop where
  cont : ContinuousOn w (Ioc 0 1)
  bound : ∀ t ∈ Ioc (0 : ℝ) 1, ‖w t‖ ≤ M
  orth : ∀ a : ℝ, 1 ≤ a → ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * w t = 0

/-- The extension of `w` by zero outside `(0,1]`. -/
def unitExt (w : ℝ → ℂ) : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator w

variable {w : ℝ → ℂ} {M : ℝ}

theorem IsBoundedFermiWitness.nonneg (hw : IsBoundedFermiWitness w M) : 0 ≤ M :=
  le_trans (norm_nonneg _) (hw.bound 1 ⟨one_pos, le_rfl⟩)

theorem IsBoundedFermiWitness.aestronglyMeasurable_unitExt (hw : IsBoundedFermiWitness w M) :
    AEStronglyMeasurable (unitExt w) volume :=
  (aestronglyMeasurable_indicator_iff measurableSet_Ioc).2
    (hw.cont.aestronglyMeasurable measurableSet_Ioc)

theorem IsBoundedFermiWitness.norm_unitExt_le (hw : IsBoundedFermiWitness w M) (t : ℝ) :
    ‖unitExt w t‖ ≤ M := by
  unfold unitExt
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem ht]; exact hw.bound t ht
  · rw [Set.indicator_of_notMem ht, norm_zero]; exact hw.nonneg

theorem unitExt_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) : unitExt w t = 0 := by
  have hn : t ∉ Ioc (0 : ℝ) 1 := fun h => by linarith [h.2]
  unfold unitExt
  rw [Set.indicator_of_notMem hn]

/-! ## The Mellin transform of the witness -/

/-- `W(z) = ∫_0^1 t^{z−1} w(t) dt`. -/
def boundedWitnessMellin (w : ℝ → ℂ) (z : ℂ) : ℂ := mellin (unitExt w) z

theorem unitExt_isBigO_atTop (w : ℝ → ℂ) (r : ℝ) :
    (unitExt w) =O[atTop] fun x : ℝ => x ^ (-r) := by
  refine Asymptotics.IsBigO.of_bound 0 ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  rw [unitExt_eq_zero_of_one_lt hx, norm_zero, zero_mul]

theorem IsBoundedFermiWitness.unitExt_isBigO_zero (hw : IsBoundedFermiWitness w M) :
    (unitExt w) =O[𝓝[>] 0] fun x : ℝ => x ^ (-(0 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound M ?_
  filter_upwards with x
  rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact hw.norm_unitExt_le x

theorem IsBoundedFermiWitness.locallyIntegrableOn_unitExt (hw : IsBoundedFermiWitness w M) :
    LocallyIntegrableOn (unitExt w) (Ioi 0) volume := by
  have hint : IntegrableOn (unitExt w) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
    refine IntegrableOn.union ?_ ?_
    · exact Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
        hw.aestronglyMeasurable_unitExt
        (Filter.Eventually.of_forall fun x => hw.norm_unitExt_le x)
    · refine (integrableOn_zero).congr_fun (fun x hx => ?_) measurableSet_Ioi
      exact (unitExt_eq_zero_of_one_lt hx).symm
  exact hint.locallyIntegrableOn

theorem IsBoundedFermiWitness.differentiableAt_boundedWitnessMellin
    (hw : IsBoundedFermiWitness w M) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (boundedWitnessMellin w) z :=
  mellin_differentiableAt_of_isBigO_rpow (a := z.re + 1) (b := 0)
    hw.locallyIntegrableOn_unitExt (unitExt_isBigO_atTop w _) (by linarith)
    hw.unitExt_isBigO_zero hz

theorem boundedWitnessMellin_eq_integral (w : ℝ → ℂ) (z : ℂ) :
    boundedWitnessMellin w z = ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (z - 1) * w t := by
  unfold boundedWitnessMellin mellin unitExt
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
  · refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    rw [Set.indicator_of_mem ht, smul_eq_mul]
  · intro t ht
    rw [Set.indicator_of_notMem ht.2, smul_zero]

theorem IsBoundedFermiWitness.norm_boundedWitnessMellin_le (hw : IsBoundedFermiWitness w M)
    {z : ℂ} (hz : 0 < z.re) : ‖boundedWitnessMellin w z‖ ≤ M / z.re := by
  rw [boundedWitnessMellin_eq_integral]
  have hint : IntegrableOn (fun t : ℝ => M * t ^ (z.re - 1)) (Ioc 0 1) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := z.re - 1)
      (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.const_mul M
  calc ‖∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (z - 1) * w t‖
      ≤ ∫ t in Ioc (0 : ℝ) 1, M * t ^ (z.re - 1) := by
        refine norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioc ?_)
        intro t ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.sub_re, Complex.one_re,
          mul_comm]
        exact mul_le_mul_of_nonneg_right (hw.bound t ht) (Real.rpow_nonneg ht.1.le _)
    _ = M / z.re := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
          integral_rpow (Or.inl (by linarith))]
        simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hz.ne', sub_zero]
        field_simp

theorem IsBoundedFermiWitness.measurable_unitExt (hw : IsBoundedFermiWitness w M) :
    Measurable (unitExt w) := by
  classical
  have h := ContinuousOn.measurable_piecewise (s := Ioc (0 : ℝ) 1) (f := w) (g := fun _ => 0)
    hw.cont continuousOn_const measurableSet_Ioc
  convert h using 1
  funext t
  unfold unitExt
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem ht, Set.piecewise_eq_of_mem _ _ _ ht]
  · rw [Set.indicator_of_notMem ht, Set.piecewise_eq_of_notMem _ _ _ ht]

/-! ## The correlation with the generators -/

/-- The correlation `F(a) = ∫ φ_1(at) w(t) dt` over `t ∈ (0,1]`. -/
def witnessCorrelation (w : ℝ → ℂ) (a : ℝ) : ℂ := ∫ t, fermiNymanGen 1 (a * t) * unitExt w t

theorem fermiNymanGen_one_mul (a t : ℝ) : fermiNymanGen 1 (a * t) = fermiNymanGen a t := by
  unfold fermiNymanGen nymanGen
  rw [one_mul, show 2 * 1 * (a * t) = 2 * a * t by ring]

theorem witnessCorrelation_eq (w : ℝ → ℂ) (a : ℝ) :
    witnessCorrelation w a = ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * w t := by
  unfold witnessCorrelation unitExt
  simp_rw [fermiNymanGen_one_mul]
  have : (fun t => fermiNymanGen a t * (Ioc (0 : ℝ) 1).indicator w t) =
      (Ioc (0 : ℝ) 1).indicator (fun t => fermiNymanGen a t * w t) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
  rw [this, integral_indicator measurableSet_Ioc]

theorem IsBoundedFermiWitness.witnessCorrelation_eq_zero (hw : IsBoundedFermiWitness w M) {a : ℝ}
    (ha : 1 ≤ a) : witnessCorrelation w a = 0 := by
  rw [witnessCorrelation_eq]; exact hw.orth a ha

theorem IsBoundedFermiWitness.norm_witnessCorrelation_le (hw : IsBoundedFermiWitness w M) (a : ℝ) :
    ‖witnessCorrelation w a‖ ≤ 3 * M := by
  rw [witnessCorrelation_eq]
  calc ‖∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * w t‖
      ≤ ∫ t in Ioc (0 : ℝ) 1, 3 * M := by
        refine norm_integral_le_of_norm_le (integrableOn_const measure_Ioc_lt_top.ne)
          (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
        rw [norm_mul]
        exact mul_le_mul (norm_fermiNymanGen_le a t) (hw.bound t ht) (norm_nonneg _) (by norm_num)
    _ = 3 * M := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le zero_le_one, smul_eq_mul]; ring

theorem IsBoundedFermiWitness.measurable_correlationIntegrand (hw : IsBoundedFermiWitness w M) :
    Measurable (fun p : ℝ × ℝ => fermiNymanGen 1 (p.1 * p.2) * unitExt w p.2) :=
  ((measurable_fermiNymanGen 1).comp (measurable_fst.mul measurable_snd)).mul
    (hw.measurable_unitExt.comp measurable_snd)

theorem IsBoundedFermiWitness.aestronglyMeasurable_witnessCorrelation
    (hw : IsBoundedFermiWitness w M) : AEStronglyMeasurable (witnessCorrelation w) volume :=
  (hw.measurable_correlationIntegrand.aestronglyMeasurable (μ := volume.prod volume)).integral_prod_right'

/-- `Φ₀(s) = ∫_0^∞ a^{s−1} F(a) da`. -/
def correlationMellin (w : ℝ → ℂ) (s : ℂ) : ℂ := mellin (witnessCorrelation w) s

theorem IsBoundedFermiWitness.differentiableAt_correlationMellin (hw : IsBoundedFermiWitness w M)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (correlationMellin w) s := by
  have hloc : LocallyIntegrableOn (witnessCorrelation w) (Ioi 0) volume := by
    have hint : IntegrableOn (witnessCorrelation w) (Ioi 0) := by
      rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
      refine IntegrableOn.union ?_ ?_
      · exact Measure.integrableOn_of_bounded (M := 3 * M) measure_Ioc_lt_top.ne
          hw.aestronglyMeasurable_witnessCorrelation
          (Filter.Eventually.of_forall fun x => hw.norm_witnessCorrelation_le x)
      · refine (integrableOn_zero).congr_fun (fun x hx => ?_) measurableSet_Ioi
        exact (hw.witnessCorrelation_eq_zero (le_of_lt hx)).symm
    exact hint.locallyIntegrableOn
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0) hloc ?_ (by linarith) ?_ hs
  · refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [hw.witnessCorrelation_eq_zero hx, norm_zero, zero_mul]
  · refine Asymptotics.IsBigO.of_bound (3 * M) ?_
    filter_upwards with x
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact hw.norm_witnessCorrelation_le x

theorem IsBoundedFermiWitness.norm_correlationMellin_le (hw : IsBoundedFermiWitness w M)
    {s : ℂ} (hs : 0 < s.re) : ‖correlationMellin w s‖ ≤ 3 * M / s.re := by
  unfold correlationMellin mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    (fun t ht => by
      have ht1 : 1 < t := by
        rcases ht with ⟨ht0, htn⟩
        simp only [mem_Ioc, not_and, not_le] at htn
        exact htn ht0
      rw [hw.witnessCorrelation_eq_zero ht1.le, smul_zero])]
  have hint : IntegrableOn (fun t : ℝ => 3 * M * t ^ (s.re - 1)) (Ioc 0 1) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := s.re - 1)
      (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.const_mul _
  calc ‖∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • witnessCorrelation w t‖
      ≤ ∫ t in Ioc (0 : ℝ) 1, 3 * M * t ^ (s.re - 1) := by
        refine norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioc ?_)
        intro t ht
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.sub_re, Complex.one_re,
          mul_comm]
        exact mul_le_mul_of_nonneg_right (hw.norm_witnessCorrelation_le t)
          (Real.rpow_nonneg ht.1.le _)
    _ = 3 * M / s.re := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
          integral_rpow (Or.inl (by linarith))]
        simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hs.ne', sub_zero]
        field_simp

/-! ## The Fubini identity -/

theorem mellinConvergent_fermiNymanGen {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {a : ℝ}
    (ha : 0 < a) : MellinConvergent (fermiNymanGen a) s := by
  have h1 := mellinConvergent_nymanGen hs0 hs1 ha
  have h2 := mellinConvergent_nymanGen hs0 hs1 (by positivity : (0 : ℝ) < 2 * a)
  unfold MellinConvergent at *
  refine (h1.sub (h2.const_mul 2)).congr_fun (fun t _ => ?_) measurableSet_Ioi
  unfold fermiNymanGen
  simp only [Pi.sub_apply, smul_eq_mul]
  ring

theorem setIntegral_Ioi_rpow_mul_norm_fermiNymanGen_le {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (ht : 0 < t) :
    (∫ a in Ioi (0 : ℝ), a ^ (σ - 1) * ‖fermiNymanGen t a‖) ≤ 3 * (1 / t) ^ σ / σ := by
  have hint1 : IntegrableOn (fun a : ℝ => 3 * a ^ (σ - 1)) (Ioc 0 (1 / t)) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 / t) (r := σ - 1)
      (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)] at this
    exact this.const_mul 3
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    (fun a ha => by
      have ha1 : 1 / t < a := by
        rcases ha with ⟨ha0, han⟩
        simp only [mem_Ioc, not_and, not_le] at han
        exact han ha0
      rw [fermiNymanGen_eq_zero_of_inv_lt ht ha1, norm_zero, mul_zero])]
  calc (∫ a in Ioc (0 : ℝ) (1 / t), a ^ (σ - 1) * ‖fermiNymanGen t a‖)
      ≤ ∫ a in Ioc (0 : ℝ) (1 / t), 3 * a ^ (σ - 1) := by
        refine setIntegral_mono_on ?_ hint1 measurableSet_Ioc (fun a ha => ?_)
        · refine hint1.mono' ((measurable_id.pow_const _).mul
            (measurable_fermiNymanGen t).norm).aestronglyMeasurable
            (ae_restrict_of_forall_mem measurableSet_Ioc fun a ha => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ha.1.le _)
            (norm_nonneg _)), mul_comm 3]
          exact mul_le_mul_of_nonneg_left (norm_fermiNymanGen_le t a) (Real.rpow_nonneg ha.1.le _)
        · rw [mul_comm 3]
          exact mul_le_mul_of_nonneg_left (norm_fermiNymanGen_le t a) (Real.rpow_nonneg ha.1.le _)
    _ = 3 * (1 / t) ^ σ / σ := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le (by positivity),
          integral_rpow (Or.inl (by linarith))]
        simp only [sub_add_cancel, Real.zero_rpow hσ.ne', sub_zero]
        ring

/-- **The Fubini identity.**  On the strip, `Φ₀(s) = M[φ_1](s) · W(1 − s)`. -/
theorem IsBoundedFermiWitness.correlationMellin_eq (hw : IsBoundedFermiWitness w M) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    correlationMellin w s = mellin (fermiNymanGen 1) s * boundedWitnessMellin w (1 - s) := by
  set f : ℝ → ℝ → ℂ := fun a t => (a : ℂ) ^ (s - 1) * (fermiNymanGen 1 (a * t) * unitExt w t)
    with hf
  have hmeas : Measurable (Function.uncurry f) := by
    refine ((Complex.continuous_ofReal.measurable.comp measurable_fst).pow_const _).mul ?_
    exact hw.measurable_correlationIntegrand
  have hswapMeas : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := hmeas.aestronglyMeasurable
  have hint : Integrable (Function.uncurry f) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    rw [integrable_prod_iff' hswapMeas]
    constructor
    · refine Filter.Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ Ioc (0 : ℝ) 1
      · have hc := (mellinConvergent_fermiNymanGen hs0 hs1 ht.1).const_smul (unitExt w t)
        unfold MellinConvergent at hc
        refine hc.congr_fun (fun a _ => ?_) measurableSet_Ioi
        simp only [Function.uncurry_apply_pair, hf, smul_eq_mul]
        rw [mul_comm a t, fermiNymanGen_one_mul]; ring
      · have h0 : ∀ a, Function.uncurry f (a, t) = 0 := fun a => by
          simp only [Function.uncurry_apply_pair, hf, unitExt, Set.indicator_of_notMem ht, mul_zero]
        simp only [h0]
        exact integrable_zero _ _ _
    · have hnormint : ∀ t ∈ Ioc (0 : ℝ) 1,
          (∫ a, ‖Function.uncurry f (a, t)‖ ∂(volume.restrict (Ioi (0 : ℝ)))) =
            ‖unitExt w t‖ * ∫ a in Ioi (0 : ℝ), a ^ (s.re - 1) * ‖fermiNymanGen t a‖ := by
        intro t ht
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi (fun a ha => ?_)
        simp only [Function.uncurry_apply_pair, hf]
        rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.sub_re,
          Complex.one_re, mul_comm a t, fermiNymanGen_one_mul]
        ring
      have hbd : ∀ t, ‖(∫ a, ‖Function.uncurry f (a, t)‖ ∂(volume.restrict (Ioi (0 : ℝ))))‖ ≤
          (Ioc (0 : ℝ) 1).indicator (fun t => M * (3 * (1 / t) ^ s.re / s.re)) t := by
        intro t
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        by_cases ht : t ∈ Ioc (0 : ℝ) 1
        · rw [Set.indicator_of_mem ht, hnormint t ht]
          exact mul_le_mul (hw.norm_unitExt_le t)
            (setIntegral_Ioi_rpow_mul_norm_fermiNymanGen_le hs0 ht.1)
            (setIntegral_nonneg measurableSet_Ioi fun a ha =>
              mul_nonneg (Real.rpow_nonneg (le_of_lt ha) _) (norm_nonneg _)) hw.nonneg
        · rw [Set.indicator_of_notMem ht]
          have h0 : ∀ a, Function.uncurry f (a, t) = 0 := fun a => by
            simp only [Function.uncurry_apply_pair, hf, unitExt, Set.indicator_of_notMem ht, mul_zero]
          simp [h0]
      have hG : Integrable ((Ioc (0 : ℝ) 1).indicator (fun t => M * (3 * (1 / t) ^ s.re / s.re))) := by
        rw [integrable_indicator_iff measurableSet_Ioc]
        have hI : IntegrableOn (fun t : ℝ => t ^ (-s.re)) (Ioc 0 1) :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
            (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -s.re)
              (by linarith))
        have hI' : IntegrableOn (fun t : ℝ => M * 3 / s.re * t ^ (-s.re)) (Ioc 0 1) :=
          hI.const_mul _
        refine hI'.congr_fun (fun t ht => ?_) measurableSet_Ioc
        rw [one_div, Real.inv_rpow ht.1.le, ← Real.rpow_neg ht.1.le]
        ring
      have hmeasN : AEStronglyMeasurable
          (fun t => ∫ a, ‖Function.uncurry f (a, t)‖ ∂(volume.restrict (Ioi (0 : ℝ)))) volume := by
        have h1 := (hswapMeas.norm).prod_swap
        exact h1.integral_prod_right'
      exact hG.mono' hmeasN (Filter.Eventually.of_forall hbd)
  -- the swap
  have hinner : ∀ t : ℝ, (∫ a in Ioi (0 : ℝ), f a t) =
      (Ioc (0 : ℝ) 1).indicator (fun t => (t : ℂ) ^ (-s) * w t) t * mellin (fermiNymanGen 1) s := by
    intro t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht]
      have hscale := mellin_comp_mul_left (fermiNymanGen 1) s ht.1
      have hcalc : (∫ a in Ioi (0 : ℝ), f a t) =
          mellin (fun a => fermiNymanGen 1 (t * a)) s * w t := by
        unfold mellin
        rw [← integral_mul_const]
        refine setIntegral_congr_fun measurableSet_Ioi (fun a _ => ?_)
        simp only [hf, unitExt, Set.indicator_of_mem ht, smul_eq_mul]
        rw [mul_comm a t]; ring
      rw [hcalc, hscale, smul_eq_mul]
      ring
    · rw [Set.indicator_of_notMem ht, zero_mul]
      refine setIntegral_eq_zero_of_forall_eq_zero (fun a _ => ?_)
      simp only [hf, unitExt, Set.indicator_of_notMem ht, mul_zero]
  have hlhs : correlationMellin w s = ∫ a in Ioi (0 : ℝ), ∫ t, f a t := by
    unfold correlationMellin mellin witnessCorrelation
    refine setIntegral_congr_fun measurableSet_Ioi (fun a _ => ?_)
    simp only [hf, smul_eq_mul]
    rw [← integral_const_mul]
  rw [hlhs, integral_integral_swap hint]
  simp_rw [hinner]
  rw [integral_mul_const, integral_indicator measurableSet_Ioc, boundedWitnessMellin_eq_integral]
  have hexp : ∀ t : ℝ, (t : ℂ) ^ (1 - s - 1) * w t = (t : ℂ) ^ (-s) * w t := fun t => by
    rw [show (1 : ℂ) - s - 1 = -s by ring]
  simp_rw [hexp]
  ring

end RHTower
