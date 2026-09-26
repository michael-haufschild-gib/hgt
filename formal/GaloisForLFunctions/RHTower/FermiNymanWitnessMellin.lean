import GaloisForLFunctions.RHTower.FermiNymanBeurlingWitnessSignature
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding

/-!
# Mellin analysis of witnesses of the alternating Nyman–Beurling system

A witness of Mellin exponent `a < 1` is a function `w`, continuous on `(0,1]`, with
`∫_0^1 φ_b(t) w(t) dt = 0` for every `b ≥ 1`, where `φ_b(t) = {1/(bt)} − 2{1/(2bt)} = φ_1(bt)`, and
with finite Mellin majorant `m(x) = ∫_0^1 t^{x−1}|w(t)| dt` for every `x > a`.  Bounded witnesses have
exponent `0`, square-integrable ones exponent `½`, and the zero witness `t^{ρ̄−1}` has exponent
`1 − Re ρ`.  With

* `W(z) = ∫_0^1 t^{z−1} w(t) dt` (analytic on `Re z > a`, `|W(z)| ≤ m(Re z)`),
* the correlation `F(b) = ∫_0^1 φ_1(bt) w(t) dt` (`|F| ≤ 3 m(1)`, `F = 0` on `[1, ∞)`),
* `Φ₀(s) = ∫_0^∞ b^{s−1} F(b) db` (analytic on `Re s > 0`, `|Φ₀(s)| ≤ 3 m(1)/Re s`),

Fubini and the scaling rule of the Mellin transform give on the strip `0 < Re s < 1 − a`

`Φ₀(s) = M[φ_1](s) · W(1 − s) = −(1 − 2^{1−s}) ζ(s) W(1 − s)/s`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.NymanMellin

/-- A witness of Mellin exponent `a`: continuous on `(0,1]`, orthogonal to every `φ_b`, `b ≥ 1`,
with `∫_0^1 t^{x−1}|w|` finite for every `x > a`, and `a < 1`. -/
structure IsMellinFermiWitness (w : ℝ → ℂ) (a : ℝ) : Prop where
  cont : ContinuousOn w (Ioc 0 1)
  nonneg : 0 ≤ a
  lt_one : a < 1
  integ : ∀ x : ℝ, a < x → IntegrableOn (fun t : ℝ => t ^ (x - 1) * ‖w t‖) (Ioc 0 1)
  orth : ∀ b : ℝ, 1 ≤ b → ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen b t * w t = 0

/-- The extension of `w` by zero outside `(0,1]`. -/
def unitExt (w : ℝ → ℂ) : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator w

/-- The Mellin majorant `m(x) = ∫_0^1 t^{x−1}|w(t)| dt`. -/
def witnessMajorant (w : ℝ → ℂ) (x : ℝ) : ℝ := ∫ t in Ioc (0 : ℝ) 1, t ^ (x - 1) * ‖w t‖

variable {w : ℝ → ℂ} {a : ℝ}

theorem witnessMajorant_nonneg (w : ℝ → ℂ) (x : ℝ) : 0 ≤ witnessMajorant w x :=
  setIntegral_nonneg measurableSet_Ioc fun _ ht =>
    mul_nonneg (Real.rpow_nonneg ht.1.le _) (norm_nonneg _)

theorem unitExt_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) : unitExt w t = 0 := by
  have hn : t ∉ Ioc (0 : ℝ) 1 := fun h => by linarith [h.2]
  unfold unitExt
  rw [Set.indicator_of_notMem hn]

theorem measurable_unitExt_of_continuousOn (hw : ContinuousOn w (Ioc 0 1)) :
    Measurable (unitExt w) := by
  classical
  have h := ContinuousOn.measurable_piecewise (s := Ioc (0 : ℝ) 1) (f := w) (g := fun _ => 0)
    hw continuousOn_const measurableSet_Ioc
  convert h using 1
  funext t
  unfold unitExt
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem ht, Set.piecewise_eq_of_mem _ _ _ ht]
  · rw [Set.indicator_of_notMem ht, Set.piecewise_eq_of_notMem _ _ _ ht]

theorem IsMellinFermiWitness.measurable_unitExt (hw : IsMellinFermiWitness w a) :
    Measurable (unitExt w) :=
  measurable_unitExt_of_continuousOn hw.cont

theorem IsMellinFermiWitness.integrableOn_norm (hw : IsMellinFermiWitness w a) :
    IntegrableOn (fun t : ℝ => ‖w t‖) (Ioc 0 1) := by
  refine (hw.integ 1 hw.lt_one).congr_fun (fun t _ => ?_) measurableSet_Ioc
  simp

theorem witnessMajorant_one (w : ℝ → ℂ) :
    witnessMajorant w 1 = ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ := by
  unfold witnessMajorant
  refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
  simp

theorem IsMellinFermiWitness.integrableOn_cpow_mul (hw : IsMellinFermiWitness w a) {z : ℂ}
    (hz : a < z.re) : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * w t) (Ioc 0 1) := by
  refine (hw.integ z.re hz).mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine ContinuousOn.mul ?_ hw.cont
    intro t ht
    exact ((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 ht.1)).continuousWithinAt
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.sub_re, Complex.one_re]

/-! ## The Mellin transform of the witness -/

/-- `W(z) = ∫_0^1 t^{z−1} w(t) dt`. -/
def witnessMellin (w : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (z - 1) * w t

theorem witnessMellin_eq_mellin (w : ℝ → ℂ) (z : ℂ) : witnessMellin w z = mellin (unitExt w) z := by
  unfold witnessMellin mellin unitExt
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
  · refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    rw [Set.indicator_of_mem ht, smul_eq_mul]
  · intro t ht
    rw [Set.indicator_of_notMem ht.2, smul_zero]

theorem IsMellinFermiWitness.norm_witnessMellin_le (hw : IsMellinFermiWitness w a) {z : ℂ}
    (hz : a < z.re) : ‖witnessMellin w z‖ ≤ witnessMajorant w z.re := by
  unfold witnessMellin witnessMajorant
  refine norm_integral_le_of_norm_le (hw.integ z.re hz)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.sub_re, Complex.one_re]

/-- **`W` is analytic on `Re z > a`**, by differentiation under the integral sign with the
dominating function `ε⁻¹ t^{Re z₀ − 2ε − 1}|w(t)|`, `ε = (Re z₀ − a)/3`. -/
theorem IsMellinFermiWitness.differentiableAt_witnessMellin (hw : IsMellinFermiWitness w a)
    {z₀ : ℂ} (hz₀ : a < z₀.re) : DifferentiableAt ℂ (witnessMellin w) z₀ := by
  set ε : ℝ := (z₀.re - a) / 3 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set F : ℂ → ℝ → ℂ := fun z t => (t : ℂ) ^ (z - 1) * w t with hF
  set F' : ℂ → ℝ → ℂ := fun z t => (t : ℂ) ^ (z - 1) * Complex.log t * w t with hF'
  have hball : Metric.ball z₀ ε ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hε0
  have hre : ∀ z ∈ Metric.ball z₀ ε, z₀.re - ε < z.re := by
    intro z hz
    have h1 := Complex.abs_re_le_norm (z - z₀)
    rw [Complex.sub_re] at h1
    have h2 : ‖z - z₀‖ < ε := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    linarith [neg_abs_le (z.re - z₀.re)]
  have hmeasF : ∀ z : ℂ, a < z.re →
      AEStronglyMeasurable (F z) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    fun z hz => (hw.integrableOn_cpow_mul hz).aestronglyMeasurable
  have hbound_int : Integrable (fun t : ℝ => ε⁻¹ * (t ^ ((z₀.re - 2 * ε) - 1) * ‖w t‖))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hw.integ _ (by rw [hε]; linarith)).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (F := F) (F' := F') (x₀ := z₀)
    (bound := fun t => ε⁻¹ * (t ^ ((z₀.re - 2 * ε) - 1) * ‖w t‖)) hball
    (by
      filter_upwards [hball] with z hz
      exact hmeasF z (by linarith [hre z hz]))
    (hw.integrableOn_cpow_mul hz₀)
    (by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) hw.cont
      · intro t ht
        exact ((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
          (Complex.ofReal_mem_slitPlane.2 ht.1)).continuousWithinAt
      · intro t ht
        exact ((Complex.continuous_ofReal.continuousAt).clog
          (Complex.ofReal_mem_slitPlane.2 ht.1)).continuousWithinAt)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht z hz => by
      have ht0 := ht.1
      have hzr := hre z hz
      simp only [hF']
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re,
        Complex.one_re, ← Complex.ofReal_log ht0.le, Complex.norm_real, Real.norm_eq_abs]
      have hpow : t ^ (z.re - 1) ≤ t ^ ((z₀.re - ε) - 1) :=
        Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 (by linarith)
      have hlog : |Real.log t| * t ^ ε ≤ ε⁻¹ := by
        have := Real.abs_log_mul_self_rpow_lt t ε ht0 ht.2 hε0
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 ε)] at this
        rw [inv_eq_one_div]; exact this.le
      have hsplit : t ^ ((z₀.re - ε) - 1) = t ^ ((z₀.re - 2 * ε) - 1) * t ^ ε := by
        rw [← Real.rpow_add ht0]; ring_nf
      calc t ^ (z.re - 1) * |Real.log t| * ‖w t‖
          ≤ t ^ ((z₀.re - ε) - 1) * |Real.log t| * ‖w t‖ := by gcongr
        _ = (|Real.log t| * t ^ ε) * (t ^ ((z₀.re - 2 * ε) - 1) * ‖w t‖) := by
            rw [hsplit]; ring
        _ ≤ ε⁻¹ * (t ^ ((z₀.re - 2 * ε) - 1) * ‖w t‖) :=
            mul_le_mul_of_nonneg_right hlog
              (mul_nonneg (Real.rpow_nonneg ht0.le _) (norm_nonneg _)))
    hbound_int
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht z _ => by
      have h := ((hasDerivAt_id z).sub_const 1).const_cpow
        (c := (t : ℂ)) (Or.inl (Complex.ofReal_ne_zero.2 ht.1.ne'))
      simp only [hF, hF', mul_one] at h ⊢
      exact h.mul_const (w t))
  exact key.2.differentiableAt

/-! ## The correlation with the generators -/

/-- The correlation `F(b) = ∫ φ_1(bt) w(t) dt` over `t ∈ (0,1]`. -/
def witnessCorrelation (w : ℝ → ℂ) (b : ℝ) : ℂ := ∫ t, fermiNymanGen 1 (b * t) * unitExt w t

theorem fermiNymanGen_one_mul (b t : ℝ) : fermiNymanGen 1 (b * t) = fermiNymanGen b t := by
  unfold fermiNymanGen nymanGen
  rw [one_mul, show 2 * 1 * (b * t) = 2 * b * t by ring]

theorem witnessCorrelation_eq (w : ℝ → ℂ) (b : ℝ) :
    witnessCorrelation w b = ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen b t * w t := by
  unfold witnessCorrelation unitExt
  simp_rw [fermiNymanGen_one_mul]
  have : (fun t => fermiNymanGen b t * (Ioc (0 : ℝ) 1).indicator w t) =
      (Ioc (0 : ℝ) 1).indicator (fun t => fermiNymanGen b t * w t) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
  rw [this, integral_indicator measurableSet_Ioc]

theorem IsMellinFermiWitness.witnessCorrelation_eq_zero (hw : IsMellinFermiWitness w a) {b : ℝ}
    (hb : 1 ≤ b) : witnessCorrelation w b = 0 := by
  rw [witnessCorrelation_eq]; exact hw.orth b hb

theorem IsMellinFermiWitness.norm_witnessCorrelation_le (hw : IsMellinFermiWitness w a) (b : ℝ) :
    ‖witnessCorrelation w b‖ ≤ 3 * witnessMajorant w 1 := by
  rw [witnessCorrelation_eq, witnessMajorant_one, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hw.integrableOn_norm.const_mul 3)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_fermiNymanGen_le b t) (norm_nonneg _)

theorem IsMellinFermiWitness.measurable_correlationIntegrand (hw : IsMellinFermiWitness w a) :
    Measurable (fun p : ℝ × ℝ => fermiNymanGen 1 (p.1 * p.2) * unitExt w p.2) :=
  ((measurable_fermiNymanGen 1).comp (measurable_fst.mul measurable_snd)).mul
    (hw.measurable_unitExt.comp measurable_snd)

theorem IsMellinFermiWitness.aestronglyMeasurable_witnessCorrelation
    (hw : IsMellinFermiWitness w a) : AEStronglyMeasurable (witnessCorrelation w) volume :=
  (hw.measurable_correlationIntegrand.aestronglyMeasurable
    (μ := volume.prod volume)).integral_prod_right'

/-- `Φ₀(s) = ∫_0^∞ b^{s−1} F(b) db`. -/
def correlationMellin (w : ℝ → ℂ) (s : ℂ) : ℂ := mellin (witnessCorrelation w) s

theorem IsMellinFermiWitness.differentiableAt_correlationMellin (hw : IsMellinFermiWitness w a)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (correlationMellin w) s := by
  have hloc : LocallyIntegrableOn (witnessCorrelation w) (Ioi 0) volume := by
    have hint : IntegrableOn (witnessCorrelation w) (Ioi 0) := by
      rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
      refine IntegrableOn.union ?_ ?_
      · exact Measure.integrableOn_of_bounded (M := 3 * witnessMajorant w 1)
          measure_Ioc_lt_top.ne hw.aestronglyMeasurable_witnessCorrelation
          (Filter.Eventually.of_forall fun x => hw.norm_witnessCorrelation_le x)
      · refine (integrableOn_zero).congr_fun (fun x hx => ?_) measurableSet_Ioi
        exact (hw.witnessCorrelation_eq_zero (le_of_lt hx)).symm
    exact hint.locallyIntegrableOn
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0) hloc ?_ (by linarith) ?_ hs
  · refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [hw.witnessCorrelation_eq_zero hx, norm_zero, zero_mul]
  · refine Asymptotics.IsBigO.of_bound (3 * witnessMajorant w 1) ?_
    filter_upwards with x
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact hw.norm_witnessCorrelation_le x

theorem IsMellinFermiWitness.norm_correlationMellin_le (hw : IsMellinFermiWitness w a)
    {s : ℂ} (hs : 0 < s.re) : ‖correlationMellin w s‖ ≤ 3 * witnessMajorant w 1 / s.re := by
  unfold correlationMellin mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    (fun t ht => by
      have ht1 : 1 < t := by
        rcases ht with ⟨ht0, htn⟩
        simp only [mem_Ioc, not_and, not_le] at htn
        exact htn ht0
      rw [hw.witnessCorrelation_eq_zero ht1.le, smul_zero])]
  have hint : IntegrableOn (fun t : ℝ => 3 * witnessMajorant w 1 * t ^ (s.re - 1)) (Ioc 0 1) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := s.re - 1)
      (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.const_mul _
  calc ‖∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • witnessCorrelation w t‖
      ≤ ∫ t in Ioc (0 : ℝ) 1, 3 * witnessMajorant w 1 * t ^ (s.re - 1) := by
        refine norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioc ?_)
        intro t ht
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.sub_re, Complex.one_re,
          mul_comm]
        exact mul_le_mul_of_nonneg_right (hw.norm_witnessCorrelation_le t)
          (Real.rpow_nonneg ht.1.le _)
    _ = 3 * witnessMajorant w 1 / s.re := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
          integral_rpow (Or.inl (by linarith))]
        simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hs.ne', sub_zero]
        field_simp

/-! ## The Fubini identity -/

theorem mellinConvergent_fermiNymanGen {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {b : ℝ}
    (hb : 0 < b) : MellinConvergent (fermiNymanGen b) s := by
  have h1 := mellinConvergent_nymanGen hs0 hs1 hb
  have h2 := mellinConvergent_nymanGen hs0 hs1 (by positivity : (0 : ℝ) < 2 * b)
  unfold MellinConvergent at *
  refine (h1.sub (h2.const_mul 2)).congr_fun (fun t _ => ?_) measurableSet_Ioi
  unfold fermiNymanGen
  simp only [Pi.sub_apply, smul_eq_mul]
  ring

theorem setIntegral_Ioi_rpow_mul_norm_fermiNymanGen_le {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (ht : 0 < t) :
    (∫ b in Ioi (0 : ℝ), b ^ (σ - 1) * ‖fermiNymanGen t b‖) ≤ 3 * (1 / t) ^ σ / σ := by
  have hint1 : IntegrableOn (fun b : ℝ => 3 * b ^ (σ - 1)) (Ioc 0 (1 / t)) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 / t) (r := σ - 1)
      (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)] at this
    exact this.const_mul 3
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    (fun b hb => by
      have hb1 : 1 / t < b := by
        rcases hb with ⟨hb0, hbn⟩
        simp only [mem_Ioc, not_and, not_le] at hbn
        exact hbn hb0
      rw [fermiNymanGen_eq_zero_of_inv_lt ht hb1, norm_zero, mul_zero])]
  calc (∫ b in Ioc (0 : ℝ) (1 / t), b ^ (σ - 1) * ‖fermiNymanGen t b‖)
      ≤ ∫ b in Ioc (0 : ℝ) (1 / t), 3 * b ^ (σ - 1) := by
        refine setIntegral_mono_on ?_ hint1 measurableSet_Ioc (fun b hb => ?_)
        · refine hint1.mono' ((measurable_id.pow_const _).mul
            (measurable_fermiNymanGen t).norm).aestronglyMeasurable
            (ae_restrict_of_forall_mem measurableSet_Ioc fun b hb => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hb.1.le _)
            (norm_nonneg _)), mul_comm 3]
          exact mul_le_mul_of_nonneg_left (norm_fermiNymanGen_le t b) (Real.rpow_nonneg hb.1.le _)
        · rw [mul_comm 3]
          exact mul_le_mul_of_nonneg_left (norm_fermiNymanGen_le t b) (Real.rpow_nonneg hb.1.le _)
    _ = 3 * (1 / t) ^ σ / σ := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le (by positivity),
          integral_rpow (Or.inl (by linarith))]
        simp only [sub_add_cancel, Real.zero_rpow hσ.ne', sub_zero]
        ring

/-- **The Fubini identity.**  On `0 < Re s < 1 − a`, `Φ₀(s) = M[φ_1](s) · W(1 − s)`. -/
theorem IsMellinFermiWitness.correlationMellin_eq (hw : IsMellinFermiWitness w a) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 - a) :
    correlationMellin w s = mellin (fermiNymanGen 1) s * witnessMellin w (1 - s) := by
  have hs1' : s.re < 1 := by linarith [hw.nonneg]
  set f : ℝ → ℝ → ℂ := fun b t => (b : ℂ) ^ (s - 1) * (fermiNymanGen 1 (b * t) * unitExt w t)
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
      · have hc := (mellinConvergent_fermiNymanGen hs0 hs1' ht.1).const_smul (unitExt w t)
        unfold MellinConvergent at hc
        refine hc.congr_fun (fun b _ => ?_) measurableSet_Ioi
        simp only [Function.uncurry_apply_pair, hf, smul_eq_mul]
        rw [mul_comm b t, fermiNymanGen_one_mul]; ring
      · have h0 : ∀ b, Function.uncurry f (b, t) = 0 := fun b => by
          simp only [Function.uncurry_apply_pair, hf, unitExt, Set.indicator_of_notMem ht, mul_zero]
        simp only [h0]
        exact integrable_zero _ _ _
    · have hnormint : ∀ t ∈ Ioc (0 : ℝ) 1,
          (∫ b, ‖Function.uncurry f (b, t)‖ ∂(volume.restrict (Ioi (0 : ℝ)))) =
            ‖unitExt w t‖ * ∫ b in Ioi (0 : ℝ), b ^ (s.re - 1) * ‖fermiNymanGen t b‖ := by
        intro t ht
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi (fun b hb => ?_)
        simp only [Function.uncurry_apply_pair, hf]
        rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb, Complex.sub_re,
          Complex.one_re, mul_comm b t, fermiNymanGen_one_mul]
        ring
      have hbd : ∀ t, ‖(∫ b, ‖Function.uncurry f (b, t)‖ ∂(volume.restrict (Ioi (0 : ℝ))))‖ ≤
          (Ioc (0 : ℝ) 1).indicator (fun t => ‖w t‖ * (3 * (1 / t) ^ s.re / s.re)) t := by
        intro t
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        by_cases ht : t ∈ Ioc (0 : ℝ) 1
        · rw [Set.indicator_of_mem ht, hnormint t ht, unitExt, Set.indicator_of_mem ht]
          exact mul_le_mul_of_nonneg_left
            (setIntegral_Ioi_rpow_mul_norm_fermiNymanGen_le hs0 ht.1) (norm_nonneg _)
        · rw [Set.indicator_of_notMem ht]
          have h0 : ∀ b, Function.uncurry f (b, t) = 0 := fun b => by
            simp only [Function.uncurry_apply_pair, hf, unitExt, Set.indicator_of_notMem ht, mul_zero]
          simp [h0]
      have hG : Integrable
          ((Ioc (0 : ℝ) 1).indicator (fun t => ‖w t‖ * (3 * (1 / t) ^ s.re / s.re))) := by
        rw [integrable_indicator_iff measurableSet_Ioc]
        have hI : IntegrableOn (fun t : ℝ => 3 / s.re * (t ^ (1 - s.re - 1) * ‖w t‖)) (Ioc 0 1) :=
          (hw.integ (1 - s.re) (by linarith)).const_mul (3 / s.re)
        refine hI.congr_fun (fun t ht => ?_) measurableSet_Ioc
        rw [one_div, Real.inv_rpow ht.1.le, ← Real.rpow_neg ht.1.le,
          show 1 - s.re - 1 = -s.re by ring]
        ring
      have hmeasN : AEStronglyMeasurable
          (fun t => ∫ b, ‖Function.uncurry f (b, t)‖ ∂(volume.restrict (Ioi (0 : ℝ)))) volume := by
        have h1 := (hswapMeas.norm).prod_swap
        exact h1.integral_prod_right'
      exact hG.mono' hmeasN (Filter.Eventually.of_forall hbd)
  -- the swap
  have hinner : ∀ t : ℝ, (∫ b in Ioi (0 : ℝ), f b t) =
      (Ioc (0 : ℝ) 1).indicator (fun t => (t : ℂ) ^ (-s) * w t) t * mellin (fermiNymanGen 1) s := by
    intro t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht]
      have hscale := mellin_comp_mul_left (fermiNymanGen 1) s ht.1
      have hcalc : (∫ b in Ioi (0 : ℝ), f b t) =
          mellin (fun b => fermiNymanGen 1 (t * b)) s * w t := by
        unfold mellin
        rw [← integral_mul_const]
        refine setIntegral_congr_fun measurableSet_Ioi (fun b _ => ?_)
        simp only [hf, unitExt, Set.indicator_of_mem ht, smul_eq_mul]
        rw [mul_comm b t]; ring
      rw [hcalc, hscale, smul_eq_mul]
      ring
    · rw [Set.indicator_of_notMem ht, zero_mul]
      refine setIntegral_eq_zero_of_forall_eq_zero (fun b _ => ?_)
      simp only [hf, unitExt, Set.indicator_of_notMem ht, mul_zero]
  have hlhs : correlationMellin w s = ∫ b in Ioi (0 : ℝ), ∫ t, f b t := by
    unfold correlationMellin mellin witnessCorrelation
    refine setIntegral_congr_fun measurableSet_Ioi (fun b _ => ?_)
    simp only [hf, smul_eq_mul]
    rw [← integral_const_mul]
  rw [hlhs, integral_integral_swap hint]
  simp_rw [hinner]
  rw [integral_mul_const, integral_indicator measurableSet_Ioc]
  unfold witnessMellin
  have hexp : ∀ t : ℝ, (t : ℂ) ^ (1 - s - 1) * w t = (t : ℂ) ^ (-s) * w t := fun t => by
    rw [show (1 : ℂ) - s - 1 = -s by ring]
  simp_rw [hexp]
  ring

/-! ## Bounded witnesses -/

/-- A bounded continuous function on `(0,1]` has finite Mellin majorant at every `x > 0`. -/
theorem integrableOn_rpow_mul_norm_of_bounded {M : ℝ} (hc : ContinuousOn w (Ioc 0 1))
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖w t‖ ≤ M) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t ^ (x - 1) * ‖w t‖) (Ioc 0 1) := by
  have hI : IntegrableOn (fun t : ℝ => M * t ^ (x - 1)) (Ioc 0 1) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := x - 1)
      (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.const_mul M
  refine hI.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact (continuousOn_id.rpow_const fun t ht => Or.inl ht.1.ne').mul hc.norm
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (norm_nonneg _)),
      mul_comm M]
    exact mul_le_mul_of_nonneg_left (hb t ht) (Real.rpow_nonneg ht.1.le _)

/-- A bounded witness has Mellin exponent `0`. -/
theorem isMellinFermiWitness_of_bounded {M : ℝ} (hc : ContinuousOn w (Ioc 0 1))
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖w t‖ ≤ M)
    (ho : ∀ b : ℝ, 1 ≤ b → ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen b t * w t = 0) :
    IsMellinFermiWitness w 0 :=
  ⟨hc, le_rfl, zero_lt_one, fun _ hx => integrableOn_rpow_mul_norm_of_bounded hc hb hx, ho⟩

end RHTower
