import GaloisForLFunctions.RHTower.CHMDFullJumpMoment
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover
import GaloisForLFunctions.HTGeometry.YoungConvolutionL2

/-!
# Compact-domain transfer to the stationary archimedean jump space

For compact inputs, positivity of theta transfers the singular small jumps to
the translation-invariant Levy norm. Large stationary jumps require only ordinary
L2. This permits smoothing rough compact members of the complete Doob domain.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph
open WeilLevyCoshCrossover

theorem measurable_difference {v : ℝ → ℝ} (hv : Measurable v) : Measurable (difference v) :=
  (hv.comp measurable_snd).sub (hv.comp (measurable_snd.add measurable_fst))

theorem bounded_compact_memLp_volume {v : ℝ → ℝ} (hv : Measurable v)
    (hc : HasCompactSupport v) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |v x| ≤ M) : MemLp v 2 volume := by
  have hi := memLp_indicator_const (μ := (volume : Measure ℝ))
    (2 : ENNReal) hc.measurableSet M (Or.inr hc.measure_lt_top.ne)
  apply hi.mono hv.aestronglyMeasurable
  filter_upwards with x
  by_cases hx : x ∈ tsupport v
  · simpa only [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg hM] using hb x
  · have hz : v x = 0 := by
      by_contra hn
      exact hx (subset_tsupport v hn)
    simp only [hz, norm_zero, indicator_of_notMem hx, norm_zero, le_refl]

theorem compact_small_jump_theta_lower {v : ℝ → ℝ} (hc : HasCompactSupport v) :
    ∃ m : ℝ, 0 < m ∧ ∀ t x : ℝ, 0 < t → t < 1 → difference v (t, x) ≠ 0 →
      m ≤ riemannKernelReal x ∧ m ≤ riemannKernelReal (x + t) := by
  obtain ⟨L, hL⟩ := hc.isCompact.isBounded.subset_closedBall 0
  let R := |L| + 1
  have hs {x : ℝ} (hx : v x ≠ 0) : |x| ≤ R := by
    have h := hL (subset_tsupport v hx)
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at h
    rw [abs_le]
    dsimp [R]
    constructor <;> linarith [h.1, h.2, le_abs_self L]
  obtain ⟨m, hm, hmin⟩ := (isCompact_Icc : IsCompact (Icc (-(R + 1)) (R + 1))).exists_forall_le'
    continuous_riemannKernelReal.continuousOn (fun x _ => riemannKernelReal_pos x)
  refine ⟨m, hm, fun t x ht ht1 hd => ?_⟩
  have habs : |x| ≤ R + 1 ∧ |x + t| ≤ R + 1 := by
    by_cases hx : v x = 0
    · have hy : v (x + t) ≠ 0 := by
        intro hy
        exact hd (by simp [difference, left, right, hx, hy])
      have hyb := hs hy
      have hxb : |x| ≤ |x + t| + t := by
        have hh := abs_sub (x + t) t
        simpa only [add_sub_cancel_right, abs_of_pos ht] using hh
      constructor <;> linarith
    · have hxb := hs hx
      have hyb : |x + t| ≤ |x| + t := by simpa only [abs_of_pos ht] using abs_add_le x t
      constructor <;> linarith
  exact ⟨hmin x (abs_le.mp habs.1), hmin (x + t) (abs_le.mp habs.2)⟩

def levyTail : ℝ → ℝ := (Ici (1 : ℝ)).indicator archLevyDensity

theorem levyTail_nonneg (t : ℝ) : 0 ≤ levyTail t := by
  by_cases ht : 1 ≤ t
  · rw [levyTail, indicator_of_mem (show t ∈ Ici (1 : ℝ) from ht)]
    exact (archLevyDensity_pos (by linarith)).le
  · simp only [levyTail, indicator_of_notMem (show t ∉ Ici (1 : ℝ) from ht), le_refl]

theorem integrable_levyTail : Integrable levyTail := by
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  exact (integrableOn_archLevyDensity_Ioi (c := (1 : ℝ) / 2) (by norm_num)).mono_set
    (fun t ht => by change 1 ≤ t at ht; change 1 / 2 < t; linarith)

def stationaryJump (v : ℝ → ℝ) (e : ℝ × ℝ) : ℝ := archLevyDensity e.1 * difference v e ^ 2
def stationaryEnergy (v : ℝ → ℝ) : ℝ := ∫ e, stationaryJump v e ∂archBase

/-- A compact maximal-domain function has the full stationary Levy jump norm. -/
theorem integrable_stationaryJump {v : ℝ → ℝ} (hv : Measurable v) (hc : HasCompactSupport v)
    (h2 : MemLp v 2 volume) (hd : MemLp (difference v) 2 edgeMeasure) :
    Integrable (stationaryJump v) archBase := by
  obtain ⟨m, hm, hmin⟩ := compact_small_jump_theta_lower hc
  have ha : Integrable (fun e => archWeight e * difference v e ^ 2) archBase := by
    apply (integrable_weighted_iff archBase measurable_archWeight archWeight_nonneg_ae _).mp
    exact hd.integrable_sq.mono_measure
      (show archMeasure ≤ edgeMeasure from le_add_of_nonneg_right (show 0 ≤ Measure.sum primeMeasure from bot_le))
  have htail : Integrable (fun e : ℝ × ℝ => levyTail e.1 * v e.2 ^ 2) archBase :=
    integrable_levyTail.restrict.mul_prod h2.integrable_sq
  have htail' : Integrable (fun e : ℝ × ℝ => levyTail e.1 * v (e.2 + e.1) ^ 2) archBase := by
    have h := (measurePreserving_prod_add (volume.restrict (Ioi (0 : ℝ))) volume).integrable_comp_of_integrable htail
    change Integrable (fun e : ℝ × ℝ => levyTail e.1 * v (e.2 + e.1) ^ 2)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume)
    simpa only [Function.comp_def, add_comm] using h
  have hi := (ha.const_mul (1 / m ^ 2)).add ((htail.add htail').const_mul 2)
  apply hi.mono' ((measurable_archLevyDensity.comp measurable_fst).mul
    ((measurable_difference hv).pow_const 2)).aestronglyMeasurable
  have ht : ∀ᵐ e ∂archBase, e.1 ∈ Ioi (0 : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [ht, archWeight_nonneg_ae] with e he harch
  change ‖archLevyDensity e.1 * difference v e ^ 2‖ ≤
    (1 / m ^ 2) * (archWeight e * difference v e ^ 2) +
      2 * (levyTail e.1 * v e.2 ^ 2 + levyTail e.1 * v (e.2 + e.1) ^ 2)
  rw [Real.norm_of_nonneg (mul_nonneg (archLevyDensity_pos he).le (sq_nonneg _))]
  have htail0 : 0 ≤ 2 * (levyTail e.1 * v e.2 ^ 2 + levyTail e.1 * v (e.2 + e.1) ^ 2) :=
    by have h := levyTail_nonneg e.1; positivity
  by_cases ht1 : e.1 < 1
  · by_cases hd0 : difference v e = 0
    · simp only [hd0, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
      exact htail0
    · have hθ := hmin e.1 e.2 he ht1 hd0
      have hp : m ^ 2 ≤ riemannKernelReal e.2 * riemannKernelReal (e.2 + e.1) := by
        simpa only [pow_two] using mul_le_mul hθ.1 hθ.2 hm.le (riemannKernelReal_pos _).le
      have hfactor := (one_le_div (sq_pos_of_pos hm)).mpr hp
      have hmul := mul_le_mul_of_nonneg_right hfactor
        (mul_nonneg (archLevyDensity_pos he).le (sq_nonneg (difference v e)))
      have hsmall : archLevyDensity e.1 * difference v e ^ 2 ≤
          (1 / m ^ 2) * (archWeight e * difference v e ^ 2) := by
        calc
          _ = 1 * (archLevyDensity e.1 * difference v e ^ 2) := by ring
          _ ≤ (riemannKernelReal e.2 * riemannKernelReal (e.2 + e.1) / m ^ 2) *
              (archLevyDensity e.1 * difference v e ^ 2) := hmul
          _ = _ := by unfold archWeight; ring
      exact hsmall.trans (le_add_of_nonneg_right htail0)
  · have htge : 1 ≤ e.1 := le_of_not_gt ht1
    rw [levyTail, indicator_of_mem (show e.1 ∈ Ici (1 : ℝ) from htge)]
    have hdiff : difference v e ^ 2 ≤ 2 * (v e.2 ^ 2 + v (e.2 + e.1) ^ 2) := by
      dsimp [difference, left, right]
      nlinarith [sq_nonneg (v e.2 + v (e.2 + e.1))]
    have hb := mul_le_mul_of_nonneg_left hdiff (archLevyDensity_pos he).le
    have h0 : 0 ≤ (1 / m ^ 2) * (archWeight e * difference v e ^ 2) := by positivity
    nlinarith only [hb, h0]

theorem stationaryEnergy_eq_iterated {v : ℝ → ℝ} (hi : Integrable (stationaryJump v) archBase) :
    stationaryEnergy v = ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x, (v x - v (x + t)) ^ 2 := by
  rw [stationaryEnergy, archBase, integral_prod _ hi]
  simp only [stationaryJump, difference, left, right, integral_const_mul]

theorem integrable_stationary_outer {v : ℝ → ℝ} (hi : Integrable (stationaryJump v) archBase) :
    IntegrableOn (fun t => archLevyDensity t * ∫ x, (v x - v (x + t)) ^ 2) (Ioi 0) := by
  change Integrable (fun t => archLevyDensity t * ∫ x, (v x - v (x + t)) ^ 2)
    (volume.restrict (Ioi (0 : ℝ)))
  simpa only [stationaryJump, difference, left, right, integral_const_mul] using hi.integral_prod_left

end RHTower.CHMDDoobGraph
