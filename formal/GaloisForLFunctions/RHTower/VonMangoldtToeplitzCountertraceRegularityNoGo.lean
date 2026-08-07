import GaloisForLFunctions.HTGeometry.MomentToeplitzRegularityNoGo
import GaloisForLFunctions.RHTower.VonMangoldtWeightedMarginalBoundaryAnomaly
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.NumberTheory.PrimeCounting

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- Positive measure obtained by spreading each resolved von Mangoldt mass uniformly across its
successor logarithmic segment. -/
def vonMangoldtSuccessorLogSegmentMeasure : Measure ℝ :=
  Measure.sum fun m : ℕ =>
    ENNReal.ofReal (finiteVonMangoldtRealWeight (m + 2)) •
      volume.restrict (Ioc (Real.log (m + 2 : ℝ)) (Real.log (m + 3 : ℝ)))

private theorem integral_pow_vonMangoldtSuccessorLogSegmentComponent
    (q m : ℕ) :
    (∫ x : ℝ, x ^ q ∂
      (ENNReal.ofReal (finiteVonMangoldtRealWeight (m + 2)) •
        volume.restrict (Ioc (Real.log (m + 2 : ℝ)) (Real.log (m + 3 : ℝ))))) =
      vonMangoldtSuccessorRelativeMomentTerm (q + 1) (m + 2) / (q + 1 : ℝ) := by
  have hlogle : Real.log (m + 2 : ℝ) ≤ Real.log (m + 3 : ℝ) := by
    have hm2 : (0 : ℝ) < m + 2 := by positivity
    have hm3 : (0 : ℝ) < m + 3 := by positivity
    exact Real.strictMonoOn_log.monotoneOn hm2 hm3 (by norm_num)
  rw [integral_smul_measure]
  rw [ENNReal.toReal_ofReal (finiteVonMangoldtRealWeight_nonneg _)]
  rw [← intervalIntegral.integral_of_le hlogle]
  rw [integral_pow]
  unfold vonMangoldtSuccessorRelativeMomentTerm
  unfold vonMangoldtAdditiveLogJetDifference vonMangoldtAdditiveLogJet
  push_cast
  ring_nf

theorem integrable_pow_vonMangoldtSuccessorLogSegmentMeasure (q : ℕ) :
    Integrable (fun x : ℝ => x ^ q) vonMangoldtSuccessorLogSegmentMeasure := by
  rw [vonMangoldtSuccessorLogSegmentMeasure]
  apply integrable_sum_measure
  · intro m
    apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
    exact ((continuous_pow q).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  · have hs : Summable (fun m : ℕ =>
        vonMangoldtSuccessorRelativeMomentTerm (q + 1) (m + 2) / (q + 1 : ℝ)) :=
      ((summable_vonMangoldtSuccessorRelativeMomentTerm (q + 1)).comp_injective
        (fun a b h => Nat.add_right_cancel h)).div_const _
    apply hs.congr
    intro m
    rw [← integral_pow_vonMangoldtSuccessorLogSegmentComponent]
    rw [integral_smul_measure, integral_smul_measure]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg]
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 2 := by linarith
    exact pow_nonneg (le_trans (Real.log_nonneg hm1) hx.1.le) q

private instance : IsFiniteMeasure vonMangoldtSuccessorLogSegmentMeasure := by
  have h := integrable_pow_vonMangoldtSuccessorLogSegmentMeasure 0
  simp only [pow_zero] at h
  exact (integrable_const_iff.mp h).resolve_left one_ne_zero

theorem integral_pow_vonMangoldtSuccessorLogSegmentMeasure (q : ℕ) :
    (∫ x : ℝ, x ^ q ∂vonMangoldtSuccessorLogSegmentMeasure) =
      vonMangoldtSuccessorRelativeMoment (q + 1) / (q + 1 : ℝ) := by
  rw [vonMangoldtSuccessorLogSegmentMeasure,
    integral_sum_measure (integrable_pow_vonMangoldtSuccessorLogSegmentMeasure q)]
  simp_rw [integral_pow_vonMangoldtSuccessorLogSegmentComponent]
  rw [tsum_div_const]
  rfl

theorem vonMangoldtSuccessorLogSegmentMeasure_unbounded_support
    (R : ℝ) : vonMangoldtSuccessorLogSegmentMeasure {x | R ≤ x} ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp R)
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  have hexp_lt_p : Real.exp R < (p : ℝ) := hN.trans_le (by exact_mod_cast hpN)
  have hRp : R < Real.log (p : ℝ) := by
    rw [← Real.log_exp R]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact Real.strictMonoOn_log (Real.exp_pos R) hp0 hexp_lt_p
  have hp2 : 2 ≤ p := hp.two_le
  let m := p - 2
  have hmp : m + 2 = p := by dsimp [m]; omega
  let mucomp : ℕ → Measure ℝ := fun k =>
    ENNReal.ofReal (finiteVonMangoldtRealWeight (k + 2)) •
      volume.restrict (Ioc (Real.log (k + 2 : ℝ)) (Real.log (k + 3 : ℝ)))
  have hweight : 0 < finiteVonMangoldtRealWeight p := by
    rw [finiteVonMangoldtRealWeight, ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact div_pos (Real.log_pos (by exact_mod_cast hp2)) (by positivity)
  have hlogsucc : Real.log (p : ℝ) < Real.log (p + 1 : ℝ) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp10 : (0 : ℝ) < p + 1 := by positivity
    exact Real.strictMonoOn_log hp0 hp10 (by norm_num)
  have hcomponent : 0 < mucomp m (Ioc (Real.log (p : ℝ)) (Real.log (p + 1 : ℝ))) := by
    dsimp [mucomp]
    have hmp3 : m + 3 = p + 1 := by omega
    have hmpReal : (m : ℝ) + 2 = p := by exact_mod_cast hmp
    have hmp3Real : (m : ℝ) + 3 = p + 1 := by exact_mod_cast hmp3
    rw [hmp, hmpReal, hmp3Real]
    rw [Measure.restrict_apply measurableSet_Ioc, inter_self, Real.volume_Ioc]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hweight).ne'
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr hlogsucc)).ne'
  have hinterval : Ioc (Real.log (p : ℝ)) (Real.log (p + 1 : ℝ)) ⊆ {x | R ≤ x} := by
    intro x hx
    exact hRp.le.trans hx.1.le
  have hlecomp :
      mucomp m (Ioc (Real.log (p : ℝ)) (Real.log (p + 1 : ℝ))) ≤
        mucomp m {x | R ≤ x} := measure_mono hinterval
  have hlesum : mucomp m {x | R ≤ x} ≤ Measure.sum mucomp {x | R ≤ x} :=
    Measure.le_sum mucomp m _
  rw [vonMangoldtSuccessorLogSegmentMeasure]
  change Measure.sum mucomp {x | R ≤ x} ≠ 0
  exact ne_of_gt (hcomponent.trans_le (hlecomp.trans hlesum))

private theorem ae_nonneg_vonMangoldtSuccessorLogSegmentMeasure :
    ∀ᵐ x ∂vonMangoldtSuccessorLogSegmentMeasure, 0 ≤ x := by
  rw [vonMangoldtSuccessorLogSegmentMeasure]
  apply Measure.ae_sum_iff.2
  intro m
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 2 := by linarith
  exact le_trans (Real.log_nonneg hm1) hx.1.le

theorem tendsto_vonMangoldtSuccessorRelativeMoment_ratio_zero :
    Tendsto (fun q : ℕ =>
      vonMangoldtSuccessorRelativeMoment q /
        vonMangoldtSuccessorRelativeMoment (q + 1)) atTop (nhds 0) := by
  let A : ℕ → ℝ := fun q =>
    ∫ x : ℝ, (max x 0) ^ q ∂vonMangoldtSuccessorLogSegmentMeasure
  have hIntegrable (q : ℕ) :
      Integrable (fun x : ℝ => (max x 0) ^ q)
        vonMangoldtSuccessorLogSegmentMeasure :=
    (integrable_pow_vonMangoldtSuccessorLogSegmentMeasure q).congr
      (ae_nonneg_vonMangoldtSuccessorLogSegmentMeasure.mono fun x hx => by
        simp [max_eq_left hx])
  have hUnbounded (R : ℝ) :
      vonMangoldtSuccessorLogSegmentMeasure {x | R ≤ max x 0} ≠ 0 := by
    intro hzero
    apply vonMangoldtSuccessorLogSegmentMeasure_unbounded_support R
    have hsubset : {x : ℝ | R ≤ x} ⊆ {x : ℝ | R ≤ max x 0} := by
      intro x hx
      exact le_trans hx (le_max_left x 0)
    have hle := measure_mono (μ := vonMangoldtSuccessorLogSegmentMeasure) hsubset
    rw [hzero] at hle
    exact bot_unique hle
  have hescape : Tendsto (fun q : ℕ => A (q + 1) / A q) atTop atTop :=
    GaloisForLFunctions.HTGeometry.tendsto_integral_pow_succ_div_integral_pow_atTop
      (measurable_id.max measurable_const) (fun x => le_max_right x 0)
      hIntegrable hUnbounded
  have hA : Tendsto (fun q : ℕ => A q / A (q + 1)) atTop (nhds 0) := by
    simpa [Function.comp_def, inv_div] using tendsto_inv_atTop_zero.comp hescape
  rw [← tendsto_add_atTop_iff_nat 1]
  have hfactor : Tendsto (fun q : ℕ => (q + 1 : ℝ) / (q + 2 : ℝ)) atTop (nhds 1) := by
    have hzero : Tendsto (fun q : ℕ => (1 : ℝ) / (q + 2 : ℝ)) atTop (nhds 0) := by
      simpa [Function.comp_def, Nat.cast_add] using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
          (tendsto_add_atTop_nat 2)
    have heq : (fun q : ℕ => (q + 1 : ℝ) / (q + 2 : ℝ)) =
        fun q : ℕ => 1 - 1 / (q + 2 : ℝ) := by
      funext q
      field_simp
      ring
    rw [heq]
    simpa using tendsto_const_nhds.sub hzero
  have hAid (q : ℕ) : A q =
      vonMangoldtSuccessorRelativeMoment (q + 1) / (q + 1 : ℝ) := by
    dsimp [A]
    calc
      (∫ x : ℝ, max x 0 ^ q ∂vonMangoldtSuccessorLogSegmentMeasure) =
          ∫ x : ℝ, x ^ q ∂vonMangoldtSuccessorLogSegmentMeasure :=
        integral_congr_ae
          (ae_nonneg_vonMangoldtSuccessorLogSegmentMeasure.mono fun x hx => by
            simp [max_eq_left hx])
      _ = _ := integral_pow_vonMangoldtSuccessorLogSegmentMeasure q
  have hprod := hfactor.mul hA
  convert hprod using 1
  · funext q
    rw [hAid q, hAid (q + 1)]
    field_simp [ne_of_gt (vonMangoldtSuccessorRelativeMoment_pos (q + 2) (by omega))]
    push_cast
    ring
  · simp

/-- The canonical von Mangoldt counterweights required by exact finite-section cancellation are
not uniformly bounded. -/
theorem vonMangoldtHankelToeplitzCounterweight_not_bounded :
    ¬ ∃ B : ℝ, ∀ n : ℕ,
      |GaloisForLFunctions.HTGeometry.hankelToeplitzCounterweight
        vonMangoldtSuccessorRelativeMoment n| ≤ B :=
  GaloisForLFunctions.HTGeometry.hankelToeplitzCounterweight_not_bounded_of_ratio_tendsto_zero
      vonMangoldtSuccessorRelativeMoment
      vonMangoldtSuccessorRelativeMoment_pos
      tendsto_vonMangoldtSuccessorRelativeMoment_ratio_zero

/-- The source counterdensity is exactly the symmetric Toeplitz matrix generated by the canonical
counterweight sequence. -/
theorem vonMangoldtHankelToeplitzCounterDensity_eq_counterweight_offset
    (i j : ℕ) :
    vonMangoldtHankelToeplitzCounterDensity i j =
      GaloisForLFunctions.HTGeometry.hankelToeplitzCounterweight
        vonMangoldtSuccessorRelativeMoment
        (GaloisForLFunctions.HTGeometry.toeplitzOffset i j) := by
  unfold vonMangoldtHankelToeplitzCounterDensity
    GaloisForLFunctions.HTGeometry.hankelToeplitzCounterDensity
    GaloisForLFunctions.HTGeometry.toeplitzOffset
  split <;> rfl

/-- No bounded operator on `ℓ²(ℕ)` realizes the exact von Mangoldt counterdensity. -/
theorem not_hasBoundedToeplitzL2Realization_vonMangoldtCounterweight :
    ¬ GaloisForLFunctions.HTGeometry.HasBoundedToeplitzL2Realization
      (GaloisForLFunctions.HTGeometry.hankelToeplitzCounterweight
        vonMangoldtSuccessorRelativeMoment) :=
  GaloisForLFunctions.HTGeometry.not_hasBoundedToeplitzL2Realization_of_not_bounded
    vonMangoldtHankelToeplitzCounterweight_not_bounded

/-- Even an everywhere-defined linear realization from the canonical finite-support core into
`ℓ²(ℕ)` is impossible for the exact von Mangoldt counterdensity. -/
theorem not_hasFiniteCoreToeplitzL2Realization_vonMangoldtCounterweight :
    ¬ GaloisForLFunctions.HTGeometry.HasFiniteCoreToeplitzL2Realization
      (GaloisForLFunctions.HTGeometry.hankelToeplitzCounterweight
        vonMangoldtSuccessorRelativeMoment) :=
  GaloisForLFunctions.HTGeometry.not_hasFiniteCoreToeplitzL2Realization_of_not_bounded
    vonMangoldtHankelToeplitzCounterweight_not_bounded

/-- **Unconditional von Mangoldt Toeplitz countertrace regularity no-go.**  Exact opening
cancellation and the nonzero finite countertrace law coexist with unbounded canonical weights;
consequently the counterdensity has neither a bounded `ℓ²` realization nor an `ℓ²`-valued linear
realization on the canonical finite-support core. -/
theorem vonMangoldtToeplitzCountertraceRegularityNoGo :
    (¬ ∃ B : ℝ, ∀ n : ℕ,
        |GaloisForLFunctions.HTGeometry.hankelToeplitzCounterweight
          vonMangoldtSuccessorRelativeMoment n| ≤ B) ∧
      (¬ GaloisForLFunctions.HTGeometry.HasBoundedToeplitzL2Realization
        (GaloisForLFunctions.HTGeometry.hankelToeplitzCounterweight
          vonMangoldtSuccessorRelativeMoment)) ∧
      (¬ GaloisForLFunctions.HTGeometry.HasFiniteCoreToeplitzL2Realization
        (GaloisForLFunctions.HTGeometry.hankelToeplitzCounterweight
          vonMangoldtSuccessorRelativeMoment)) ∧
      (∀ n : ℕ,
        vonMangoldtHankelToeplitzCounterDensity (n + 1) (n + 1) *
              vonMangoldtSuccessorRelativeMoment (2 * (n + 1) + 2) +
            ∑ i : Fin (n + 1),
              (vonMangoldtHankelToeplitzCounterDensity (n + 1) i +
                  vonMangoldtHankelToeplitzCounterDensity i (n + 1)) *
                vonMangoldtSuccessorRelativeMoment ((n + 1) + i + 2) = 0) ∧
      (∀ N : ℕ,
        GaloisForLFunctions.HTGeometry.matrixDensityPair
            (finiteVonMangoldtJetDensity
              vonMangoldtHankelToeplitzCounterDensity (N + 1))
            (vonMangoldtSuccessorPrincipalRelativeHankel (N + 1)) =
          vonMangoldtSuccessorRelativeMoment 2) := by
  exact ⟨vonMangoldtHankelToeplitzCounterweight_not_bounded,
    not_hasBoundedToeplitzL2Realization_vonMangoldtCounterweight,
    not_hasFiniteCoreToeplitzL2Realization_vonMangoldtCounterweight,
    vonMangoldtHankelToeplitzCounterDensity_opening_cancellation,
    vonMangoldtHankelToeplitzCounterDensity_pair_constant⟩

end

end RHTower
