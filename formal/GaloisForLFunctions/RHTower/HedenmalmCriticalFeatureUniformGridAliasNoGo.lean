import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureBoundaryAliasPositiveSaving
import GaloisForLFunctions.HTGeometry.IntervalRiemannSum

/-!
# Uniform-grid alias no-go for HCF

The HCF boundary alias has exact mean zero on every height cell.  Therefore a positive packet
whose phases form an increasingly fine uniform grid has normalized alias tending to zero.  A
source estimate based only on positivity and total packet mass can consequently never yield the
positive variance scale needed by the HCF density receiver; it must use arithmetic
anti-equidistribution of the actual packet.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped BigOperators Interval

namespace RHTower

noncomputable section

/-- The normalized HCF alias of an equal-weight uniform phase packet in one height cell. -/
def criticalFeatureUniformGridAlias (N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N,
    (1 / (N : ℝ)) •
      ((criticalFeatureRealBoundaryPeriodization
        (uniformNode 0 1 N i) - 2 * Real.pi : ℝ) : ℂ)

/-- **Uniform-grid alias no-go.** Equal-weight positive packets can make the full HCF
nonzero-mode alias arbitrarily small.  Hence positivity plus total mass cannot produce the
height-local variance lower bound needed for an HCF source ceiling. -/
theorem tendsto_criticalFeatureUniformGridAlias :
    Tendsto criticalFeatureUniformGridAlias atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  let h : ℝ → ℂ := fun x =>
    ((criticalFeatureRealBoundaryPeriodization x - 2 * Real.pi : ℝ) : ℂ)
  have hcont : Continuous h := by
    exact Complex.continuous_ofReal.comp
      (continuous_criticalFeatureRealBoundaryPeriodization.sub continuous_const)
  have huniform : UniformContinuousOn h (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont.continuousOn
  obtain ⟨delta, hdelta, hdeltaSpec⟩ :=
    (Metric.uniformContinuousOn_iff.mp huniform) (eps / 2) (half_pos heps)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / delta)
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 0 < n := lt_of_lt_of_le (by omega : 0 < max N 1) hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hdeltaN : 1 / (n : ℝ) < delta := by
    rw [div_lt_iff₀ hnR]
    have hNN : (N : ℝ) ≤ n := by exact_mod_cast hnN
    have hN' : 1 < delta * N := by
      have := (div_lt_iff₀ hdelta).mp hN
      nlinarith
    nlinarith
  have hint : ∀ i < n, IntervalIntegrable h volume
      (uniformNode 0 1 n i) (uniformNode 0 1 n (i + 1)) := by
    intro i hi
    exact hcont.intervalIntegrable _ _
  have hmod : ∀ i < n, ∀ x ∈ Set.uIoc
      (uniformNode 0 1 n i) (uniformNode 0 1 n (i + 1)),
      ‖h x - h (uniformNode 0 1 n i)‖ ≤ eps / 2 := by
    intro i hi x hx
    have hstep : uniformNode 0 1 n (i + 1) - uniformNode 0 1 n i =
        1 / (n : ℝ) := by
      simpa using (uniformNode_succ_sub (a := (0 : ℝ)) (b := 1) hn1 i)
    have hstepNonneg : 0 ≤ uniformNode 0 1 n (i + 1) - uniformNode 0 1 n i :=
      by rw [hstep]; positivity
    rw [Set.uIoc_of_le (sub_nonneg.mp hstepNonneg)] at hx
    have hnode : uniformNode 0 1 n i ∈ Icc (0 : ℝ) 1 :=
      uniformNode_mem_Icc (by norm_num) hn1 (le_of_lt hi)
    have hnext : uniformNode 0 1 n (i + 1) ∈ Icc (0 : ℝ) 1 :=
      uniformNode_mem_Icc (by norm_num) hn1 (Nat.succ_le_iff.mpr hi)
    have hxIcc : x ∈ Icc (0 : ℝ) 1 :=
      ⟨hnode.1.trans hx.1.le, hx.2.trans hnext.2⟩
    have hdist : dist x (uniformNode 0 1 n i) < delta := by
      rw [Real.dist_eq, abs_of_pos (by linarith [hx.1])]
      calc
        x - uniformNode 0 1 n i ≤
            uniformNode 0 1 n (i + 1) - uniformNode 0 1 n i :=
          sub_le_sub_right hx.2 _
        _ = 1 / (n : ℝ) := hstep
        _ < delta := hdeltaN
    have hosc := hdeltaSpec x hxIcc (uniformNode 0 1 n i) hnode hdist
    rw [Complex.dist_eq] at hosc
    exact hosc.le
  have hriem := norm_intervalIntegral_sub_uniformRiemannSum_le
    (h := h) (by norm_num : (0 : ℝ) ≤ 1) hn1 hint (le_of_lt (half_pos heps)) hmod
  have hintReal : (∫ x in (0 : ℝ)..1,
      (criticalFeatureRealBoundaryPeriodization x - 2 * Real.pi)) = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simpa using integral_Ioc_criticalFeatureRealBoundaryPeriodization_add_sub_two_pi_eq_zero 0
  have hintZero : (∫ x in (0 : ℝ)..1, h x) = 0 := by
    have hrealCont : Continuous fun x : ℝ =>
        criticalFeatureRealBoundaryPeriodization x - 2 * Real.pi :=
      continuous_criticalFeatureRealBoundaryPeriodization.sub continuous_const
    change (∫ x in (0 : ℝ)..1,
      Complex.ofReal (criticalFeatureRealBoundaryPeriodization x - 2 * Real.pi)) = 0
    calc
      (∫ x in (0 : ℝ)..1,
        Complex.ofReal (criticalFeatureRealBoundaryPeriodization x - 2 * Real.pi)) =
          Complex.ofReal (∫ x in (0 : ℝ)..1,
            criticalFeatureRealBoundaryPeriodization x - 2 * Real.pi) :=
        Complex.ofRealCLM.intervalIntegral_comp_comm
          (hrealCont.intervalIntegrable (0 : ℝ) 1)
      _ = 0 := by rw [hintReal]; rfl
  rw [hintZero] at hriem
  have hsum : (∑ i ∈ Finset.range n,
      ((1 - 0) / (n : ℝ)) • h (uniformNode 0 1 n i)) =
        criticalFeatureUniformGridAlias n := by
    simp only [criticalFeatureUniformGridAlias, h]
    norm_num
  rw [hsum] at hriem
  have hbound : ‖criticalFeatureUniformGridAlias n‖ ≤ eps / 2 := by
    simpa using hriem
  rw [dist_zero_right]
  exact hbound.trans_lt (half_lt_self heps)

end

end RHTower
