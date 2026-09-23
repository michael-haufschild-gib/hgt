import GaloisForLFunctions.RHTower.SuzukiMovableAnchorImpedance
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

/-!
# The source-measurable calibration of the defect base

The impedance runs continuously and strictly downward from its zero-anchor value to `1`, so any
target strictly between them is attained at exactly one anchor scale.  That is the whole existence
and uniqueness content of the calibration.

The lower bound for the zero-anchor impedance is a truncation argument: each bounded truncation of
the weight is a bounded continuous test function, so its integrals converge, and the truncations
increase to the weight itself.  Hence the limit inferior of the zero-anchor impedances is at least
the target constant, with no continuity of the unbounded weight required.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The weight comparison down to the zero anchor -/

/-- The weight strictly decreases in the anchor scale, including from the zero anchor, away from
the edge point. -/
theorem movableWeight_strictAnti_of_pos {c₁ c₂ u : ℝ} (hu : 0 < u) (h1 : 0 ≤ c₁) (h12 : c₁ < c₂) :
    movableWeight c₂ u < movableWeight c₁ u := by
  have hd1 : (0 : ℝ) < u + c₁ ^ (2 : ℕ) := by positivity
  have hd2 : (0 : ℝ) < u + c₂ ^ (2 : ℕ) := by nlinarith
  have hnum : (0 : ℝ) < u + 1 := by linarith
  have hsq : c₁ ^ (2 : ℕ) < c₂ ^ (2 : ℕ) := by nlinarith
  rw [movableWeight, movableWeight, div_lt_div_iff₀ hd2 hd1]
  nlinarith [hsq, hnum]

/-! ## `(182)`: the calibrated anchor exists and is unique -/

/-- **`(182)`: a target strictly between the zero-anchor and fixed-anchor impedances is attained at
exactly one anchor scale.** -/
theorem existsUnique_impedanceRoot {Z : ℝ → ℝ} {D B : ℝ}
    (hcont : ContinuousOn Z (Set.Icc 0 1)) (hanti : StrictAntiOn Z (Set.Icc 0 1))
    (h0 : Z 0 = D) (h1 : Z 1 = 1) (hB1 : 1 < B) (hBD : B < D) :
    ∃! c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧ Z c = B := by
  have hmem : B ∈ Set.Icc (Z 1) (Z 0) := by
    rw [h0, h1]
    exact ⟨hB1.le, hBD.le⟩
  obtain ⟨c, hc, hcB⟩ :=
    intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, h0] at hcB
    exact absurd hcB (by linarith)
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, h1] at hcB
    exact absurd hcB (by linarith)
  refine ⟨c, ⟨⟨lt_of_le_of_ne hc.1 (Ne.symm hc0), lt_of_le_of_ne hc.2 hc1⟩, hcB⟩, ?_⟩
  rintro d ⟨hd, hdB⟩
  exact hanti.injOn ⟨hd.1.le, hd.2.le⟩ hc (by rw [hdB, hcB])

/-! ## `(185)`: the truncation lower bound -/

/-- Bounded truncations of an integrable nonnegative weight have converging integrals. -/
theorem tendsto_integral_truncation {μ : Measure ℝ} {w : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable w μ) (hw : 0 ≤ᵐ[μ] w) (hint : Integrable w μ) :
    Tendsto (fun M : ℕ => ∫ u, min (w u) (M : ℝ) ∂μ) atTop (𝓝 (∫ u, w u ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence w
    (fun M => (hmeas.aemeasurable.min aemeasurable_const).aestronglyMeasurable) hint ?_ ?_
  · intro M
    filter_upwards [hw] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hu (by positivity))]
    exact min_le_left _ _
  · filter_upwards [hw] with u hu
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈w u⌉₊) ?_
    intro M hM
    refine min_eq_left ?_
    calc w u ≤ (⌈w u⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (M : ℝ) := by exact_mod_cast hM

/-- **`(185)`: a converging family of lower bounds forces the same lower bound eventually.** -/
theorem eventually_ge_of_truncated_limit {Dn Sn : ℕ → ℝ} {L ε : ℝ} (hε : 0 < ε)
    (hSD : ∀ n, Sn n ≤ Dn n) (hS : Tendsto Sn atTop (𝓝 L)) :
    ∀ᶠ n in atTop, L - ε ≤ Dn n := by
  have h := (Metric.tendsto_nhds.mp hS) ε hε
  filter_upwards [h] with n hn
  have : |Sn n - L| < ε := by rwa [Real.dist_eq] at hn
  have hlow : L - ε < Sn n := by
    have := (abs_lt.mp this).1
    linarith
  linarith [hSD n]

/-- **The contradiction that forces coalescence**: a positive limiting anchor scale would make the
calibrated impedance strictly smaller than the target. -/
theorem impedance_lt_of_pos_limit {μ : Measure ℝ} [IsProbabilityMeasure μ] {c : ℝ}
    (hsupp : ∀ᵐ u ∂μ, 0 < u) (hc : 0 < c)
    (hint : Integrable (movableWeight 0) μ) :
    impedance μ c < impedance μ 0 := by
  have hsupp' : ∀ᵐ u ∂μ, 0 ≤ u := by
    filter_upwards [hsupp] with u hu using hu.le
  have hmono : ∀ᵐ u ∂μ, movableWeight c u < movableWeight 0 u := by
    filter_upwards [hsupp] with u hu
    exact movableWeight_strictAnti_of_pos hu le_rfl hc
  have hint₂ : Integrable (movableWeight c) μ := by
    refine hint.mono' ?_ ?_
    · have hm : Measurable (movableWeight c) := by
        unfold movableWeight
        fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [hsupp, hmono] with u hu hlt
      have hpos := movableWeight_pos hu.le (ne_of_gt hc)
      rw [Real.norm_eq_abs, abs_of_pos hpos]
      linarith
  have hdiff : Integrable (fun u => movableWeight 0 u - movableWeight c u) μ := hint.sub hint₂
  have hnn : 0 ≤ᵐ[μ] fun u => movableWeight 0 u - movableWeight c u := by
    filter_upwards [hmono] with u hlt
    simp only [Pi.zero_apply, sub_nonneg]
    exact hlt.le
  have hpos : 0 < ∫ u, (movableWeight 0 u - movableWeight c u) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hdiff]
    by_contra hcon
    rw [not_lt] at hcon
    have hzero : μ (Function.support fun u => movableWeight 0 u - movableWeight c u) = 0 :=
      le_antisymm hcon zero_le
    have hae : ∀ᵐ u ∂μ, movableWeight 0 u - movableWeight c u = 0 := by
      rw [ae_iff]
      simpa [Function.support, Function.mem_support] using hzero
    have hfalse : ∀ᵐ u ∂μ, False := by
      filter_upwards [hae, hmono] with u h1 h2
      exact absurd h1 (by linarith)
    have hμ : μ = 0 := by simpa using hfalse
    exact absurd hμ (IsProbabilityMeasure.ne_zero μ)
  rw [integral_sub hint hint₂] at hpos
  rw [impedance, impedance]
  linarith

end GaloisForLFunctions.RHTower
