import GaloisForLFunctions.RHTower.Deninger.DeningerLocallyConstantApproximation
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The locally constant test space is dense in `L²`

A square integrable function is approximated in `L²` by a continuous function with compact
support, and such a function is approximated uniformly by a locally constant test function whose
error is supported in a fixed compact open set of finite measure.  A uniform bound on a set of
finite measure is an `L²` bound, so the test space is dense in `L²`.

Together with the injectivity of the embedding this is the test/Hilbert half of a Gelfand scale,
and by the dual injection principle it makes the dual of `L²` inject into the dual of the test
space.

* `deningerELpNorm_le_of_bound` : a uniform bound on a set of finite measure is an `L²` bound.
* `deningerTestToL2_denseRange` : **the test space is dense in `L²`.**
-/

namespace RHTower

open MeasureTheory

section Bound

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] (μ : Measure Y)

omit [TopologicalSpace Y] in
/-- **A function bounded by `δ` and supported in `S` has `L²` norm at most `δ (μ S)^{1/2}`.** -/
theorem deningerELpNorm_le_of_bound {φ : Y → ℝ} {S : Set Y} (hS : MeasurableSet S) {δ : ℝ}
    (hδ : 0 ≤ δ) (hbound : ∀ y, |φ y| ≤ δ) (hsupp : Function.support φ ⊆ S) :
    eLpNorm φ 2 μ ≤ ENNReal.ofReal δ * μ S ^ (1 / (2 : ℝ)) := by
  have hmono : eLpNorm φ 2 μ ≤ eLpNorm (S.indicator fun _ => δ) 2 μ := by
    refine eLpNorm_mono fun y => ?_
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy]
      simpa [Real.norm_eq_abs, abs_of_nonneg hδ] using hbound y
    · have hzero : φ y = 0 := by
        by_contra hne
        exact hy (hsupp hne)
      simp [hzero, Set.indicator_of_notMem hy]
  refine hmono.trans (le_of_eq ?_)
  rw [eLpNorm_indicator_const hS (by norm_num) (by norm_num)]
  congr 1
  rw [Real.enorm_eq_ofReal hδ]

end Bound

section Dense

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
variable [TotallyDisconnectedSpace Y] [SecondCountableTopology Y]
variable [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [μ.Regular]

/-- **The locally constant test space is dense in `L²`.** -/
theorem deningerTestToL2_denseRange : DenseRange (deningerTestToL2 μ) := by
  refine Metric.denseRange_iff.mpr fun F ε hε => ?_
  obtain ⟨g, hgcs, hgle, hgcont, hgmem⟩ :=
    (Lp.memLp F).exists_hasCompactSupport_eLpNorm_sub_le (μ := μ) (p := 2) (by norm_num)
      (ε := ENNReal.ofReal (ε / 3)) (by simp [hε])
  obtain ⟨S, hS, hgS, happrox⟩ := deningerExists_locallyConstant_approx hgcont hgcs
  have hSmeas : MeasurableSet S := hS.1.measurableSet
  have hSfin : μ S ≠ ⊤ := hS.2.measure_lt_top.ne
  have hMfin : μ S ^ (1 / (2 : ℝ)) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hSfin
  set M : ℝ := (μ S ^ (1 / (2 : ℝ))).toReal with hMdef
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  set δ : ℝ := ε / (3 * (M + 1)) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    positivity
  obtain ⟨h, hhmem, hhS, hhbound⟩ := happrox δ hδ
  set G : Lp ℝ 2 μ := hgmem.toLp g with hGdef
  set H : Lp ℝ 2 μ := deningerTestToL2 μ ⟨h, hhmem⟩ with hHdef
  have h1 : ‖F - G‖ ≤ ε / 3 := by
    rw [Lp.norm_def]
    refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) hgle
    filter_upwards [Lp.coeFn_sub F G, hgmem.coeFn_toLp] with y hy hy2
    rw [hy, Pi.sub_apply, Pi.sub_apply, hy2]
  have h2 : ‖G - H‖ ≤ ε / 3 := by
    rw [Lp.norm_def]
    refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
    have hcong : eLpNorm ((G - H : Lp ℝ 2 μ) : Y → ℝ) 2 μ = eLpNorm (g - h) 2 μ := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub G H, hgmem.coeFn_toLp,
        deningerTestToL2_coeFn μ ⟨h, hhmem⟩] with y hy hy2 hy3
      rw [hy, Pi.sub_apply, Pi.sub_apply, hy2, hy3]
    rw [hcong]
    have hbound : ∀ y, |(g - h) y| ≤ δ := by
      intro y
      simpa using hhbound y
    have hsupp : Function.support (g - h) ⊆ S := by
      intro y hy
      by_contra hyS
      have hgy : g y = 0 := by
        by_contra hne
        exact hyS (hgS hne)
      have hhy : h y = 0 := by
        by_contra hne
        exact hyS (hhS hne)
      exact hy (by simp [hgy, hhy])
    refine (deningerELpNorm_le_of_bound μ hSmeas hδ.le hbound hsupp).trans ?_
    have hMeq : μ S ^ (1 / (2 : ℝ)) = ENNReal.ofReal M := (ENNReal.ofReal_toReal hMfin).symm
    rw [hMeq, ← ENNReal.ofReal_mul hδ.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hδdef, div_mul_eq_mul_div]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨⟨h, hhmem⟩, ?_⟩
  calc dist F H ≤ dist F G + dist G H := dist_triangle _ _ _
    _ = ‖F - G‖ + ‖G - H‖ := by rw [dist_eq_norm, dist_eq_norm]
    _ ≤ ε / 3 + ε / 3 := add_le_add h1 h2
    _ < ε := by linarith

/-- **The dual of `L²` injects into the dual of the test space.**  The embedding of the test space
has dense range, so a continuous functional on `L²` is determined by its restriction. -/
theorem deningerTestScale_dual_injective {φ ψ : Lp ℝ 2 μ →ₗ[ℝ] ℝ} (hφ : Continuous φ)
    (hψ : Continuous ψ)
    (h : φ.comp (deningerTestToL2 μ) = ψ.comp (deningerTestToL2 μ)) : φ = ψ :=
  deningerDual_injective_of_denseRange (deningerTestToL2_denseRange μ) hφ hψ h

/-- **The test/Hilbert scale**: the test space embeds into `L²` injectively, continuously and
densely, and the transpose of the embedding is injective. -/
theorem deningerTestScale [μ.IsOpenPosMeasure] :
    Function.Injective (deningerTestToL2 μ) ∧ DenseRange (deningerTestToL2 μ) ∧
      ∃ p : Seminorm ℝ (DeningerTestSpace Y), ∀ g, ‖deningerTestToL2 μ g‖ ≤ 1 * p g :=
  ⟨deningerTestToL2_injective μ, deningerTestToL2_denseRange μ, deningerTestToL2_bounded μ⟩

end Dense

end RHTower
