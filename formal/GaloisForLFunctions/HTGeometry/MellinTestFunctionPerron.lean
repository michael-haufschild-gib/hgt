import GaloisForLFunctions.HTGeometry.MellinPlancherelBound
import GaloisForLFunctions.HTGeometry.SmoothedPerronContourShift

/-!
# Perron's formula for smooth test functions supported away from `0`

Let `f : ℝ → ℂ` be smooth with support in `[a, b]`, `0 < a ≤ b` (`IsTest f a b`).

* `𝓜f` is entire, `s 𝓜f(s) = −𝓜[u f'](s)` (`mellin_mul_deriv_eq`), hence
  `|s|² |𝓜f(s)| ≤ ∫_a^b |u (u f')'| u^{σ−1} du` and `𝓜f` is integrable on vertical lines.
* **Perron.**  For `|c| ≤ 1`, `c(0) = 0`, `σ > 1`, `X > 0`:
  `(1/2πi) ∫_{(σ)} L(c, s) 𝓜f(s) X^s ds = Σ_n c(n) f(n/X)` (`verticalIntegral'_eq_tsum`).
-/

open Real Complex Set MeasureTheory Function Filter Topology
open scoped ContDiff Interval

noncomputable section

namespace GaloisForLFunctions.HTGeometry.TestFunctionPerron

/-- A smooth test function supported in `[a, b]`, `0 < a ≤ b`. -/
structure IsTest (f : ℝ → ℂ) (a b : ℝ) : Prop where
  pos : 0 < a
  le : a ≤ b
  smooth : ContDiff ℝ ∞ f
  supp : support f ⊆ Icc a b

namespace IsTest

variable {f : ℝ → ℂ} {a b : ℝ} (hf : IsTest f a b)
include hf

theorem eq_zero {u : ℝ} (hu : u ∉ Icc a b) : f u = 0 := by
  by_contra h; exact hu (hf.supp h)

theorem continuous : Continuous f := hf.smooth.continuous

theorem eq_zero_of_le {u : ℝ} (hu : u ≤ a) : f u = 0 := by
  rcases hu.lt_or_eq with h | h
  · exact hf.eq_zero fun h' => absurd h'.1 (not_le.mpr h)
  · -- `f = 0` left of `a`, so `f(a) = 0` by continuity
    have hlim : Tendsto f (𝓝[<] u) (𝓝 (f u)) := hf.continuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have hzero : ∀ᶠ v in 𝓝[<] u, f v = 0 := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      have hv' : v < a := by rw [← h]; exact hv
      exact hf.eq_zero fun h' => absurd h'.1 (not_le.mpr hv')
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun v hv => hv.symm))

theorem eq_zero_of_ge {u : ℝ} (hu : b ≤ u) : f u = 0 := by
  rcases hu.lt_or_eq with h | h
  · exact hf.eq_zero fun h' => absurd h'.2 (not_le.mpr h)
  · have hlim : Tendsto f (𝓝[>] u) (𝓝 (f u)) := hf.continuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have hzero : ∀ᶠ v in 𝓝[>] u, f v = 0 := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      have hv' : b < v := by rw [h]; exact hv
      exact hf.eq_zero fun h' => absurd h'.2 (not_le.mpr hv')
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun v hv => hv.symm))

/-- The Mellin transform is an integral over `[a, b]`. -/
theorem mellin_eq (s : ℂ) :
    mellin f s = ∫ u in a..b, (u : ℂ) ^ (s - 1) * f u := by
  rw [mellin, intervalIntegral.integral_of_le hf.le]
  simp_rw [smul_eq_mul]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi ?_ ?_
  · intro u hu; exact lt_trans hf.pos hu.1
  · intro u hu
    have : f u = 0 := by
      by_cases h1 : u ≤ a
      · exact hf.eq_zero_of_le h1
      · push Not at h1
        exact hf.eq_zero_of_ge (by
          by_contra h2; push Not at h2; exact hu.2 ⟨h1, h2.le⟩)
    simp [this]

end IsTest

end GaloisForLFunctions.HTGeometry.TestFunctionPerron
