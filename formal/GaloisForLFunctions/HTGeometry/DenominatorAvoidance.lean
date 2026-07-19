import GaloisForLFunctions.HTGeometry.DenominatorUniform
import GaloisForLFunctions.HTGeometry.NevDenominatorFactor
import GaloisForLFunctions.HTGeometry.QuasiTightness

/-!
# The truncated denominator eventually avoids a compact set

On a compact set where the limiting denominator does not vanish it is bounded away from zero, and
uniform convergence then keeps the truncated denominator away from zero there as well.

Stated for the denominator rather than for the nodes, so that it is independent of which family
describes the zeros at a given level.
-/

open scoped BigOperators
open Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- A compact set of reals is contained in a symmetric open interval. -/
theorem exists_radius_of_isCompact {K : Set ℝ} (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ K, |x| < r := by
  obtain ⟨x₁, hx₁K, hmax⟩ := hK.exists_isMaxOn hKne continuous_abs.continuousOn
  refine ⟨|x₁| + 1, by positivity, fun x hx => ?_⟩
  have hle := hmax hx
  simp only [Set.mem_setOf_eq] at hle
  linarith

/-- **The truncated denominator eventually has no zero on a compact set avoiding the limit's
zeros.** -/
theorem eventually_no_denominator_zero_on_compact (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (tau : ℝ) {K : Set ℝ} (hK : IsCompact K)
    (hKF : ∀ x ∈ K, nevBrealInf s x * tau - nevDrealInf s x ≠ 0) :
    ∀ᶠ n in atTop, ∀ x ∈ K, nevBreal s n x * tau - nevDreal s n x ≠ 0 := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact Filter.Eventually.of_forall fun n x hx => absurd hx (Set.notMem_empty x)
  have hcont : Continuous fun x : ℝ => |nevBrealInf s x * tau - nevDrealInf s x| :=
    (((continuous_nevBrealInf h h0b).mul continuous_const).sub
      (continuous_nevDrealInf h h0b)).abs
  obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
  set δ : ℝ := |nevBrealInf s x₀ * tau - nevDrealInf s x₀| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (hKF x₀ hx₀K)
  obtain ⟨r, hr, hKr⟩ := exists_radius_of_isCompact hK hKne
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  filter_upwards [eventually_nevDenominator_close h hS hP tau hr (half_pos hδ)] with n hn x hx
  intro hzero
  have h1 := hn x (hKr x hx)
  rw [hzero, zero_sub, abs_neg] at h1
  have h2 : δ ≤ |nevBrealInf s x * tau - nevDrealInf s x| := hmin hx
  linarith

/-- **No level-`n` node lies in the compact set, eventually.**  The zeros of the truncated
denominator are the quasi-orthogonal nodes whenever the leading coefficient survives. -/
theorem eventually_quasiNodes_disjoint (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (tau : ℝ) {K : Set ℝ} (hK : IsCompact K)
    (hKF : ∀ x ∈ K, nevBrealInf s x * tau - nevDrealInf s x ≠ 0) :
    ∀ᶠ n in atTop, nevAlpha s n tau ≠ 0 → ∀ x ∈ K,
      x ∉ quasiNodes s n (nevBeta s n tau / nevAlpha s n tau) := by
  filter_upwards [eventually_no_denominator_zero_on_compact h h0b tau hK hKF] with n hn hα x hx
  intro hmem
  exact hn x hx ((nevDenominator_zero_iff h n hα x).mpr hmem)

/-- **The quasi measure eventually gives the compact set zero mass.** -/
theorem eventually_quasiMeasure_compact_eq_zero (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (tau : ℝ) {K : Set ℝ} (hK : IsCompact K)
    (hKF : ∀ x ∈ K, nevBrealInf s x * tau - nevDrealInf s x ≠ 0) :
    ∀ᶠ n in atTop, nevAlpha s n tau ≠ 0 →
      quasiMeasure s n (nevBeta s n tau / nevAlpha s n tau) K = 0 := by
  classical
  filter_upwards [eventually_quasiNodes_disjoint h h0b tau hK hKF] with n hn hα
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  rw [quasiMeasure, finsetWeightedDirac_apply _ _ hKm]
  refine Finset.sum_eq_zero fun ξ hξ => ?_
  have hnot : ξ ∉ K := fun hc => hn hα ξ hc hξ
  rw [Set.indicator_of_notMem hnot, mul_zero]

end HTGeometry
