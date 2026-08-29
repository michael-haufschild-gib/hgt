import GaloisForLFunctions.HTGeometry.TotallyRamifiedOrder
import GaloisForLFunctions.HTGeometry.LogDerivProximityBound

/-!
# Radii whose circle carries no zero

The Poisson–Jensen bound is available only at radii whose circle misses the divisor.  For an entire
function whose order is finite at every point the zeros form a countable set — each closed ball meets
them in a finite set, because the divisor has finite support on compacts — so the moduli of zeros are
countable and every nondegenerate interval of radii contains a good one.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set MeasureTheory

/-- The zero set of an entire function of finite order at every point is countable. -/
theorem countable_zeroSet {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : ∀ z, meromorphicOrderAt f z ≠ ⊤) : {z : ℂ | f z = 0}.Countable := by
  classical
  have hcover : {z : ℂ | f z = 0} ⊆ ⋃ n : ℕ, {z : ℂ | f z = 0} ∩ closedBall (0 : ℂ) (n : ℝ) := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
    exact mem_iUnion.mpr ⟨n, hz, by rwa [mem_closedBall, dist_zero_right]⟩
  refine Set.Countable.mono hcover (Set.countable_iUnion fun n => ?_)
  have habs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
  have hfin : (Function.support
      fun u => MeromorphicOn.divisor f (closedBall (0 : ℂ) |(n : ℝ)|) u).Finite :=
    (MeromorphicOn.divisor f (closedBall (0 : ℂ) |(n : ℝ)|)).finiteSupport
      (isCompact_closedBall (0 : ℂ) |(n : ℝ)|)
  refine Set.Countable.mono ?_ hfin.countable
  intro z hz
  obtain ⟨hz0, hzball⟩ := hz
  rw [Function.mem_support]
  intro hzero
  refine (ne_zero_of_divisor_eq_zero hf hf0 (U := closedBall (0 : ℂ) |(n : ℝ)|)
    (fun w _ => (hf.analyticAt w).meromorphicAt) ?_ hzero) hz0
  rw [habs]
  exact hzball

/-- **A radius whose circle carries no zero.**  Every nondegenerate interval of radii contains one,
because the moduli of the zeros are countable. -/
theorem exists_radius_no_zero_on_sphere {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : ∀ z, meromorphicOrderAt f z ≠ ⊤) {a b : ℝ} (hab : a < b) :
    ∃ R ∈ Set.Ioo a b, ∀ u : ℂ, ‖u‖ = R → f u ≠ 0 := by
  classical
  have hcount : (norm '' {z : ℂ | f z = 0}).Countable := (countable_zeroSet hf hf0).image _
  have huncount : ¬ (Set.Ioo a b).Countable := by
    intro hc
    have h0 := hc.measure_zero (volume : Measure ℝ)
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
    linarith
  have hne : ¬ (Set.Ioo a b ⊆ norm '' {z : ℂ | f z = 0}) := by
    intro hsub
    exact huncount (hcount.mono hsub)
  rw [Set.not_subset] at hne
  obtain ⟨R, hRmem, hRnot⟩ := hne
  refine ⟨R, hRmem, fun u hu hfu => hRnot ⟨u, hfu, hu⟩⟩


/-- At a point where an entire function does not vanish, its divisor vanishes. -/
theorem divisor_eq_zero_of_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : ∀ z, meromorphicOrderAt f z ≠ ⊤) {U : Set ℂ} {u : ℂ} (hu : u ∈ U) (hne : f u ≠ 0) :
    MeromorphicOn.divisor f U u = 0 := by
  have hana : ∀ z : ℂ, AnalyticAt ℂ f z := fun z => hf.analyticAt z
  rw [divisor_eq_analyticOrder_toNat hana hf0 hu]
  have h0 : analyticOrderAt f u = 0 := (AnalyticAt.analyticOrderAt_eq_zero (hana u)).mpr hne
  rw [h0]
  rfl

/-- **The Poisson–Jensen boundary hypothesis at a zero-free radius.** -/
theorem divisor_eq_zero_on_sphere {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : ∀ z, meromorphicOrderAt f z ≠ ⊤) {R : ℝ} (hR : 0 < R)
    (hRzero : ∀ u : ℂ, ‖u‖ = R → f u ≠ 0) :
    ∀ u ∈ sphere (0 : ℂ) |R|, MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u = 0 := by
  intro u hu
  rw [mem_sphere_iff_norm, sub_zero, abs_of_pos hR] at hu
  refine divisor_eq_zero_of_ne_zero hf hf0 ?_ (hRzero u hu)
  rw [mem_closedBall, dist_zero_right, abs_of_pos hR, hu]

end GaloisForLFunctions.HTGeometry
