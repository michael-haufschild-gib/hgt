import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Termwise bounds for an interval integral of a series

A series of real functions whose termwise absolute masses are summable may be integrated term by
term over an interval, so a summable family of termwise cell bounds bounds the cell integral of the
sum.  This is the step that turns the per-term cancellation estimates of an approximate functional
equation into a bound on the cell integral of the function itself.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- **Termwise cell bound.**  If each term is integrable on the cell, the termwise absolute masses
are summable, and each term's cell integral is bounded by a summable `B`, then the cell integral of
the sum is bounded by `∑ B`. -/
theorem abs_intervalIntegral_tsum_le {F : ℕ → ℝ → ℝ} {B : ℕ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (hint : ∀ n, IntegrableOn (F n) (Ioc u v) volume)
    (hnorm : Summable (fun n => ∫ τ in Ioc u v, |F n τ|))
    (hbound : ∀ n, |∫ τ in u..v, F n τ| ≤ B n) (hB : Summable B) :
    |∫ τ in u..v, ∑' n : ℕ, F n τ| ≤ ∑' n : ℕ, B n := by
  have hnorm' : Summable (fun n => ∫ τ in Ioc u v, ‖F n τ‖) := by
    refine hnorm.congr fun n => ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun τ => (Real.norm_eq_abs _).symm)
  have hsum := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Ioc u v)) hint hnorm'
  have hcell : ∀ n : ℕ, (∫ τ in Ioc u v, F n τ) = ∫ τ in u..v, F n τ := fun n =>
    (intervalIntegral.integral_of_le huv).symm
  have htotal : (∫ τ in Ioc u v, ∑' n : ℕ, F n τ) = ∫ τ in u..v, ∑' n : ℕ, F n τ :=
    (intervalIntegral.integral_of_le huv).symm
  have hsum' : HasSum (fun n : ℕ => ∫ τ in u..v, F n τ) (∫ τ in u..v, ∑' n : ℕ, F n τ) := by
    have := hsum
    rw [htotal] at this
    refine this.congr_fun fun n => ?_
    exact (hcell n).symm
  have hsummable : Summable (fun n : ℕ => ∫ τ in u..v, F n τ) := hsum'.summable
  have habs : Summable (fun n : ℕ => |∫ τ in u..v, F n τ|) := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hbound hB
  calc |∫ τ in u..v, ∑' n : ℕ, F n τ|
      = |∑' n : ℕ, ∫ τ in u..v, F n τ| := by rw [hsum'.tsum_eq]
    _ ≤ ∑' n : ℕ, |∫ τ in u..v, F n τ| := by
        simpa [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (f := fun n : ℕ => ∫ τ in u..v, F n τ)
            (by simpa [Real.norm_eq_abs] using habs)
    _ ≤ ∑' n : ℕ, B n := Summable.tsum_le_tsum hbound habs hB

end GaloisForLFunctions.HTGeometry
