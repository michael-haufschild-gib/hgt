import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exchanging a sum with an interval integral

The equation satisfied by the sum of the clock iterates is obtained from the recursion by summing,
which requires the sum to pass through the two integrations. For a series of continuous functions
with summable uniform bounds on a bounded interval this is dominated convergence, in the packaged
form mathlib provides for sums.

Interval integrals differ from set integrals by a sign, the same on both sides, so the exchange
transfers to them unchanged.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory

open scoped Interval

/-- **A uniformly summable series of continuous functions may be integrated term by term.** -/
theorem tsum_intervalIntegral_of_bound {a b : ℝ} {f : ℕ → ℝ → ℂ} {M : ℕ → ℝ}
    (hf : ∀ m, Continuous (f m)) (hM : ∀ m t, ‖f m t‖ ≤ M m) (hMs : Summable M) :
    (∑' m, ∫ t in a..b, f m t) = ∫ t in a..b, ∑' m, f m t := by
  have hint : ∀ m, Integrable (f m) (volume.restrict (Ι a b)) := fun m =>
    intervalIntegrable_iff.mp ((hf m).intervalIntegrable a b)
  have hnorm : ∀ m, Integrable (fun t => ‖f m t‖) (volume.restrict (Ι a b)) :=
    fun m => (hint m).norm
  have hconst : ∀ m : ℕ, Integrable (fun _ : ℝ => M m) (volume.restrict (Ι a b)) := by
    intro m
    exact intervalIntegrable_iff.mp intervalIntegrable_const
  have hle : ∀ m, (∫ t in Ι a b, ‖f m t‖) ≤ M m * volume.real (Ι a b) := by
    intro m
    have hmono : (∫ t in Ι a b, ‖f m t‖) ≤ ∫ _t in Ι a b, M m :=
      integral_mono (hnorm m) (hconst m) fun t => hM m t
    rw [setIntegral_const] at hmono
    calc (∫ t in Ι a b, ‖f m t‖) ≤ volume.real (Ι a b) • M m := hmono
      _ = M m * volume.real (Ι a b) := by rw [smul_eq_mul]; ring
  have hsum : Summable fun m => ∫ t in Ι a b, ‖f m t‖ := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun t => norm_nonneg _) hle ?_
    exact hMs.mul_right _
  have hcore := integral_tsum_of_summable_integral_norm hint hsum
  have hsummable : Summable fun m => ∫ t in Ι a b, f m t := by
    refine Summable.of_norm_bounded hsum fun m => ?_
    exact norm_integral_le_integral_norm _
  have hsides : ∀ m : ℕ, (∫ t in a..b, f m t)
      = (if a ≤ b then (1 : ℝ) else -1) • ∫ t in Ι a b, f m t := fun m =>
    intervalIntegral.intervalIntegral_eq_integral_uIoc _ _ _ _
  calc (∑' m, ∫ t in a..b, f m t)
      = ∑' m, (if a ≤ b then (1 : ℝ) else -1) • ∫ t in Ι a b, f m t :=
        tsum_congr fun m => hsides m
    _ = (if a ≤ b then (1 : ℝ) else -1) • ∑' m, ∫ t in Ι a b, f m t :=
        hsummable.tsum_const_smul _
    _ = (if a ≤ b then (1 : ℝ) else -1) • ∫ t in Ι a b, ∑' m, f m t := by rw [hcore]
    _ = ∫ t in a..b, ∑' m, f m t :=
        (intervalIntegral.intervalIntegral_eq_integral_uIoc _ _ _ _).symm

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.tsum_intervalIntegral_of_bound
