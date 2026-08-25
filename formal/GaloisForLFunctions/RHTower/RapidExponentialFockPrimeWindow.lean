import GaloisForLFunctions.RHTower.PolynomialFockPrimeBallOverlap
import GaloisForLFunctions.RHTower.RapidExponentialFockPotentialGeometry

/-!
# Prime-log mass in rapid exponential Fock cells

The rapid adapted radius is exponentially small.  Combining its exact upper bound with the
uniform additive prime-window law proves that every fixed multiple of a rapid cell has vanishing
critical-prime mass.  This is the arithmetic producer used by the rapid-Fock vanishing-Carleson
argument; it does not assume a short-interval relative PNT.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The main prime-window term `2 x c tau_a(x)` vanishes for every fixed positive aperture. -/
theorem tendsto_rapidExponentialFockPrimeWindowMain_zero
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun x : ℝ =>
      2 * x * (c * rapidExponentialFockAdaptedRadius a x))
      atTop (nhds 0) := by
  have hmodel :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha).const_mul
      (2 * c * (2 * a)⁻¹)
  have hnonneg : ∀ᶠ x : ℝ in atTop,
      0 ≤ 2 * x * (c * rapidExponentialFockAdaptedRadius a x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (mul_nonneg (by norm_num) hx.le)
      (mul_nonneg hc.le (rapidExponentialFockAdaptedRadius_pos ha hx).le)
  have hupper : ∀ᶠ x : ℝ in atTop,
      2 * x * (c * rapidExponentialFockAdaptedRadius a x) ≤
        (2 * c * (2 * a)⁻¹) * (x ^ (1 : ℝ) * Real.exp (-a * x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hr := rapidExponentialFockAdaptedRadius_upper ha hx
    have hfactor : 0 ≤ 2 * x * c := by positivity
    calc
      2 * x * (c * rapidExponentialFockAdaptedRadius a x) =
          (2 * x * c) * rapidExponentialFockAdaptedRadius a x := by ring
      _ ≤ (2 * x * c) * ((2 * a)⁻¹ * Real.exp (-a * x)) :=
        mul_le_mul_of_nonneg_left hr hfactor
      _ = (2 * c * (2 * a)⁻¹) *
          (x ^ (1 : ℝ) * Real.exp (-a * x)) := by
        rw [Real.rpow_one]
        ring
  exact squeeze_zero' hnonneg hupper (by simpa only [mul_zero] using hmodel)

/-- Uniform PNT remainder for a fixed multiple of the rapid adapted radius. -/
theorem tendsto_primeLogWindowMass_sub_rapidExponentialFockMain
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun x : ℝ =>
      primeLogWindowMass x (c * rapidExponentialFockAdaptedRadius a x) -
        2 * x * (c * rapidExponentialFockAdaptedRadius a x))
      atTop (nhds 0) := by
  have hr0 : Tendsto (fun x : ℝ =>
      c * rapidExponentialFockAdaptedRadius a x) atTop (nhds 0) := by
    simpa using (tendsto_rapidExponentialFockAdaptedRadius_atTop ha).const_mul c
  have hrpos : ∀ᶠ x : ℝ in atTop,
      0 < c * rapidExponentialFockAdaptedRadius a x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos hc (rapidExponentialFockAdaptedRadius_pos ha hx)
  have hrone : ∀ᶠ x : ℝ in atTop,
      c * rapidExponentialFockAdaptedRadius a x ≤ 1 := by
    filter_upwards [hr0.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with x hx
    have habs : |c * rapidExponentialFockAdaptedRadius a x| < 1 := by
      simpa [Real.dist_eq] using hx
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) habs)
  exact tendsto_primeLogWindowMass_sub_main_of_admissibleRadius
    (fun x => c * rapidExponentialFockAdaptedRadius a x) hrpos hrone

/-- Critical-prime mass in every fixed rapid-Fock cell tends to zero. -/
theorem tendsto_primeLogWindowMass_rapidExponentialFockAdaptedRadius_zero
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun x : ℝ =>
      primeLogWindowMass x (c * rapidExponentialFockAdaptedRadius a x))
      atTop (nhds 0) := by
  have herr := tendsto_primeLogWindowMass_sub_rapidExponentialFockMain ha hc
  have hmain := tendsto_rapidExponentialFockPrimeWindowMain_zero ha hc
  have hsum := herr.add hmain
  simpa only [sub_add_cancel, add_zero] using hsum

end

end RHTower
