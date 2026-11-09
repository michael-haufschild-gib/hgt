import GaloisForLFunctions.RHTower.PrimePowerSumBound
import GaloisForLFunctions.RHTower.Sieve.PrimeCountRelativeWindow
import GaloisForLFunctions.PNTPlus.Consequences
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Prime mass in a logarithmic comb

The prime number theorem determines the logarithmic mass in all geometric
windows simultaneously. A summable geometric majorant controls the infinite
tail. At phase-aligned cutoffs these windows give actual prime subsets which
return at height one, with an exact limiting fraction of Chebyshev mass.
-/

open Filter Topology Real Finset

namespace GaloisForLFunctions.CollectiveDiophantineGeometry

noncomputable section

/-- Logarithmic prime mass in the disjoint geometric windows `(rxqʲ,xqʲ]`. -/
def geometricPrimeMass (q r x : ℝ) : ℝ :=
  ∑' j : ℕ, (Chebyshev.theta (x * q ^ j) - Chebyshev.theta (x * (r * q ^ j)))

private theorem theta_below_one {x : ℝ} (hx : x < 1) : Chebyshev.theta x = 0 := by
  simp [Chebyshev.theta, Nat.floor_eq_zero.mpr hx]

private theorem theta_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → Chebyshev.theta x ≤ C * x := by
  obtain ⟨C, hC, h⟩ := RHTower.exists_chebyshevTheta_le_linear
  refine ⟨C, hC, fun x hx => ?_⟩
  rcases le_or_gt 1 x with h1 | h1
  · exact h x h1
  · rw [theta_below_one h1]
    exact mul_nonneg hC.le hx

private theorem theta_ratio_limit :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  have hne : ∀ᶠ x : ℝ in atTop, x ≠ 0 :=
    (eventually_gt_atTop 0).mono fun _ hx => hx.ne'
  exact (Asymptotics.isEquivalent_iff_tendsto_one hne).mp chebyshev_asymptotic

private theorem scaled_theta_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Chebyshev.theta (x * c) / x) atTop (𝓝 c) := by
  have h := (theta_ratio_limit.comp (Filter.Tendsto.atTop_mul_const hc tendsto_id)).mul_const c
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp
  field_simp [hx.ne', hc.ne']

/-- Exact mass of the infinite comb, with no restriction on the number of windows. -/
theorem geometricPrimeMass_ratio_limit {q r : ℝ}
    (hq : 0 < q) (hqr : q < r) (hr : r < 1) :
    Tendsto (fun x : ℝ => geometricPrimeMass q r x / x) atTop
      (𝓝 ((1 - r) / (1 - q))) := by
  have hr0 : 0 < r := hq.trans hqr
  have hq1 : q < 1 := hqr.trans hr
  obtain ⟨C, hC0, hC⟩ := theta_linear
  have hs : Summable (fun j : ℕ => C * q ^ j) :=
    (summable_geometric_of_lt_one hq.le hq1).mul_left C
  have hterm (j : ℕ) :
      Tendsto (fun x : ℝ =>
        (Chebyshev.theta (x * q ^ j) - Chebyshev.theta (x * (r * q ^ j))) / x)
        atTop (𝓝 ((1 - r) * q ^ j)) := by
    have h := (scaled_theta_limit (pow_pos hq j)).sub
      (scaled_theta_limit (mul_pos hr0 (pow_pos hq j)))
    have heq : q ^ j - r * q ^ j = (1 - r) * q ^ j := by ring
    simpa only [← sub_div, heq] using h
  have hb : ∀ᶠ x : ℝ in atTop, ∀ j : ℕ,
      ‖(Chebyshev.theta (x * q ^ j) - Chebyshev.theta (x * (r * q ^ j))) / x‖
        ≤ C * q ^ j := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx j
    have hnonneg : 0 ≤ Chebyshev.theta (x * q ^ j) -
        Chebyshev.theta (x * (r * q ^ j)) := by
      apply sub_nonneg.mpr
      apply RHTower.chebyshevTheta_mono
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (pow_nonneg hq.le j) hr.le) hx.le
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnonneg hx.le)]
    apply (div_le_iff₀ hx).mpr
    calc
      Chebyshev.theta (x * q ^ j) - Chebyshev.theta (x * (r * q ^ j))
          ≤ Chebyshev.theta (x * q ^ j) :=
        sub_le_self _ (RHTower.chebyshevTheta_nonneg _)
      _ ≤ C * (x * q ^ j) := hC _ (mul_nonneg hx.le (pow_nonneg hq.le j))
      _ = C * q ^ j * x := by ring
  have h := tendsto_tsum_of_dominated_convergence hs hterm hb
  simpa only [geometricPrimeMass, tsum_div_const, tsum_mul_left,
    tsum_geometric_of_lt_one hq.le hq1, ← div_eq_mul_inv] using h

end

end GaloisForLFunctions.CollectiveDiophantineGeometry
