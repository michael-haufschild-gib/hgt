import GaloisForLFunctions.HTGeometry.SteinhausScalingIdentity
import GaloisForLFunctions.RHTower.SteinhausSubgaussian

/-!
# The super-critical constant

For `1/2 < α < 1` the fixed integrand `u ↦ log I₀(w_α(u))` is integrable on the whole half line:
near the origin it is dominated by `w_α(u) = (1−α)u^{−α}` (integrable because `α < 1`), and near
infinity by `w_α(u)²/2` (integrable because `2α > 1`).  Its total mass

`K_α = ∫₀^∞ log I₀(w_α(u)) du`

is exactly the card's constant `(7)`; the substitution `x = w_α(u)` turns it into
`((1−α)^{1/α}/α)∫₀^∞ log I₀(x) x^{−1/α−1} dx`.

The scaling identity therefore turns the small-tilt asymptotic of `Λ_α` into the statement that the
truncated integral converges to its improper value.
-/

open MeasureTheory Filter Topology Set

namespace HTGeometry

noncomputable section

theorem measurable_profileCumulant (α : ℝ) :
    Measurable fun u : ℝ => steinhausLogLaplace (weightProfile α u) := by
  have hwm : Measurable (weightProfile α) := by
    have hfun : (weightProfile α) = fun v : ℝ => (1 - α) * v ^ (-α) := rfl
    rw [hfun]
    exact measurable_const.mul (measurable_id.pow_const (-α))
  exact continuous_steinhausLogLaplace.measurable.comp hwm

/-- Near the origin the integrand is dominated by the profile itself. -/
theorem integrableOn_profileCumulant_Ioc {α : ℝ} (hα : α < 1) :
    IntegrableOn (fun u : ℝ => steinhausLogLaplace (weightProfile α u)) (Ioc (0 : ℝ) 1) := by
  have hdom : IntegrableOn (weightProfile α) (Ioc (0 : ℝ) 1) := by
    have h := intervalIntegrable_weightProfile hα
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
    exact h
  refine Integrable.mono' hdom
    ((measurable_profileCumulant α).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : (0 : ℝ) ≤ u := hu.1.le
  have hw : 0 ≤ weightProfile α u := weightProfile_nonneg hα hu0
  rw [Real.norm_eq_abs, abs_of_nonneg (steinhausLogLaplace_nonneg _)]
  have := steinhausLogLaplace_le_abs (weightProfile α u)
  rwa [abs_of_nonneg hw] at this

/-- Near infinity the integrand is dominated by the square of the profile. -/
theorem integrableOn_profileCumulant_Ioi_one {α : ℝ} (hα2 : 1 / 2 < α) :
    IntegrableOn (fun u : ℝ => steinhausLogLaplace (weightProfile α u)) (Ioi (1 : ℝ)) := by
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-(2 * α))) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hdom : IntegrableOn (fun u : ℝ => (1 - α) ^ 2 / 2 * u ^ (-(2 * α))) (Ioi (1 : ℝ)) :=
    hpow.const_mul _
  refine Integrable.mono' hdom
    ((measurable_profileCumulant α).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0 : ℝ) < u := lt_trans (by norm_num) hu
  rw [Real.norm_eq_abs, abs_of_nonneg (steinhausLogLaplace_nonneg _)]
  refine (steinhausLogLaplace_le_sq _).trans (le_of_eq ?_)
  rw [weightProfile]
  rw [mul_pow, ← Real.rpow_natCast (u ^ (-α)) 2, ← Real.rpow_mul hu0.le]
  ring_nf

/-- **The integrand is integrable on the whole half line.** -/
theorem integrableOn_profileCumulant {α : ℝ} (hα2 : 1 / 2 < α) (hα : α < 1) :
    IntegrableOn (fun u : ℝ => steinhausLogLaplace (weightProfile α u)) (Ioi (0 : ℝ)) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)).symm
  rw [hsplit]
  exact (integrableOn_profileCumulant_Ioc hα).union (integrableOn_profileCumulant_Ioi_one hα2)

/-- **The super-critical constant** `K_α`. -/
def rvSuperConst (α : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), steinhausLogLaplace (weightProfile α u)

/-- The truncated integrals converge to the constant. -/
theorem tendsto_rvTailIntegral {α : ℝ} (hα2 : 1 / 2 < α) (hα : α < 1) {ι : Type*}
    {l : Filter ι} [l.IsCountablyGenerated] {b : ι → ℝ} (hb : Tendsto b l atTop) :
    Tendsto (fun i => rvTailIntegral α (b i)) l (𝓝 (rvSuperConst α)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_profileCumulant hα2 hα) hb

/-- The constant is nonnegative. -/
theorem rvSuperConst_nonneg (α : ℝ) : 0 ≤ rvSuperConst α := by
  refine setIntegral_nonneg measurableSet_Ioi ?_
  intro u _
  exact steinhausLogLaplace_nonneg _

end

end HTGeometry
