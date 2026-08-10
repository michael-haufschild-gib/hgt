import GaloisForLFunctions.RHTower.DeningerHigherMajorant
import GaloisForLFunctions.RHTower.DeningerPreimageMass

/-!
# All moments of the canonical Möbius preimage are finite

The canonical preimage is bounded pointwise by the Abel majorant, so its `x^r`-weighted mass is
bounded by the mass of the order-`r` majorant, which is finite for every `r ≥ 1`.  Together with
the order-`0` bound this gives

`∫_0^∞ x^r |f_h(x)| dx < ∞` for every `r ≥ 0`,

so the canonical preimage lies in every weighted `L¹` of the ray: all its moments exist.

* `deningerMobiusPreimage_aestronglyMeasurable` : the preimage is measurable on the ray.
* `deningerMobiusPreimage_higherMass_lt_top` : **every weighted mass is finite.**
* `deningerMobiusPreimage_moment_integrable` : **every moment of the preimage exists.**
-/

namespace RHTower

open MeasureTheory SchwartzMap ENNReal Filter Topology ArithmeticFunction

noncomputable section

/-- The Abel partial sums of the Möbius series are measurable. -/
theorem deningerMobiusPartial_measurable (h : 𝓢(ℝ, ℂ)) (N : ℕ) :
    Measurable fun x : ℝ =>
      ∑ n ∈ Finset.range N, ((moebius n : ℤ) : ℂ) * deningerLogPull h ((n : ℝ) * x) := by
  have hpull : Measurable (deningerLogPull h) :=
    (h.continuous.measurable).comp Real.measurable_log
  refine Finset.measurable_sum _ fun n _ => ?_
  exact (hpull.comp (measurable_id.const_mul _)).const_mul _

/-- **The canonical preimage is measurable on the ray.**  It is the pointwise limit of its Abel
partial sums, which converge at every positive point. -/
theorem deningerMobiusPreimage_aestronglyMeasurable {h : 𝓢(ℝ, ℂ)}
    (hh : h ∈ DeningerExpSchwartz) :
    AEStronglyMeasurable (deningerMobiusPreimage h) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (fun N => (deningerMobiusPartial_measurable h N).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  exact (deningerMobiusRay_summable hh hx0).hasSum.tendsto_sum_nat

/-- The preimage is bounded by the order-`r` majorant. -/
theorem deningerMobiusPreimage_higherEnorm_le {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    (r : ℕ) {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (x ^ r) * ‖deningerMobiusPreimage h x‖ₑ ≤ deningerHigherMajorant h r x := by
  rw [deningerHigherMajorant]
  exact mul_le_mul_right (deningerMobiusPreimage_enorm_le hh hx) _

/-- **Every weighted mass of the canonical preimage is finite.** -/
theorem deningerMobiusPreimage_higherMass_lt_top {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    {r : ℕ} (hr : 1 ≤ r) :
    (∫⁻ x in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (x ^ r) * ‖deningerMobiusPreimage h x‖ₑ) < ⊤ := by
  refine lt_of_le_of_lt ?_ (deningerHigherMajorant_mass_lt_top hh hr)
  refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
  exact deningerMobiusPreimage_higherEnorm_le hh r hx

/-- **Every moment of the canonical preimage exists.**  For `r = 0` this is the `L¹` bound; for
`r ≥ 1` it is the order-`r` majorant estimate. -/
theorem deningerMobiusPreimage_moment_integrable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    (r : ℕ) :
    IntegrableOn (fun x : ℝ => ((x ^ r : ℝ) : ℂ) * deningerMobiusPreimage h x)
      (Set.Ioi (0 : ℝ)) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => ((x ^ r : ℝ) : ℂ) * deningerMobiusPreimage h x)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((Complex.measurable_ofReal.comp (measurable_id.pow_const r)).aestronglyMeasurable).mul
      (deningerMobiusPreimage_aestronglyMeasurable hh)
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hcongr : (∫⁻ x in Set.Ioi (0 : ℝ),
      ‖((x ^ r : ℝ) : ℂ) * deningerMobiusPreimage h x‖ₑ)
      = ∫⁻ x in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (x ^ r) * ‖deningerMobiusPreimage h x‖ₑ := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    rw [enorm_mul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hx0.le r)]
  rw [hcongr]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 : (∫⁻ x in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (x ^ (0 : ℕ)) * ‖deningerMobiusPreimage h x‖ₑ)
        = ∫⁻ x in Set.Ioi (0 : ℝ), ‖deningerMobiusPreimage h x‖ₑ := by
      refine lintegral_congr fun x => ?_
      rw [pow_zero, ENNReal.ofReal_one, one_mul]
    rw [h0]
    exact deningerMobiusPreimage_mass_lt_top hh
  · exact deningerMobiusPreimage_higherMass_lt_top hh hr

end

end RHTower
