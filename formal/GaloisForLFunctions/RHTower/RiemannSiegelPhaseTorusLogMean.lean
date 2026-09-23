import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Torus (random-phase) log-means of the Riemann–Siegel amplitude

On the critical line the Riemann–Siegel formula writes Hardy's function as
`Z(t) = 2 Re (e^{iθ(t)} D(t)) + O(t^{-1/4})` with `D(t) = ∑_{n ≤ √(t/2π)} n^{-1/2-it}`, so that
`|ζ(1/2+it)| = 2 |D(t)| |cos (θ(t) + arg D(t))|` up to that additive error. This does not
give a logarithmic-mean error bound near zeros. The "torus model" of the
critical line replaces the arithmetic phases `(θ(t), t log p)_p` by independent uniform phases.
This file certifies exact identities for the **geometric mean of the randomized main term**,
not deterministic flow transfer or a logarithmic remainder estimate for zeta:

* `circleAverage_log_norm_const_add` — Jensen: the circle average of `log ‖a + z‖` over `‖z‖ = R`
  is `log (max R ‖a‖)`; in particular a fresh uniform phase never lowers a log-mean
  (`log_norm_le_circleAverage_log_norm_const_add`);
* `abs_two_re_mul_eq_norm_conj_add_sq_mul` — for `‖z‖ = 1`, `|2 Re (z w)| = ‖conj w + z² w‖`;
* `circleAverage_comp_sq` — the unit-circle average is invariant under `z ↦ z²`;
* `circleAverage_log_norm_conj_add_mul` — the phase average of `log ‖conj w + u w‖` is `log ‖w‖`;
* `circleAverage_log_norm_two_re_mul` — hence the average over the AFE phase of
  `log |2 Re (e^{iφ} w)|` is exactly `log ‖w‖`.

Thus independent-phase averaging of the main term leaves the amplitude log-mean unchanged.
No growth law for that amplitude, deterministic phase-locking law, zeta log-mean limit or RH
equivalence is proved here. The identities contain no zeta divisor and use no computation.
-/

open Real Complex

namespace RHTower

noncomputable section

/-- **Jensen's max identity.**  The circle average of `log ‖a + z‖` over `‖z‖ = R` equals
`log (max R ‖a‖)`. -/
theorem circleAverage_log_norm_const_add (a : ℂ) {R : ℝ} (hR : 0 < R) :
    circleAverage (fun z : ℂ => Real.log ‖a + z‖) 0 R = Real.log (max R ‖a‖) := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := -a) (c := 0) hR.ne'
  have hfun : (fun z : ℂ => Real.log ‖a + z‖) = (Real.log ‖· - -a‖) := by
    funext z; simp [sub_neg_eq_add, add_comm]
  rw [hfun, h]
  simp only [zero_sub, norm_neg]
  by_cases ha : a = 0
  · simp [ha, hR.le]
  · have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
    rw [posLog_eq_log_max_one (by positivity)]
    rw [← Real.log_mul hR.ne' (by positivity)]
    congr 1
    rw [mul_max_of_nonneg _ _ hR.le, mul_one, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]

/-- Adding an independent uniform phase never lowers a log-mean. -/
theorem log_norm_le_circleAverage_log_norm_const_add {a : ℂ} (ha : a ≠ 0) {R : ℝ}
    (hR : 0 < R) :
    Real.log ‖a‖ ≤ circleAverage (fun z : ℂ => Real.log ‖a + z‖) 0 R := by
  rw [circleAverage_log_norm_const_add a hR]
  exact Real.log_le_log (norm_pos_iff.mpr ha) (le_max_right _ _)

/-- On the unit circle, twice the real part of `z * w` has modulus `‖conj w + z ^ (2 : ℕ) * w‖`. -/
theorem abs_two_re_mul_eq_norm_conj_add_sq_mul {z : ℂ} (hz : ‖z‖ = 1) (w : ℂ) :
    |2 * (z * w).re| = ‖(starRingEnd ℂ) w + z ^ (2 : ℕ) * w‖ := by
  have hzz : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  have hfac : (starRingEnd ℂ) w + z ^ (2 : ℕ) * w = z * ((2 * (z * w).re : ℝ) : ℂ) := by
    rw [← Complex.add_conj, map_mul]
    linear_combination (-(starRingEnd ℂ) w) * hzz
  rw [hfac, norm_mul, hz, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The unit-circle average is invariant under the doubling map `z ↦ z ^ (2 : ℕ)`. -/
theorem circleAverage_comp_sq {g : ℂ → ℝ} (hg : CircleIntegrable g 0 1) :
    circleAverage (fun z : ℂ => g (z ^ (2 : ℕ))) 0 1 = circleAverage g 0 1 := by
  have hsq : ∀ θ : ℝ, circleMap 0 1 θ ^ (2 : ℕ) = circleMap 0 1 (2 * θ) := by
    intro θ
    rw [circleMap_zero, circleMap_zero, Complex.ofReal_one, one_mul, one_mul,
      ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  set G : ℝ → ℝ := fun θ => g (circleMap 0 1 θ) with hG
  have hper : Function.Periodic G (2 * Real.pi) := (periodic_circleMap 0 1).comp g
  have hint : IntervalIntegrable G MeasureTheory.volume 0 (2 * Real.pi) := hg
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hint0 : IntervalIntegrable G MeasureTheory.volume 0 (0 + 2 * Real.pi) := by
    rw [zero_add]; exact hint
  have hint2 : IntervalIntegrable G MeasureTheory.volume (2 * Real.pi) (2 * Real.pi + 2 * Real.pi) :=
    hper.intervalIntegrable h2pi hint0 _ _
  rw [Real.circleAverage_def, Real.circleAverage_def]
  simp_rw [hsq]
  change (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, G (2 * θ)
      = (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, G θ
  congr 1
  rw [intervalIntegral.integral_comp_mul_left G (by norm_num : (2 : ℝ) ≠ 0)]
  have hsplit : ∫ θ in (2 * (0 : ℝ))..2 * (2 * Real.pi), G θ
      = (∫ θ in (0 : ℝ)..2 * Real.pi, G θ) + ∫ θ in (2 * Real.pi)..(2 * Real.pi + 2 * Real.pi), G θ := by
    rw [show (2 : ℝ) * 0 = 0 by ring, show (2 : ℝ) * (2 * Real.pi) = 2 * Real.pi + 2 * Real.pi by ring]
    exact (intervalIntegral.integral_add_adjacent_intervals hint hint2).symm
  rw [hsplit, hper.intervalIntegral_add_eq (2 * Real.pi) 0, zero_add]
  simp only [smul_eq_mul]
  ring

/-- The phase average of `log ‖conj w + u w‖` over the unit circle is `log ‖w‖`. -/
theorem circleAverage_log_norm_conj_add_mul (w : ℂ) :
    circleAverage (fun u : ℂ => Real.log ‖(starRingEnd ℂ) w + u * w‖) 0 1 = Real.log ‖w‖ := by
  by_cases hw : w = 0
  · simp [hw, Real.circleAverage_const]
  · have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw
    set b : ℂ := (starRingEnd ℂ) w / w with hb
    have hnb : ‖b‖ = 1 := by
      rw [hb, norm_div, Complex.norm_conj, div_self hnw.ne']
    have hfac : ∀ u : ℂ, (starRingEnd ℂ) w + u * w = w * (b + u) := by
      intro u; rw [hb]; field_simp
    -- off the single point `u = -b`, split the logarithm
    have hcod : {u : ℂ | b + u ≠ 0} ∈ Filter.codiscreteWithin (Metric.sphere (0 : ℂ) |1|) := by
      apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
      intro z _
      refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      apply Set.Subsingleton.finite
      intro z₁ hz₁ z₂ hz₂
      simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_univ, true_and,
        Decidable.not_not] at hz₁ hz₂
      rw [eq_neg_of_add_eq_zero_right hz₁.2, eq_neg_of_add_eq_zero_right hz₂.2]
    have hcongr : (fun u : ℂ => Real.log ‖(starRingEnd ℂ) w + u * w‖)
        =ᶠ[Filter.codiscreteWithin (Metric.sphere (0 : ℂ) |1|)]
          ((fun _ : ℂ => Real.log ‖w‖) + fun u : ℂ => Real.log ‖b + u‖) := by
      filter_upwards [hcod] with u hu
      simp only [Pi.add_apply]
      rw [hfac u, norm_mul, Real.log_mul hnw.ne' (norm_ne_zero_iff.mpr hu)]
    rw [Real.circleAverage_congr_codiscreteWithin hcongr one_ne_zero]
    have hint : CircleIntegrable (fun u : ℂ => Real.log ‖b + u‖) 0 1 := by
      have hmero : MeromorphicOn (fun u : ℂ => b + u) (Metric.sphere (0 : ℂ) |1|) :=
        (analyticOnNhd_const.add analyticOnNhd_id).meromorphicOn
      exact hmero.circleIntegrable_log_norm
    rw [Real.circleAverage_add (circleIntegrable_const _ _ _) hint, Real.circleAverage_const,
      circleAverage_log_norm_const_add b one_pos, hnb, max_self, Real.log_one, add_zero]

/-- **The torus-model AFE identity.**  Averaging over an independent uniform phase `φ`, the
log-mean of `|2 Re (e^{iφ} w)|` is exactly `log ‖w‖`: the phase factor `2 cos ψ` has geometric mean
one. This is a randomized main-term identity; no zeta remainder or deterministic flow occurs. -/
theorem circleAverage_log_norm_two_re_mul (w : ℂ) :
    circleAverage (fun z : ℂ => Real.log |2 * (z * w).re|) 0 1 = Real.log ‖w‖ := by
  have hsphere : Set.EqOn (fun z : ℂ => Real.log |2 * (z * w).re|)
      (fun z : ℂ => Real.log ‖(starRingEnd ℂ) w + z ^ (2 : ℕ) * w‖) (Metric.sphere (0 : ℂ) |1|) := by
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using hz
    simp only
    rw [abs_two_re_mul_eq_norm_conj_add_sq_mul hz1 w]
  rw [Real.circleAverage_congr_sphere hsphere]
  have hint : CircleIntegrable (fun u : ℂ => Real.log ‖(starRingEnd ℂ) w + u * w‖) 0 1 := by
    have hmero : MeromorphicOn (fun u : ℂ => (starRingEnd ℂ) w + u * w)
        (Metric.sphere (0 : ℂ) |1|) :=
      (analyticOnNhd_const.add (analyticOnNhd_id.mul analyticOnNhd_const)).meromorphicOn
    exact hmero.circleIntegrable_log_norm
  exact (circleAverage_comp_sq hint).trans (circleAverage_log_norm_conj_add_mul w)

end

end RHTower
