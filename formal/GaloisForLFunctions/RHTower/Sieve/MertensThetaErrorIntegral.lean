import GaloisForLFunctions.RHTower.Sieve.MertensFirstAbel

/-!
# Integrability of `(θ(t) − t)/t²`

`θ` is monotone, so it is integrable on every compact interval; past the point where the decay
estimate starts, `|θ(t) − t|/t² ≤ K·exp(−c√(log t))/t`, which has a finite tail integral.  Together
these give integrability on all of `(2,∞)`, hence a finite value for the constant appearing in
Mertens' theorem.
-/

namespace RHTower.Sieve

open Filter Topology Asymptotics MeasureTheory Set

/-- The error density of `θ`. -/
noncomputable def thetaErrorDensity (t : ℝ) : ℝ := (Chebyshev.theta t - t) / t ^ 2

theorem measurable_thetaErrorDensity : Measurable thetaErrorDensity := by
  unfold thetaErrorDensity
  exact (Chebyshev.theta_mono.measurable.sub measurable_id).div (measurable_id.pow_const 2)

/-- On a bounded interval away from zero the density is integrable, because `θ` is monotone. -/
theorem integrableOn_thetaErrorDensity_Ioc {a b : ℝ} (ha : 0 < a) :
    IntegrableOn thetaErrorDensity (Set.Ioc a b) := by
  have hcompact : IntegrableOn (fun t : ℝ => Chebyshev.theta t - t) (Set.Icc a b) := by
    refine MeasureTheory.IntegrableOn.sub ?_ ?_
    · exact MonotoneOn.integrableOn_isCompact isCompact_Icc (Chebyshev.theta_mono.monotoneOn _)
    · exact (continuous_id.continuousOn).integrableOn_Icc
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) := by
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ha ht.1
    positivity
  have hIcc : IntegrableOn thetaErrorDensity (Set.Icc a b) := by
    have := hcompact.mul_continuousOn hcont isCompact_Icc
    refine this.congr_fun (fun t _ => ?_) measurableSet_Icc
    unfold thetaErrorDensity
    rw [div_eq_mul_inv]
  exact hIcc.mono_set Set.Ioc_subset_Icc_self

/-- Past the decay threshold the density is dominated by the tail weight. -/
theorem integrableOn_thetaErrorDensity_Ioi_of_bound {c K T : ℝ} (hc : 0 < c) (hT : 1 < T)
    (hbd : ∀ t : ℝ, T < t →
      |Chebyshev.theta t - t| ≤ K * t * Real.exp (-c * Real.sqrt (Real.log t))) :
    IntegrableOn thetaErrorDensity (Set.Ioi T) := by
  have hdom : IntegrableOn
      (fun t : ℝ => K * (Real.exp (-c * Real.sqrt (Real.log t)) / t)) (Set.Ioi T) :=
    (integrableOn_expSqrtLog_div_Ioi hc hT).const_mul K
  refine hdom.mono' measurable_thetaErrorDensity.aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := lt_trans (by linarith) ht
  have hsq : (0 : ℝ) < t ^ 2 := by positivity
  have habs : ‖thetaErrorDensity t‖ = |Chebyshev.theta t - t| / t ^ 2 := by
    unfold thetaErrorDensity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hsq]
  rw [habs]
  rw [div_le_iff₀ hsq]
  have hb := hbd t ht
  have hstep : K * (Real.exp (-c * Real.sqrt (Real.log t)) / t) * t ^ 2
      = K * t * Real.exp (-c * Real.sqrt (Real.log t)) := by
    field_simp
  rw [hstep]
  exact hb

/-- **The density is integrable on `(2,∞)`.** -/
theorem integrableOn_thetaErrorDensity_Ioi {c K T : ℝ} (hc : 0 < c) (hT : 2 ≤ T)
    (hbd : ∀ t : ℝ, T < t →
      |Chebyshev.theta t - t| ≤ K * t * Real.exp (-c * Real.sqrt (Real.log t))) :
    IntegrableOn thetaErrorDensity (Set.Ioi 2) := by
  have hsplit : Set.Ioc (2 : ℝ) T ∪ Set.Ioi T = Set.Ioi 2 := Set.Ioc_union_Ioi_eq_Ioi hT
  rw [← hsplit]
  exact (integrableOn_thetaErrorDensity_Ioc (by norm_num)).union
    (integrableOn_thetaErrorDensity_Ioi_of_bound hc (by linarith) hbd)

end RHTower.Sieve
