import GaloisForLFunctions.HTGeometry.UnitTorusPoincare

/-!
# From an almost-everywhere gradient bound to the translate-difference hypothesis

A Lipschitz observable on the unit torus lifts to a periodic Lipschitz function on the vector model,
where Rademacher's theorem supplies almost-everywhere differentiability.  Coordinate translate
differences of the observable are exactly coordinate difference quotients of the lift on a
fundamental box, so dominated convergence turns an almost-everywhere bound on the sum of squared
coordinate derivatives into the quadratic translate bound required by the torus Poincaré inequality.

The two steps compose into the variance bound in the form the phase-orbit estimates supply it: an
almost-everywhere gradient bound on the lift bounds the variance of the observable by the same
constant divided by `4π²`.
-/

open MeasureTheory Complex UnitAddTorus Filter Topology Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]

section Lift

/-- The projection from the vector model onto the unit torus. -/
def torusProj (x : d → ℝ) : UnitAddTorus d := fun j => ((x j : ℝ) : UnitAddCircle)

theorem torusProj_add_single (x : d → ℝ) (j : d) (h : ℝ) :
    torusProj (x + Pi.single j h) = torusProj x + coordShift j h := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp [torusProj, coordShift, Pi.single_eq_same]
  · simp [torusProj, coordShift, Pi.single_eq_of_ne hij]

/-- The fundamental box of the vector model. -/
def torusBox (d : Type*) [Fintype d] : Set (d → ℝ) := {x : d → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1}

theorem measurableSet_torusBox : MeasurableSet (torusBox d) := by
  have hset : torusBox d = ⋂ i : d, (fun x : d → ℝ => x i) ⁻¹' (Ioc (0 : ℝ) 1) := by
    ext x
    simp [torusBox]
  rw [hset]
  exact MeasurableSet.iInter fun i => (measurable_pi_apply i) measurableSet_Ioc

theorem integral_torus_eq_integral_box {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UnitAddTorus d → E) :
    (∫ t : UnitAddTorus d, f t) = ∫ x in torusBox d, f (torusProj x) := by
  have h := UnitAddTorus.integral_preimage f (fun _ : d => (0 : ℝ))
  simp only [zero_add] at h
  exact h

theorem torusBox_eq_pi : torusBox d = Set.univ.pi fun _ : d => Ioc (0 : ℝ) 1 := by
  ext x
  simp [torusBox]

theorem volume_torusBox : (volume (torusBox d)) = 1 := by
  rw [torusBox_eq_pi, volume_pi_pi]
  simp

theorem norm_single (j : d) (h : ℝ) : ‖(Pi.single j h : d → ℝ)‖ = ‖h‖ := by
  simpa using Pi.norm_single (G := fun _ : d => ℝ) (i := j) (y := h)

/-- Along a coordinate direction, difference quotients of a differentiable lift converge to the
directional derivative. -/
theorem tendsto_diffQuotient_sq {G : (d → ℝ) → ℂ} {x : d → ℝ} (hx : DifferentiableAt ℝ G x)
    (j : d) :
    Tendsto (fun h : ℝ => ‖G (x + Pi.single j h) - G x‖ ^ 2 / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (‖fderiv ℝ G x (Pi.single j 1)‖ ^ 2)) := by
  have hg : HasDerivAt (fun s : ℝ => x + s • (Pi.single j 1 : d → ℝ)) (Pi.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j 1 : d → ℝ)).const_add x
  have hx0 : x + (0 : ℝ) • (Pi.single j 1 : d → ℝ) = x := by simp
  have hGx : HasFDerivAt G (fderiv ℝ G x) (x + (0 : ℝ) • (Pi.single j 1 : d → ℝ)) := by
    rw [hx0]
    exact hx.hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => G (x + s • (Pi.single j 1 : d → ℝ)))
      (fderiv ℝ G x (Pi.single j 1)) 0 := hGx.comp_hasDerivAt 0 hg
  have hslope := hasDerivAt_iff_tendsto_slope.mp hline
  have hnorm := ((continuous_norm.pow 2).tendsto _).comp hslope
  refine hnorm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := hh
  have hsingle : (h : ℝ) • (Pi.single j 1 : d → ℝ) = Pi.single j h := by
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_eq_of_ne hij]
  simp only [Function.comp_apply, Pi.pow_apply, slope_def_module, hsingle, hx0, sub_zero]
  rw [norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, inv_pow, sq_abs, div_eq_inv_mul]


end Lift

section Transfer

variable {F : C(UnitAddTorus d, ℂ)}

/-- The lift of a torus observable to the vector model. -/
def torusLift (F : C(UnitAddTorus d, ℂ)) : (d → ℝ) → ℂ := fun x => F (torusProj x)

theorem continuous_torusLift (F : C(UnitAddTorus d, ℂ)) : Continuous (torusLift F) := by
  refine F.continuous.comp ?_
  refine continuous_pi fun j => ?_
  exact (AddCircle.continuous_mk' 1).comp (continuous_apply j)

theorem integral_translate_diff_eq (F : C(UnitAddTorus d, ℂ)) (j : d) (h : ℝ) :
    (∫ t : UnitAddTorus d, ‖F (t + coordShift j h) - F t‖ ^ 2) =
      ∫ x in torusBox d, ‖torusLift F (x + Pi.single j h) - torusLift F x‖ ^ 2 := by
  rw [integral_torus_eq_integral_box (fun t => ‖F (t + coordShift j h) - F t‖ ^ 2)]
  refine setIntegral_congr_fun measurableSet_torusBox fun x _ => ?_
  rw [torusLift, torusLift, torusProj_add_single]

theorem measurable_fderiv_apply (G : (d → ℝ) → ℂ) (v : d → ℝ) :
    Measurable fun x => fderiv ℝ G x v :=
  (ContinuousLinearMap.apply ℝ ℂ v).continuous.measurable.comp (measurable_fderiv ℝ G)

set_option maxHeartbeats 1000000 in
/-- **Dominated convergence for coordinate difference quotients.** -/
theorem tendsto_integral_diffQuotient (F : C(UnitAddTorus d, ℂ)) {L : NNReal}
    (hLip : LipschitzWith L (torusLift F)) (j : d) :
    Tendsto (fun h : ℝ => ∫ x in torusBox d,
        ‖torusLift F (x + Pi.single j h) - torusLift F x‖ ^ 2 / h ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ x in torusBox d, ‖fderiv ℝ (torusLift F) x (Pi.single j 1)‖ ^ 2)) := by
  have hcont := continuous_torusLift F
  refine tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (d → ℝ)).restrict (torusBox d))
    (l := 𝓝[≠] (0 : ℝ))
    (F := fun (h : ℝ) (x : d → ℝ) =>
      ‖torusLift F (x + Pi.single j h) - torusLift F x‖ ^ 2 / h ^ 2)
    (f := fun x : d → ℝ => ‖fderiv ℝ (torusLift F) x (Pi.single j 1)‖ ^ 2)
    (bound := fun _ => ((L : ℝ)) ^ 2) ?_ ?_ ?_ ?_
  · filter_upwards with h
    refine Continuous.aestronglyMeasurable ?_
    refine Continuous.div_const ?_ _
    exact ((hcont.comp (continuous_id.add continuous_const)).sub hcont).norm.pow 2
  · filter_upwards [self_mem_nhdsWithin] with h hh
    filter_upwards with x
    have hh0 : h ≠ 0 := hh
    have hdist : ‖torusLift F (x + Pi.single j h) - torusLift F x‖ ≤ (L : ℝ) * |h| := by
      have := hLip.dist_le_mul (x + Pi.single j h) x
      rw [dist_eq_norm, dist_eq_norm] at this
      simpa [norm_single, Real.norm_eq_abs] using this
    have hnn : (0 : ℝ) ≤ ‖torusLift F (x + Pi.single j h) - torusLift F x‖ := norm_nonneg _
    have hsq : ‖torusLift F (x + Pi.single j h) - torusLift F x‖ ^ 2 ≤ ((L : ℝ)) ^ 2 * h ^ 2 := by
      have hsq' := mul_self_le_mul_self hnn hdist
      calc ‖torusLift F (x + Pi.single j h) - torusLift F x‖ ^ 2
          = ‖torusLift F (x + Pi.single j h) - torusLift F x‖ *
            ‖torusLift F (x + Pi.single j h) - torusLift F x‖ := by ring
        _ ≤ ((L : ℝ) * |h|) * ((L : ℝ) * |h|) := hsq'
        _ = ((L : ℝ)) ^ 2 * h ^ 2 := by
            rw [← sq_abs h]
            ring
    have hh2 : (0 : ℝ) < h ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hh2]
    exact hsq
  · refine integrableOn_const.mpr (Or.inr ?_)
    rw [volume_torusBox]
    exact one_lt_top
  · filter_upwards [hLip.ae_differentiableAt] with x hx
    exact tendsto_diffQuotient_sq hx j

end Transfer

end GaloisForLFunctions.HTGeometry
