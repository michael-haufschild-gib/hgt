import GaloisForLFunctions.HTGeometry.SzegoLowerBound
import GaloisForLFunctions.HTGeometry.RieszBrothersReduction
import GaloisForLFunctions.HTGeometry.SzegoConcretePolynomial

/-!
# Transporting the Szegő lower bound to `circleLebesgue`

The classical Szegő/Jensen machinery of `SzegoLowerBound` is phrased with `Real.circleAverage` over
the angular parametrization.  This module bridges those angular averages to Bochner integrals
against `circleLebesgue`, the normalized Haar probability measure used as the reference measure `m`
in the first Szegő limit theorem, so that the lower bound can be run against a general finite circle
measure and its Radon–Nikodym density.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real Polynomial
open scoped ComplexConjugate

/-- **Circle-measure ↔ angular-average bridge.**  Integrating a function of `z ∈ Circle` against the
normalized Haar (Lebesgue) probability measure equals its `circleAverage` over the angular
parametrization. -/
theorem integral_circleLebesgue_eq_circleAverage (F : ℂ → ℝ)
    (hF : AEStronglyMeasurable (fun z : Circle => F (z : ℂ)) circleLebesgue) :
    ∫ z : Circle, F (z : ℂ) ∂circleLebesgue = circleAverage F 0 1 := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  rw [circleLebesgue] at hF ⊢
  rw [integral_map (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.aemeasurable hF]
  simp only [AddCircle.homeomorphCircle_apply]
  rw [AddCircle.integral_haarAddCircle, inv_one, one_smul,
    ← AddCircle.intervalIntegral_preimage (1 : ℝ) 0, zero_add]
  have hcv : (fun a : ℝ => F ((AddCircle.toCircle (↑a : AddCircle (1 : ℝ)) : Circle) : ℂ))
      = fun a : ℝ => F (circleMap 0 1 (2 * Real.pi * a)) := by
    funext a
    congr 1
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap]
    simp
  rw [hcv]
  have hcomp := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun θ => F (circleMap 0 1 θ)) (show (2 * Real.pi) ≠ 0 by positivity)
  simp only [mul_zero, mul_one] at hcomp
  rw [hcomp, Real.circleAverage]

/-- **Transported sub-mean-value inequality.**  The `circleLebesgue`-average of `log‖q*‖` is
nonnegative, because `q* = revPoly` is a polynomial with `q*(0) = 1`: Jensen's inequality gives
`log‖q*(0)‖ = 0 ≤ average of log‖q*‖`.  This is the factor that makes `exp(∫ log‖q*‖²) ≥ 1` in the
Szegő lower bound. -/
theorem integral_log_revPoly_nonneg (c : ℕ → ℂ) (N : ℕ) :
    (0 : ℝ) ≤ ∫ z : Circle, Real.log ‖revPoly c N (z : ℂ)‖ ∂circleLebesgue := by
  have hd : Differentiable ℂ (revPoly c N) := by unfold revPoly; fun_prop
  have hana : AnalyticOnNhd ℂ (revPoly c N) (Metric.closedBall 0 |(1 : ℝ)|) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hd).mono (Set.subset_univ _)
  have h0 : revPoly c N 0 ≠ 0 := by rw [revPoly_zero]; exact one_ne_zero
  have hsub := log_norm_center_le_circleAverage_log_norm (revPoly c N) hana h0
  rw [revPoly_zero, norm_one, Real.log_one] at hsub
  have hcont : Continuous (fun z : Circle => revPoly c N (z : ℂ)) :=
    hd.continuous.comp (by fun_prop)
  have hmeas : AEStronglyMeasurable
      (fun z : Circle => Real.log ‖revPoly c N (z : ℂ)‖) circleLebesgue :=
    (Real.measurable_log.comp hcont.norm.measurable).aestronglyMeasurable
  rwa [← integral_circleLebesgue_eq_circleAverage (fun w => Real.log ‖revPoly c N w‖) hmeas] at hsub

/-- **Integrability transfer.**  A function whose angular composite `θ ↦ F(circleMap 0 1 θ)` is
interval-integrable over `[0, 2π]` is Bochner-integrable against `circleLebesgue`.  Proof: pull the
Haar measure back to the fundamental interval via the measure-preserving quotient map and rescale by
`2π`. -/
theorem integrable_circleLebesgue_of_intervalIntegrable (F : ℂ → ℝ) (hFm : Measurable F)
    (hII : IntervalIntegrable (fun θ => F (circleMap 0 1 θ)) volume 0 (2 * Real.pi)) :
    Integrable (fun z : Circle => F (z : ℂ)) circleLebesgue := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have hIoc1 : IntegrableOn (fun a : ℝ => F (circleMap 0 1 (2 * Real.pi * a)))
      (Set.Ioc 0 1) volume := by
    have h := hII.comp_mul_left (c := 2 * Real.pi) enorm_ne_top enorm_ne_top
    norm_num at h
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
  have htoC : (fun a : ℝ => F ((AddCircle.toCircle (↑a : AddCircle (1 : ℝ)) : Circle) : ℂ))
      = fun a : ℝ => F (circleMap 0 1 (2 * Real.pi * a)) := by
    funext a; congr 1
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap]; simp
  have hstep : Integrable
      (fun a : ℝ => F ((AddCircle.toCircle (↑a : AddCircle (1 : ℝ)) : Circle) : ℂ))
      (volume.restrict (Set.Ioc 0 1)) := by rw [htoC]; exact hIoc1
  have hmeasAC : Measurable (fun x : AddCircle (1 : ℝ) => F ((AddCircle.toCircle x : Circle) : ℂ)) :=
    hFm.comp (AddCircle.continuous_toCircle.subtype_val).measurable
  have hAC : Integrable
      (fun x : AddCircle (1 : ℝ) => F ((AddCircle.toCircle x : Circle) : ℂ)) volume := by
    rw [← (AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq,
      integrable_map_measure hmeasAC.aestronglyMeasurable AddCircle.measurable_mk'.aemeasurable]
    have h1 : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h1] at *
    simpa [Function.comp] using hstep
  have hvh : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  have hmeasC : Measurable (fun z : Circle => F (z : ℂ)) :=
    hFm.comp (show Continuous (fun z : Circle => (z : ℂ)) by fun_prop).measurable
  rw [circleLebesgue,
    integrable_map_measure hmeasC.aestronglyMeasurable
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.aemeasurable]
  have hfun : ((fun z : Circle => F (z : ℂ)) ∘
        ⇑(AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero))
      = fun x : AddCircle (1 : ℝ) => F ((AddCircle.toCircle x : Circle) : ℂ) := by
    funext x; rw [Function.comp_apply, AddCircle.homeomorphCircle_apply]
  rw [hfun, hvh]
  exact hAC

/-- **Log-norm of the reversed polynomial is integrable against `circleLebesgue`.**  Analytic
functions have integrable log-norm (log singularities at zeros are integrable); transported from the
mathlib circle-integrability of `log‖meromorphic‖`. -/
theorem integrable_log_revPoly (c : ℕ → ℂ) (N : ℕ) :
    Integrable (fun z : Circle => Real.log ‖revPoly c N (z : ℂ)‖) circleLebesgue := by
  have hd : Differentiable ℂ (revPoly c N) := by unfold revPoly; fun_prop
  refine integrable_circleLebesgue_of_intervalIntegrable (fun w => Real.log ‖revPoly c N w‖)
    (Real.measurable_log.comp hd.continuous.norm.measurable) ?_
  have hmero : MeromorphicOn (revPoly c N) (Metric.sphere 0 |(1 : ℝ)|) :=
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr hd).mono (Set.subset_univ _)).meromorphicOn
  exact hmero.circleIntegrable_log_norm

/-- The squared reversed polynomial is integrable against `circleLebesgue`: it is continuous on the
compact circle. -/
theorem integrable_normSq_revPoly (c : ℕ → ℂ) (N : ℕ) :
    Integrable (fun z : Circle => ‖revPoly c N (z : ℂ)‖ ^ 2) circleLebesgue := by
  have hd : Differentiable ℂ (revPoly c N) := by unfold revPoly; fun_prop
  have hcont : Continuous (fun z : Circle => ‖revPoly c N (z : ℂ)‖ ^ 2) :=
    (hd.continuous.comp (by fun_prop)).norm.pow 2
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The normalized Haar (Lebesgue) probability measure on the circle has no atoms. -/
instance circleLebesgue_noAtoms : NoAtoms circleLebesgue := by
  haveI hna : NoAtoms (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) := ⟨fun x => by
    have h := AddCircle.volume_closedBall (1 : ℝ) (x := x) 0
    rw [AddCircle.volume_eq_smul_haarAddCircle] at h
    simpa using h⟩
  constructor
  intro z
  rw [circleLebesgue, Measure.map_apply
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.measurable
    (measurableSet_singleton z)]
  have hpre : (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) ⁻¹' {z}
      = {(AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; rw [← h]; exact (Homeomorph.symm_apply_apply _ _).symm
    · intro h; rw [h]; exact Homeomorph.apply_symm_apply _ _
  rw [hpre]
  exact measure_singleton _

/-- **The reversed polynomial is nonzero almost everywhere.**  `q*` is a nonzero polynomial (value
`1` at the origin), so its zero set is finite; the circle Haar measure is atomless, hence the zero
set is null.  This gives the strict positivity `|q*|² · w > 0` a.e. needed for the Jensen step. -/
theorem revPoly_ne_zero_ae (c : ℕ → ℂ) (N : ℕ) :
    ∀ᵐ z : Circle ∂circleLebesgue, revPoly c N (z : ℂ) ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  set P : Polynomial ℂ :=
    1 - ∑ i ∈ Finset.range N, Polynomial.C (conj (c i)) * Polynomial.X ^ (N - i) with hP
  have hPeval : ∀ z : ℂ, revPoly c N z = P.eval z := fun z => by
    simp [revPoly, hP, eval_finsetSum]
  have hPne : P ≠ 0 := fun h => by
    have h0 := hPeval 0
    rw [h, eval_zero, revPoly_zero] at h0
    exact one_ne_zero h0
  have hfin : {x : ℂ | P.eval x = 0}.Finite := Polynomial.finite_setOf_isRoot hPne
  have hinj : Function.Injective (fun z : Circle => (z : ℂ)) := fun a b h => Subtype.ext h
  have hset : {z : Circle | revPoly c N (z : ℂ) = 0}
      = (fun z : Circle => (z : ℂ)) ⁻¹' {x : ℂ | P.eval x = 0} := by
    ext z; simp [hPeval (z : ℂ)]
  rw [hset]
  exact (hfin.preimage hinj.injOn).measure_zero _

end GaloisForLFunctions.HTGeometry
