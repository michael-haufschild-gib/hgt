import GaloisForLFunctions.HTGeometry.SzegoLowerBound
import GaloisForLFunctions.HTGeometry.RieszBrothersReduction
import GaloisForLFunctions.HTGeometry.SzegoConcretePolynomial
import GaloisForLFunctions.HTGeometry.SzegoFirstLimitInterface

/-!
# Transporting the Szegő lower bound to `circleLebesgue`

The classical Szegő/Jensen machinery of `SzegoLowerBound` is phrased with `Real.circleAverage` over
the angular parametrization.  This module bridges those angular averages to Bochner integrals
against `circleLebesgue`, the normalized Haar probability measure used as the reference measure `m`
in the first Szegő limit theorem, so that the lower bound can be run against a general finite circle
measure and its Radon–Nikodym density.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real Polynomial InnerProductSpace
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
    simpa [Function.comp] using! hstep
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
instance circleLebesgue_noAtoms : NullSingletonClass circleLebesgue := by
  haveI hna : NullSingletonClass (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) := ⟨fun x => by
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

open scoped ENNReal in
/-- **The general Szegő inequality.**  For any finite circle measure `μ` and any level `N`, the Szegő
geometric mean of the Radon–Nikodym density is a lower bound for `∫ |q*|² dμ`, where `q*` is the
reversed polynomial (value `1` at the origin).  Drop the singular part, express the absolutely
continuous part via the density, and apply Jensen's inequality (with the sub-mean-value factor
`∫ log‖q*‖ ≥ log‖q*(0)‖ = 0`) against the reference probability measure. -/
theorem szegoGeometricMean_le_integral_normSq_revPoly
    (mu : Measure Circle) [IsFiniteMeasure mu] (c : ℕ → ℂ) (N : ℕ) :
    szegoGeometricMean circleLebesgue (mu.rnDeriv circleLebesgue)
      ≤ ∫ z : Circle, ‖revPoly c N (z : ℂ)‖ ^ 2 ∂mu := by
  classical
  set w := mu.rnDeriv circleLebesgue with hw
  set Q : Circle → ℝ := fun z => ‖revPoly c N (z : ℂ)‖ ^ 2 with hQ
  have hQnonneg : ∀ z, 0 ≤ Q z := fun z => by positivity
  have hQint : Integrable Q mu := by
    have hd : Differentiable ℂ (revPoly c N) := by unfold revPoly; fun_prop
    have hcont : Continuous Q := (hd.continuous.comp (by fun_prop)).norm.pow 2
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  by_cases hgood : (∀ᵐ z ∂circleLebesgue, 0 < w z ∧ w z < ∞) ∧
      Integrable (fun z => Real.log (w z).toReal) circleLebesgue
  · rw [szegoGeometricMean_eq_exp_integral circleLebesgue w hgood.1 hgood.2]
    obtain ⟨hpos, hlogint⟩ := hgood
    set W : Circle → ℝ := fun z => (w z).toReal with hW
    set H : Circle → ℝ := fun z => Q z * W z with hH
    have hWint : Integrable W circleLebesgue := Measure.integrable_toReal_rnDeriv
    have hd : Differentiable ℂ (revPoly c N) := by unfold revPoly; fun_prop
    have hcontQ : Continuous Q :=
      (hd.continuous.comp (by fun_prop : Continuous fun z : Circle => (z : ℂ))).norm.pow 2
    obtain ⟨z0, hz0⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcontQ.continuousOn
    have hQbdd : ∀ z, ‖Q z‖ ≤ Q z0 := fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hQnonneg z)]; exact hz0.2 (Set.mem_univ z)
    have hHint : Integrable H circleLebesgue :=
      hWint.bdd_mul hcontQ.aestronglyMeasurable (Filter.Eventually.of_forall hQbdd)
    have hHpos : ∀ᵐ z ∂circleLebesgue, 0 < H z := by
      filter_upwards [revPoly_ne_zero_ae c N, hpos] with z hz hwz
      have h1 : 0 < Q z := by rw [hQ]; positivity
      have h2 : 0 < W z := ENNReal.toReal_pos hwz.1.ne' hwz.2.ne
      exact mul_pos h1 h2
    have hlogH : (fun z => Real.log (H z)) =ᵐ[circleLebesgue]
        fun z => Real.log (Q z) + Real.log (W z) := by
      filter_upwards [hHpos, revPoly_ne_zero_ae c N, hpos] with z hHz hz hwz
      have h1 : Q z ≠ 0 := by rw [hQ]; positivity
      have h2 : W z ≠ 0 := (ENNReal.toReal_pos hwz.1.ne' hwz.2.ne).ne'
      rw [hH, Real.log_mul h1 h2]
    have hlogQ : (fun z => Real.log (Q z)) =ᵐ[circleLebesgue]
        fun z => 2 * Real.log ‖revPoly c N (z : ℂ)‖ := by
      filter_upwards with z
      rw [hQ, Real.log_pow]; ring
    have hlogQint : Integrable (fun z => Real.log (Q z)) circleLebesgue :=
      (((integrable_log_revPoly c N).const_mul 2)).congr hlogQ.symm
    have hlogQnonneg : 0 ≤ ∫ z, Real.log (Q z) ∂circleLebesgue := by
      rw [integral_congr_ae hlogQ, integral_const_mul]
      have := integral_log_revPoly_nonneg c N
      positivity
    have hlogHint : Integrable (fun z => Real.log (H z)) circleLebesgue :=
      (hlogQint.add hlogint).congr hlogH.symm
    have hjensen : Real.exp (∫ z, Real.log (H z) ∂circleLebesgue) ≤ ∫ z, H z ∂circleLebesgue := by
      have hexpH : (fun z => Real.exp (Real.log (H z))) =ᵐ[circleLebesgue] H := by
        filter_upwards [hHpos] with z hz; rw [Real.exp_log hz]
      have hmap := convexOn_exp.map_integral_le (μ := circleLebesgue)
        (f := fun z => Real.log (H z)) Real.continuous_exp.continuousOn isClosed_univ
        (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hlogHint
        (hHint.congr hexpH.symm)
      calc Real.exp (∫ z, Real.log (H z) ∂circleLebesgue)
          ≤ ∫ z, Real.exp (Real.log (H z)) ∂circleLebesgue := hmap
        _ = ∫ z, H z ∂circleLebesgue := integral_congr_ae hexpH
    have hlogHge : ∫ z, Real.log (W z) ∂circleLebesgue ≤ ∫ z, Real.log (H z) ∂circleLebesgue := by
      rw [integral_congr_ae hlogH, integral_add hlogQint hlogint]
      linarith [hlogQnonneg]
    have hstep1 : Real.exp (∫ z, Real.log (W z) ∂circleLebesgue) ≤ ∫ z, H z ∂circleLebesgue :=
      le_trans (Real.exp_le_exp.mpr hlogHge) hjensen
    have hWD : ∫ z, H z ∂circleLebesgue = ∫ z, Q z ∂(circleLebesgue.withDensity w) := by
      rw [integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv mu circleLebesgue)
        (Measure.rnDeriv_lt_top mu circleLebesgue)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show Q z * (w z).toReal = (w z).toReal • Q z
      rw [smul_eq_mul, mul_comm]
    have hdrop : ∫ z, Q z ∂(circleLebesgue.withDensity w) ≤ ∫ z, Q z ∂mu :=
      integral_mono_measure (Measure.withDensity_rnDeriv_le mu circleLebesgue)
        (Filter.Eventually.of_forall hQnonneg) hQint
    calc Real.exp (∫ z, Real.log (W z) ∂circleLebesgue)
        ≤ ∫ z, H z ∂circleLebesgue := hstep1
      _ = ∫ z, Q z ∂(circleLebesgue.withDensity w) := hWD
      _ ≤ ∫ z, Q z ∂mu := hdrop
  · rw [szegoGeometricMean, dif_neg hgood]
    exact integral_nonneg hQnonneg

/-- **The Szegő lower bound (first limit theorem, `≥` half).**  For any finite circle measure the
Szegő geometric mean of its Radon–Nikodym density is a lower bound for the infimum of the squared
monic orthogonal polynomial norms `⨅ₙ ‖Φₙ₊₁‖²`.  Each `‖Φ_N‖²` equals `∫|q*|²dμ` for the reversed
polynomial and the general Szegő inequality bounds every such integral below by the geometric
mean. -/
theorem szegoGeometricMean_le_ciInf_normSq_gramSchmidt
    (mu : Measure Circle) [IsFiniteMeasure mu] :
    szegoGeometricMean circleLebesgue (mu.rnDeriv circleLebesgue)
      ≤ ⨅ N, ‖gramSchmidt ℂ (circleMonomialLp mu) (N + 1)‖ ^ 2 := by
  apply le_ciInf
  intro N
  obtain ⟨c, hc⟩ := normSq_gramSchmidt_circleMonomial_eq_integral_revPoly mu (N + 1)
  rw [hc]
  exact szegoGeometricMean_le_integral_normSq_revPoly mu c (N + 1)

end GaloisForLFunctions.HTGeometry
