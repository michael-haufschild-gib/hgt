import GaloisForLFunctions.RHTower.ThetaBVWeilForm
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceUnconditional
import GaloisForLFunctions.RHTower.HedenmalmQuantileNormalForm

/-! # Exact singular transport of the full arithmetic Weil form

The theta quantile moves the complete prime--Gamma difference form to the
unit interval. Every prime power remains its own nonlinear shift, the Gamma
continuum remains an integral of shifts, and both poles retain their signs.
The argument uses measure transport, with no bound on quantile speed.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower.ThetaQuantileArithmetic
open CHMDDoobGraph HedenmalmThetaSource HedenmalmQuantile

def shift (h t : ℝ) : ℝ := thetaSource.cdfFun (thetaSource.quantileFun t+h)
def pull (v : ℝ → ℝ) (t : ℝ) : ℝ := v (thetaSource.quantileFun t)

theorem shift_mem (h t : ℝ) : shift h t ∈ Ioo (0 : ℝ) 1 := thetaSource.cdfFun_mem_Ioo _

theorem pull_shift (v : ℝ → ℝ) (h t : ℝ) :
    pull v (shift h t) = v (thetaSource.quantileFun t+h) := by
  simp only [pull, shift, thetaSource.quantile_cdfFun]

def massWeight (t : ℝ) : ℝ :=
  massDensity (thetaSource.quantileFun t)/thetaSource.normalized (thetaSource.quantileFun t)

def sinhWeight (t : ℝ) : ℝ :=
  (riemannKernelReal (thetaSource.quantileFun t)*Real.sinh (thetaSource.quantileFun t/2))/
    thetaSource.normalized (thetaSource.quantileFun t)

def archWeight (h t : ℝ) : ℝ :=
  CHMDDoobGraph.archWeight (h, thetaSource.quantileFun t)/
    thetaSource.normalized (thetaSource.quantileFun t)

def primeWeight (n : ℕ) (t : ℝ) : ℝ :=
  CHMDDoobGraph.primeWeight n (thetaSource.quantileFun t)/
    thetaSource.normalized (thetaSource.quantileFun t)

def archEnergy (V : ℝ → ℝ) : ℝ :=
  ∫ h in Ioi (0 : ℝ), ∫ t in Ioo (0 : ℝ) 1, archWeight h t*(V t-V (shift h t))^2

def primeEnergy (V : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1, primeWeight n t*(V t-V (shift (Real.log n) t))^2

def mass (V : ℝ → ℝ) : ℝ := ∫ t in Ioo (0 : ℝ) 1, massWeight t*V t^2
def coshMoment (V : ℝ → ℝ) : ℝ := ∫ t in Ioo (0 : ℝ) 1, massWeight t*V t
def sinhMoment (V : ℝ → ℝ) : ℝ := ∫ t in Ioo (0 : ℝ) 1, sinhWeight t*V t

/-- The complete compactified form; no prime, polar or Gamma term is discarded. -/
def weilEnergy (V : ℝ → ℝ) : ℝ :=
  archEnergy V + ∑' n, primeEnergy V n - mass V +
    2*coshMoment V^2 - 2*sinhMoment V^2

theorem integral_quantile_weight (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f x) = ∫ t in Ioo (0 : ℝ) 1,
      f (thetaSource.quantileFun t)/thetaSource.normalized (thetaSource.quantileFun t) := by
  rw [integral_comp_quantile thetaSource (fun x => f x/thetaSource.normalized x)
    (hf.div thetaSource.measurable_normalized).aestronglyMeasurable]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only [Pi.div_apply]
    rw [smul_eq_mul]
    field_simp [(thetaSource.normalized_pos x).ne']

theorem integrable_quantile_weight (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f) :
    IntegrableOn (fun t =>
      f (thetaSource.quantileFun t)/thetaSource.normalized (thetaSource.quantileFun t))
      (Ioo (0 : ℝ) 1) := by
  apply (thetaSource.integrableOn_comp_quantileFun_iff
    (hf.div thetaSource.measurable_normalized).aestronglyMeasurable).mpr
  apply hi.congr
  exact Eventually.of_forall fun x => by
    dsimp only [Pi.div_apply]
    rw [smul_eq_mul]
    field_simp [(thetaSource.normalized_pos x).ne']

theorem integrable_quantile_weight_prod (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (hi : Integrable f archBase) :
    Integrable (fun e : ℝ × ℝ =>
      f (e.1, thetaSource.quantileFun e.2)/thetaSource.normalized (thetaSource.quantileFun e.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hm : Measurable (fun e : ℝ × ℝ =>
      f (e.1, thetaSource.quantileFun e.2)/thetaSource.normalized (thetaSource.quantileFun e.2)) :=
    (hf.comp (measurable_fst.prodMk (thetaSource.measurable_quantileFun.comp measurable_snd))).div
      (thetaSource.measurable_normalized.comp (thetaSource.measurable_quantileFun.comp measurable_snd))
  have hparts := (integrable_prod_iff hf.aestronglyMeasurable).mp hi
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hparts.1] with h hh
    exact integrable_quantile_weight (fun x => f (h,x))
      (hf.comp (measurable_const.prodMk measurable_id)) hh
  · apply hparts.2.congr
    filter_upwards [] with h
    rw [integral_quantile_weight (fun x => ‖f (h,x)‖)
      (hf.comp (measurable_const.prodMk measurable_id)).norm]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t _
    dsimp only
    rw [norm_div, Real.norm_of_nonneg (thetaSource.normalized_pos _).le]

/-- Absolute admission of the transported Gamma continuum, including its diagonal singularity. -/
theorem integrable_arch_pull (v : ℝ → ℝ) (hv : BoundedVariationOn v univ) :
    Integrable (fun e : ℝ × ℝ => archWeight e.1 e.2*
      (pull v e.2-pull v (shift e.1 e.2))^2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hm := GaloisForLFunctions.HTGeometry.measurable_of_boundedVariation_univ hv
  have hi := integrable_quantile_weight_prod _
    (measurable_archWeight.mul ((measurable_difference hm).pow_const 2))
      (bv_integrable_arch_weighted_sq hv)
  apply hi.congr
  filter_upwards [] with e
  rw [pull_shift]
  dsimp [archWeight, pull, difference, left, right]
  ring

theorem archEnergy_pull (v : ℝ → ℝ) (hv : Measurable v) :
    archEnergy (pull v) = phiDoobArchJumpEnergy v := by
  unfold archEnergy phiDoobArchJumpEnergy
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h _
  dsimp only
  rw [← integral_const_mul]
  have hm : Measurable (fun x => archLevyDensity h*phiDoobArchShiftJump v h x) := by
    have hθ := continuous_riemannKernelReal.measurable
    unfold phiDoobArchShiftJump
    fun_prop
  rw [integral_quantile_weight _ hm]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t _
  dsimp only
  rw [pull_shift]
  dsimp [archWeight, CHMDDoobGraph.archWeight, pull, phiDoobArchShiftJump]
  ring

theorem primeEnergy_pull (v : ℝ → ℝ) (hv : Measurable v) (n : ℕ) :
    primeEnergy (pull v) n = ∫ x, phiDoobPrimeJump v n x := by
  have hm : Measurable (phiDoobPrimeJump v n) := by
    have hθ := continuous_riemannKernelReal.measurable
    unfold phiDoobPrimeJump
    fun_prop
  rw [integral_quantile_weight _ hm]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t _
  dsimp only
  rw [pull_shift]
  dsimp [primeWeight, CHMDDoobGraph.primeWeight, pull, phiDoobPrimeJump]
  ring

theorem integrable_prime_pull (v : ℝ → ℝ) (hv : BoundedVariationOn v univ) (n : ℕ) :
    IntegrableOn (fun t => primeWeight n t*(pull v t-pull v (shift (Real.log n) t))^2)
      (Ioo (0 : ℝ) 1) := by
  have hm := GaloisForLFunctions.HTGeometry.measurable_of_boundedVariation_univ hv
  have hi := (integrable_sum_measure_iff.mp (bv_memLp_prime_difference hv).integrable_sq).1 n
  rw [CHMDDoobGraph.primeMeasure,
    integrable_map_measure ((measurable_difference hm).pow_const 2).aestronglyMeasurable (by fun_prop),
    integrable_weighted_iff volume (continuous_primeWeight n).measurable
      (Eventually.of_forall (primeWeight_nonneg n))] at hi
  have hp : Measurable (phiDoobPrimeJump v n) := by
    have hθ := continuous_riemannKernelReal.measurable
    unfold phiDoobPrimeJump
    fun_prop
  have hq := integrable_quantile_weight _ hp hi
  apply hq.congr
  filter_upwards [] with t
  rw [pull_shift]
  dsimp [primeWeight, CHMDDoobGraph.primeWeight, pull, phiDoobPrimeJump]
  ring

/-- Absolute prime summability is paid before the transported series is evaluated. -/
theorem summable_primeEnergy_pull (v : ℝ → ℝ) (hv : BoundedVariationOn v univ) :
    Summable (primeEnergy (pull v)) := by
  have hm := GaloisForLFunctions.HTGeometry.measurable_of_boundedVariation_univ hv
  have hs := (integrable_sum_measure_iff.mp (bv_memLp_prime_difference hv).integrable_sq).2
  simpa only [Real.norm_of_nonneg (sq_nonneg _), integral_prime_sq_measurable hm,
    ← primeEnergy_pull v hm] using hs

theorem mass_pull (v : ℝ → ℝ) (hv : Measurable v) :
    mass (pull v) = phiDoobCoshMass (fun x => v x^2) := by
  have hm : Measurable (fun x => phiDoobTest (fun y => v y^2) x*Real.cosh (x/2)) := by
    have hθ := continuous_riemannKernelReal.measurable
    unfold phiDoobTest
    fun_prop
  rw [phiDoobCoshMass, integral_quantile_weight _ hm]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t _
  dsimp [massWeight, massDensity, pull, phiDoobTest]
  ring

theorem coshMoment_pull (v : ℝ → ℝ) (hv : Measurable v) :
    coshMoment (pull v) = phiDoobCoshMass v := by
  have hm : Measurable (fun x => phiDoobTest v x*Real.cosh (x/2)) := by
    have hθ := continuous_riemannKernelReal.measurable
    unfold phiDoobTest
    fun_prop
  rw [phiDoobCoshMass, integral_quantile_weight _ hm]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t _
  dsimp [massWeight, massDensity, pull, phiDoobTest]
  ring

theorem sinhMoment_pull (v : ℝ → ℝ) (hv : Measurable v) :
    sinhMoment (pull v) = phiDoobSinhMass v := by
  have hm : Measurable (fun x => phiDoobTest v x*Real.sinh (x/2)) := by
    have hθ := continuous_riemannKernelReal.measurable
    unfold phiDoobTest
    fun_prop
  rw [phiDoobSinhMass, integral_quantile_weight _ hm]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t _
  dsimp [sinhWeight, pull, phiDoobTest]
  ring

/-- Singular quantile transport preserves the complete original arithmetic form on all BV profiles. -/
theorem weilEnergy_pull (v : ℝ → ℝ) (hv : BoundedVariationOn v univ) :
    weilEnergy (pull v) = sourceWeilEnergy (bvLift v hv) := by
  have hm := GaloisForLFunctions.HTGeometry.measurable_of_boundedVariation_univ hv
  rw [weilEnergy, archEnergy_pull v hm, mass_pull v hm, coshMoment_pull v hm,
    sinhMoment_pull v hm, sourceWeilEnergy_bvLift]
  simp only [primeEnergy_pull v hm]

theorem weilEnergy_congr {V W : ℝ → ℝ} (h : EqOn V W (Ioo (0 : ℝ) 1)) :
    weilEnergy V = weilEnergy W := by
  have he (a : ℝ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      (V t-V (shift a t))^2 = (W t-W (shift a t))^2 := by
    rw [h ht, h (shift_mem a t)]
  have ha : archEnergy V = archEnergy W := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro a _
    exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [he a t ht]
  have hp (n : ℕ) : primeEnergy V n = primeEnergy W n :=
    setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [he (Real.log n) t ht]
  have hm : mass V = mass W :=
    setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [h ht]
  have hc : coshMoment V = coshMoment W :=
    setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [h ht]
  have hs : sinhMoment V = sinhMoment W :=
    setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [h ht]
  simp only [weilEnergy, ha, hp, hm, hc, hs]

theorem boundedVariation_cdf_pullback (V : ℝ → ℝ)
    (hV : BoundedVariationOn V (Icc (0 : ℝ) 1)) :
    BoundedVariationOn (fun x => V (thetaSource.cdfFun x)) univ := by
  apply ne_top_of_le_ne_top hV
  exact eVariationOn.comp_le_of_monotoneOn V thetaSource.cdfFun
    (thetaSource.strictMono_cdfFun.monotone.monotoneOn univ)
      (fun x _ => ⟨(thetaSource.cdfFun_mem_Ioo x).1.le, (thetaSource.cdfFun_mem_Ioo x).2.le⟩)

/-- Every BV profile on the compact interval is a genuine full arithmetic source vector. -/
theorem weilEnergy_compactBV (V : ℝ → ℝ) (hV : BoundedVariationOn V (Icc (0 : ℝ) 1)) :
    weilEnergy V = sourceWeilEnergy
      (bvLift (fun x => V (thetaSource.cdfFun x)) (boundedVariation_cdf_pullback V hV)) := by
  rw [← weilEnergy_pull]
  apply weilEnergy_congr
  intro t ht
  simp only [pull, thetaSource.cdfFun_quantile ht]

/-- All polynomial responses of compact BV data have the same exact full-source transport. -/
theorem weilEnergy_polynomial (V : ℝ → ℝ) (hV : BoundedVariationOn V (Icc (0 : ℝ) 1))
    (P : Polynomial ℝ) :
    weilEnergy (fun t => P.eval (V t)) = sourceWeilEnergy
      (bvLift (fun x => P.eval (V (thetaSource.cdfFun x)))
        (boundedVariation_polynomial_comp (boundedVariation_cdf_pullback V hV) P)) := by
  rw [← weilEnergy_pull]
  apply weilEnergy_congr
  intro t ht
  simp only [pull, thetaSource.cdfFun_quantile ht]

end RHTower.ThetaQuantileArithmetic
