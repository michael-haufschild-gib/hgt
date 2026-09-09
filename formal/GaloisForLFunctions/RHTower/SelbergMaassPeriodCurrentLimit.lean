import GaloisForLFunctions.RHTower.SelbergMaassPeriodResistance
import GaloisForLFunctions.RHTower.SelbergMaassRegularizedCusp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Full original current-period limit through nodal concentration

Periodic boundary cancellation represents the complete regulated current
integral as minus the original source acceleration paired with its value,
divided by the regulated amplitude. Original second-derivative norms give
an integrable majorant independent of the regulator. Dominated convergence
therefore supplies a finite nonnegative current limit at every positive
height, with no source-node exclusion or interchange of the pointwise
current-density limit and its integral.

Combined with original resistance classification, this proves finite joint
cost limits on zero-free periods and divergence at nodal heights with
strictly positive limiting current. A bounded nodal product requires zero
limiting current; no rate conclusion is inferred in that case. The exact
block comparison loses its regulator on its proved two-period zero-free
domain. No quotient-area quarter inequality or Xi occurrence is asserted.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory ModularGroup
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassPeriodCurrentLimit
open SelbergMaassCongruenceTrace SelbergMaassMean SelbergMaassTraceEnergy
open SelbergMaassSourceCurrents SelbergMaassTraceRegularized SelbergMaassRegulatorMass
open SelbergMaassChordEnergy SelbergMaassUnipotentPaths SelbergMaassTraceDirection
open SelbergMaassPeriodResistance SelbergMaassTraceRadial SelbergMaassCongruenceAverage
noncomputable section
variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- Complete original horizontal acceleration paired with the source. -/
def accelerationPair (z : ℂ) : ℝ :=
  ∑ q : Deck N, (dir 1 (dir 1 (field N f q)) z * (starRingEnd ℂ) (field N f q z)).re

/-- Original second-derivative norms, independent of the regulator. -/
def accelerationBound (z : ℂ) : ℝ := ∑ q : Deck N, ‖dir 1 (dir 1 (field N f q)) z‖

theorem accelerationBound_nonneg (z : ℂ) : 0 ≤ accelerationBound N f z :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem field_norm_le_amplitude (q : Deck N) (z : ℂ) :
    ‖field N f q z‖ ≤ Real.sqrt (density N f (ofComplex z)) := by
  have h := Finset.single_le_sum (s:=Finset.univ)
    (fun q _ => Complex.normSq_nonneg (field N f q z)) (Finset.mem_univ q)
  change normSq (field N f q z) ≤ density N f (ofComplex z) at h
  rw [← Complex.sq_norm] at h
  nlinarith [Real.sq_sqrt (density_nonneg N f (ofComplex z)),
    Real.sqrt_nonneg (density N f (ofComplex z)),norm_nonneg (field N f q z)]

/-- The full pairing is bounded by original acceleration times original amplitude. -/
theorem abs_accelerationPair_le (z : ℂ) :
    |accelerationPair N f z| ≤ accelerationBound N f z * Real.sqrt (density N f (ofComplex z)) := by
  calc
    _ ≤ ∑ q : Deck N, |(dir 1 (dir 1 (field N f q)) z * (starRingEnd ℂ) (field N f q z)).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q : Deck N, ‖dir 1 (dir 1 (field N f q)) z‖ * Real.sqrt (density N f (ofComplex z)) := by
      apply Finset.sum_le_sum
      intro q _
      exact (Complex.abs_re_le_norm _).trans (by
        rw [norm_mul,Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (field_norm_le_amplitude N f q z) (norm_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Original common zeros annihilate the acceleration pairing before division. -/
theorem accelerationPair_at_node (z : ℂ) (hz : density N f (ofComplex z)=0) :
    accelerationPair N f z=0 := by
  have h := abs_accelerationPair_le N f z
  simpa only [hz,Real.sqrt_zero,mul_zero,abs_nonpos_iff] using h

theorem accelerationPair_continuous {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => accelerationPair N f (point x y)) := by
  have hF (q : Deck N) : ContDiffOn ℝ 2 (field N f q) {z : ℂ | 0 < z.im} :=
    (quotientForm N f q).2.2.1.1
  have hdd (q : Deck N) : Continuous (fun x => dir 1 (dir 1 (field N f q)) (point x y)) :=
    SelbergMaassMean.slice_continuous
      (dir_contDiffOn (dir_contDiffOn (hF q) (m:=1) (by norm_num) 1) (m:=0) (by norm_num) 1).continuousOn hy
  exact continuous_finsetSum Finset.univ (fun q _ =>
    Complex.reCLM.continuous.comp
      ((hdd q).mul ((Complex.conjCLE : ℂ →L[ℝ] ℂ).continuous.comp (SelbergMaassMean.slice_continuous (hF q).continuousOn hy))))

theorem accelerationBound_continuous {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => accelerationBound N f (point x y)) := by
  apply continuous_finsetSum Finset.univ
  intro q _
  exact (SelbergMaassMean.slice_continuous
    (dir_contDiffOn (dir_contDiffOn (quotientForm N f q).2.2.1.1 (m:=1) (by norm_num) 1)
      (m:=0) (by norm_num) 1).continuousOn hy).norm

/-- Regulated original acceleration density. -/
def accelerationDensity (e : Ioi (0:ℝ)) (z : ℂ) : ℝ := accelerationPair N f z / radius N f e z

/-- Literal limiting source acceleration quotient, with Lean's zero quotient at common zeros. -/
def sourceAccelerationDensity (z : ℂ) : ℝ :=
  accelerationPair N f z / Real.sqrt (density N f (ofComplex z))

/-- One source majorant bounds every regulator, including at common zeros. -/
theorem accelerationDensity_bound (e : Ioi (0:ℝ)) (z : ℂ) :
    ‖accelerationDensity N f e z‖ ≤ accelerationBound N f z := by
  rw [Real.norm_eq_abs,accelerationDensity,abs_div,abs_of_pos (radius_pos N f e z)]
  apply (div_le_iff₀ (radius_pos N f e z)).mpr
  exact (abs_accelerationPair_le N f z).trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg (e:ℝ)))) (accelerationBound_nonneg N f z))

/-- The same source majorant bounds the literal limiting quotient. -/
theorem sourceAccelerationDensity_bound (z : ℂ) :
    ‖sourceAccelerationDensity N f z‖ ≤ accelerationBound N f z := by
  by_cases hz : density N f (ofComplex z)=0
  · simpa [sourceAccelerationDensity,hz] using accelerationBound_nonneg N f z
  · have hp := Real.sqrt_pos.mpr (lt_of_le_of_ne (density_nonneg N f (ofComplex z)) (Ne.symm hz))
    rw [Real.norm_eq_abs,sourceAccelerationDensity,abs_div,abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr (abs_accelerationPair_le N f z)

theorem accelerationDensity_continuous (e : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => accelerationDensity N f e (point x y)) :=
  (accelerationPair_continuous N f hy).div
    (SelbergMaassAugmentedDirection.radius_slice_continuous N f e hy)
    (fun x => (radius_pos N f e (point x y)).ne')

/-- The signed acceleration density has the literal pointwise limit through source nodes. -/
theorem accelerationDensity_tendsto (z : ℂ) :
    Tendsto (fun e : Ioi (0:ℝ) => accelerationDensity N f e z) regulatorAtZero
      (𝓝 (sourceAccelerationDensity N f z)) := by
  by_cases hz : density N f (ofComplex z)=0
  · simp only [accelerationDensity,sourceAccelerationDensity,accelerationPair_at_node N f z hz,zero_div]
    exact tendsto_const_nhds
  · have hr : Tendsto (fun e : Ioi (0:ℝ) => radius N f e z) regulatorAtZero
        (𝓝 (Real.sqrt (density N f (ofComplex z)))) := by
      simpa only [zero_pow (by norm_num : 2 ≠ 0),add_zero,radius] using
        ((tendsto_const_nhds (x:=density N f (ofComplex z))).add (regulator_coe_limit.pow 2)).sqrt
    exact tendsto_const_nhds.div hr
      (Real.sqrt_pos.mpr (lt_of_le_of_ne (density_nonneg N f _) (Ne.symm hz))).ne'

private theorem sq_dir {F : ℂ → ℝ} {z : ℂ} (hF : DifferentiableAt ℝ F z) (v : ℂ) :
    dir v (fun w => F w ^ 2) z = 2 * F z * dir v F z := by
  have h := congrArg (fun L => L v) (hF.hasFDerivAt.fun_mul hF.hasFDerivAt).fderiv
  change dir v (fun w => F w * F w) z = F z * dir v F z + F z * dir v F z at h
  simpa only [pow_two,two_mul,add_mul] using h

private theorem sq_second_dir {F : ℂ → ℝ} {z : ℂ} (hF : ContDiffAt ℝ 2 F z) (v : ℂ) :
    dir v (dir v (fun w => F w ^ 2)) z =
      2 * (dir v F z ^ 2 + F z * dir v (dir v F) z) := by
  have he : dir v (fun w => F w ^ 2) =ᶠ[𝓝 z] (fun w => 2 * F w * dir v F w) := by
    filter_upwards [hF.eventually (by norm_num)] with w hw
    exact sq_dir (hw.differentiableAt (by norm_num)) v
  have hd := (dir_contDiffAt hF v).differentiableAt (by norm_num)
  have hf := hF.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hh := congrArg (fun L => L v) ((hf.hasFDerivAt.const_mul 2).mul hd.hasFDerivAt).fderiv
  change fderiv ℝ (dir v (fun w => F w ^ 2)) z v = _
  rw [he.fderiv_eq]
  change dir v (fun w => 2 * F w * dir v F w) z = _
  change dir v (fun w => 2 * F w * dir v F w) z =
    2 * F z * dir v (dir v F) z + dir v F z * (2 * dir v F z) at hh
  rw [hh]
  ring

/-- Actual second density derivative retains the full source acceleration pairing. -/
theorem density_horizontal_second (z : ℍ) :
    dir 1 (dir 1 (density N f ∘ ofComplex)) (z:ℂ) =
      2*(directionalEnergy N f 1 z+accelerationPair N f (z:ℂ)) := by
  have hF (q : Deck N) : ContDiffAt ℝ 2 (field N f q) (z:ℂ) :=
    field_smooth N f q z
  have hS (q : Deck N) : ContDiffAt ℝ 2 (fun w => normSq (field N f q w)) (z:ℂ) := by
    simpa only [Complex.normSq_eq_norm_sq] using (hF q).norm_sq ℝ
  change dir 1 (dir 1 (fun w => ∑ q : Deck N, normSq (field N f q w))) (z:ℂ)=_
  rw [second_dir_sum Finset.univ (fun q _ => hS q)]
  simp_rw [normSq_second_dir (hF _) 1]
  simp only [← Finset.mul_sum,Finset.sum_add_distrib,accelerationPair,directionalEnergy,field]

/-- Horizontal radius curvature splits into retained current and exact source acceleration. -/
theorem radius_horizontal_second (e : Ioi (0:ℝ)) (z : ℍ) :
    dir 1 (dir 1 (radius N f e)) (z:ℂ)=
      horizontalCurrentDensity N f e (z:ℂ)+accelerationDensity N f e (z:ℂ) := by
  have hf := (radius_contDiffOn N f e).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have he : (fun w => radius N f e w^2)=(fun w => density N f (ofComplex w)+(e:ℝ)^2) :=
    funext (radius_sq N f e)
  have hd : dir 1 (fun w => radius N f e w^2)=dir 1 (density N f ∘ ofComplex) := by
    rw [he]
    funext w
    exact congrArg (fun L => L (1:ℂ)) (fderiv_add_const (𝕜:=ℝ)
      (f:=density N f ∘ ofComplex) (x:=w) ((e:ℝ)^2))
  have hs := sq_second_dir hf (1:ℂ)
  rw [hd,density_horizontal_second N f z] at hs
  have hE := directionalEnergy_eq N f e 1 z
  rw [horizontalCurrentDensity_eq,accelerationDensity]
  rw [← add_div]
  apply (eq_div_iff (radius_pos N f e (z:ℂ)).ne').mpr
  nlinarith

/-- Original periodic boundary cancellation represents the complete current integral by source acceleration. -/
theorem periodCurrentEnergy_eq_acceleration (e : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y) :
    periodCurrentEnergy N f e y = -(∫ x in (0:ℝ)..1, accelerationDensity N f e (point x y)) := by
  have hc := SelbergScalarHorizontalAverage.average_horizontal_second_eq_zero
    (radius_contDiffOn N f e) hy (SelbergMaassRegularizedCusp.radius_slice_periodic N f e hy)
  rw [SelbergScalarHorizontalAverage.average_eq_interval] at hc
  have he (x : ℝ) : dir 1 (dir 1 (radius N f e)) (point x y)=
      directionalRemainder N f e 1 (ofComplex (point x y))/radius N f e (point x y)+
        accelerationDensity N f e (point x y) := by
    have h := radius_horizontal_second N f e (ofComplex (point x y))
    rw [horizontalCurrentDensity_eq] at h
    simpa only [coe_ofComplex_point x hy] using h
  simp_rw [he] at hc
  rw [intervalIntegral.integral_add (path_energy_intervalIntegrable N f e hy 0 1)
    ((accelerationDensity_continuous N f e hy).intervalIntegrable 0 1)] at hc
  change periodCurrentEnergy N f e y+_=0 at hc
  linarith

/-- The literal limiting source quotient is measurable despite possible nodal discontinuities. -/
theorem sourceAccelerationDensity_measurable {y : ℝ} (hy : 0 < y) :
    Measurable (fun x => sourceAccelerationDensity N f (point x y)) :=
  (accelerationPair_continuous N f hy).measurable.div (sliceAmplitude_continuous N f hy).measurable

/-- Original C² source regularity proves actual integrability of the full limiting period expression. -/
theorem sourceAccelerationDensity_intervalIntegrable {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    IntervalIntegrable (fun x => sourceAccelerationDensity N f (point x y)) volume a b :=
  ((accelerationBound_continuous N f hy).intervalIntegrable a b).mono_fun'
    (sourceAccelerationDensity_measurable N f hy).aestronglyMeasurable
    (Eventually.of_forall (fun x => sourceAccelerationDensity_bound N f (point x y)))

/-- Full regulated acceleration integrals converge, without any common-zero exclusion. -/
theorem acceleration_integral_tendsto {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    Tendsto (fun e : Ioi (0:ℝ) => ∫ x in a..b, accelerationDensity N f e (point x y))
      regulatorAtZero (𝓝 (∫ x in a..b, sourceAccelerationDensity N f (point x y))) := by
  letI : regulatorAtZero.IsCountablyGenerated := by unfold regulatorAtZero; infer_instance
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => accelerationBound N f (point x y))
    (Eventually.of_forall (fun e => (accelerationDensity_continuous N f e hy).aestronglyMeasurable))
    (Eventually.of_forall (fun e => Eventually.of_forall (fun x _ => accelerationDensity_bound N f e (point x y))))
    ((accelerationBound_continuous N f hy).intervalIntegrable a b)
    (Eventually.of_forall (fun x _ => accelerationDensity_tendsto N f (point x y)))

/-- The original signed-acceleration functional determining complete limiting current energy. -/
def periodCurrentLimit (y : ℝ) : ℝ := -(∫ x in (0:ℝ)..1, sourceAccelerationDensity N f (point x y))

/-- Full original period current energy has a finite source-determined limit, including nodal energy. -/
theorem periodCurrentEnergy_tendsto {y : ℝ} (hy : 0 < y) :
    Tendsto (fun e : Ioi (0:ℝ) => periodCurrentEnergy N f e y) regulatorAtZero
      (𝓝 (periodCurrentLimit N f y)) := by
  simpa only [periodCurrentEnergy_eq_acceleration N f _ hy,periodCurrentLimit] using
    (acceleration_integral_tendsto N f hy 0 1).neg

/-- The complete signed source functional is nonnegative, as a limit of retained current energy. -/
theorem periodCurrentLimit_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ periodCurrentLimit N f y := by
  apply ge_of_tendsto (periodCurrentEnergy_tendsto N f hy)
  exact Eventually.of_forall (fun e => pathEnergy_nonneg N f e y (by norm_num : (0:ℝ) ≤ 1))

/-- Actual acceleration norms give a uniform-in-regulator bound for complete period current energy. -/
theorem periodCurrentEnergy_le_accelerationBound (e : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y) :
    periodCurrentEnergy N f e y ≤ ∫ x in (0:ℝ)..1, accelerationBound N f (point x y) := by
  have h := intervalIntegral.integral_mono_on (μ:=volume) (by norm_num : (0:ℝ) ≤ 1)
    (((accelerationDensity_continuous N f e hy).neg).intervalIntegrable 0 1)
    ((accelerationBound_continuous N f hy).intervalIntegrable 0 1)
    (fun x _ => (neg_le_abs (accelerationDensity N f e (point x y))).trans
      (by simpa only [Real.norm_eq_abs] using accelerationDensity_bound N f e (point x y)))
  change (∫ x in (0:ℝ)..1, -accelerationDensity N f e (point x y)) ≤ _ at h
  simpa only [intervalIntegral.integral_neg,← periodCurrentEnergy_eq_acceleration N f e hy] using h

/-- The same actual acceleration budget bounds the complete limiting current. -/
theorem periodCurrentLimit_le_accelerationBound {y : ℝ} (hy : 0 < y) :
    periodCurrentLimit N f y ≤ ∫ x in (0:ℝ)..1, accelerationBound N f (point x y) :=
  le_of_tendsto (periodCurrentEnergy_tendsto N f hy)
    (Eventually.of_forall (fun e => periodCurrentEnergy_le_accelerationBound N f e hy))

/-- A zero-free original period has an exact finite resistance/current-product limit. -/
theorem periodCost_tendsto_of_zero_free {y : ℝ} (hy : 0 < y)
    (hp : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x y))) :
    Tendsto (fun e : Ioi (0:ℝ) => periodCost N f e y) regulatorAtZero
      (𝓝 (unregularizedPeriodResistance N f y * periodCurrentLimit N f y)) :=
  (periodResistance_tendsto_of_zero_free N f hy hp).mul (periodCurrentEnergy_tendsto N f hy)

/-- At a nodal height, strictly positive limiting current forces divergence of the full path product. -/
theorem periodCost_tendsto_atTop_of_node (z : ℍ) (hz : density N f z=0)
    (hE : 0 < periodCurrentLimit N f z.im) :
    Tendsto (fun e : Ioi (0:ℝ) => periodCost N f e z.im) regulatorAtZero atTop :=
  (periodResistance_tendsto_atTop_of_node N f z hz).atTop_mul_pos hE
    (periodCurrentEnergy_tendsto N f z.im_pos)

/-- A bounded original nodal product requires exact vanishing of the complete limiting current functional. -/
theorem periodCurrentLimit_eq_zero_of_node_bddCost (z : ℍ) (hz : density N f z=0)
    (hb : BddAbove (range (fun e : Ioi (0:ℝ) => periodCost N f e z.im))) :
    periodCurrentLimit N f z.im=0 := by
  by_contra hn
  have hp := lt_of_le_of_ne (periodCurrentLimit_nonneg N f z.im_pos) (Ne.symm hn)
  exact not_bddAbove_of_tendsto_atTop (periodCost_tendsto_atTop_of_node N f z hz hp) hb

/-- When the source limiting current is positive, the full period product diverges exactly at nodal heights. -/
theorem periodCost_tendsto_atTop_iff_node {y : ℝ} (hy : 0 < y)
    (hE : 0 < periodCurrentLimit N f y) :
    Tendsto (fun e : Ioi (0:ℝ) => periodCost N f e y) regulatorAtZero atTop ↔
      ∃ x ∈ Icc (0:ℝ) 1, density N f (ofComplex (point x y))=0 := by
  constructor
  · intro ht
    by_contra hn
    have hp (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
        0 < density N f (ofComplex (point x y)) :=
      lt_of_le_of_ne (density_nonneg N f _) (Ne.symm (fun hz => hn ⟨x,hx,hz⟩))
    exact not_tendsto_nhds_of_tendsto_atTop ht _ (periodCost_tendsto_of_zero_free N f hy hp)
  · intro hn
    exact ((periodResistance_tendsto_atTop_iff_node N f hy).mpr hn).atTop_mul_pos hE
      (periodCurrentEnergy_tendsto N f hy)

/-- Literal limiting product, used with the separately proved period zero-freeness conditions. -/
def limitingPeriodCost (y : ℝ) : ℝ := unregularizedPeriodResistance N f y * periodCurrentLimit N f y

/-- Both zero-free original heights give the exact regulator-free complete block cost. -/
theorem blockPathCost_tendsto_of_zero_free (z : ℍ)
    (hp : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x z.im)))
    (hq : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x (S⁻¹ • z).im))) :
    Tendsto (fun e : Ioi (0:ℝ) => blockPathCost N f e z) regulatorAtZero
      (𝓝 (parameterMoment N * (limitingPeriodCost N f z.im + limitingPeriodCost N f (S⁻¹ • z).im))) := by
  have h := ((periodCost_tendsto_of_zero_free N f z.im_pos hp).add
    (periodCost_tendsto_of_zero_free N f (S⁻¹ • z).im_pos hq)).const_mul (parameterMoment N)
  simpa only [blockPathCost_eq_two_periods,parameterMoment_eq,limitingPeriodCost] using h

/-- Exact source comparison after regulator removal on its proved zero-free two-period domain. -/
theorem density_le_mean_add_limiting_periods (z : ℍ)
    (hp : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x z.im)))
    (hq : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x (S⁻¹ • z).im))) :
    density N f z ≤ (Fintype.card (Deck N):ℝ)*normSq (sourceMean N f z)+
      16*density N f z*parameterMoment N*
        (limitingPeriodCost N f z.im+limitingPeriodCost N f (S⁻¹ • z).im) := by
  have hm : Tendsto (fun e : Ioi (0:ℝ) => density N f z+(e:ℝ)^2) regulatorAtZero (𝓝 (density N f z)) := by
    simpa using (tendsto_const_nhds (x:=density N f z)).add (regulator_coe_limit.pow 2)
  have h := (tendsto_const_nhds (x:=(Fintype.card (Deck N):ℝ)*normSq (sourceMean N f z))).add
    ((hm.const_mul 16).mul (blockPathCost_tendsto_of_zero_free N f z hp hq))
  have hle := ge_of_tendsto h (Eventually.of_forall (fun e => density_le_mean_add_pathCost N f e z))
  simpa only [mul_assoc] using hle

/-- Mean-zero positive original sources obey the sharper limiting two-period requirement. -/
theorem limiting_period_cost_lower_of_mean_zero (z : ℍ) (hz : 0 < density N f z)
    (hm : sourceMean N f z=0)
    (hp : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x z.im)))
    (hq : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x (S⁻¹ • z).im))) :
    1 ≤ (4/3:ℝ)*(N:ℝ)*(2*(N:ℝ)+1)*
      (limitingPeriodCost N f z.im+limitingPeriodCost N f (S⁻¹ • z).im) := by
  have h := density_le_mean_add_limiting_periods N f z hp hq
  simp only [hm,normSq_zero,mul_zero,zero_add,parameterMoment_eq] at h
  nlinarith

end
end GaloisForLFunctions.RHTower.SelbergMaassPeriodCurrentLimit
