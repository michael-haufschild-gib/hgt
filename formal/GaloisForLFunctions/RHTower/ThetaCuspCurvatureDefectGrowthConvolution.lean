import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthTransferFlow
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthTransferEnvelope
import Mathlib.MeasureTheory.Group.IntegralConvolution

/-!
# Source convolution sectors for the curvature growth transfer

The actual k-fold tilted source has support at least 3k. Its moments through
order eight equal the finite logarithmic convolution moments, so sectors
k >= 3 have nonnegative transfer and an explicit eighth-moment envelope.
The moment-product inequality controls every convolution order by its
mass and one moment. The literal dominant single transfer vanishes and
its full self-pair transfer is positive. Complete signed absorption remains open.
-/

namespace RHTower.ThetaCuspDefect
open MeasureTheory
open scoped BigOperators
noncomputable section


private theorem pow_add_as_moment_sum (s t : ℝ) (j : ℕ) :
    (s+t)^j=∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*(s^i*t^(j-i)) := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem integrable_pow_measure_conv (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ)
    (hν : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) ν) (j : ℕ) :
    Integrable (fun t : ℝ => t^j) (μ ∗ ν) := by
  have hi : Integrable (fun z : ℝ×ℝ => (z.1+z.2)^j) (μ.prod ν) := by
    simp_rw [pow_add_as_moment_sum]
    exact integrable_finsetSum (Finset.range (j+1)) (fun i _ =>
      ((hμ i).mul_prod (hν (j-i))).const_mul (j.choose i:ℝ))
  unfold Measure.conv
  exact (integrable_map_measure (by fun_prop) (by fun_prop)).mpr hi

def measureMoment (μ : Measure ℝ) (j : ℕ) : ℝ := ∫ t : ℝ, t^j ∂μ

theorem measureMoment_conv (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ)
    (hν : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) ν) (j : ℕ) :
    measureMoment (μ ∗ ν) j=momentConvolution (measureMoment μ) (measureMoment ν) j := by
  unfold measureMoment momentConvolution Measure.conv
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [pow_add_as_moment_sum]
  rw [integral_finsetSum _ (fun i _ =>
    ((hμ i).mul_prod (hν (j-i))).const_mul (j.choose i:ℝ))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul,integral_prod_mul (μ := μ) (ν := ν)
    (fun s : ℝ => s^i) (fun t : ℝ => t^(j-i))]
  ring

theorem ae_add_lower_measure_conv (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a b : ℝ} (hμ : ∀ᵐ t ∂μ, a ≤ t) (hν : ∀ᵐ t ∂ν, b ≤ t) :
    ∀ᵐ t ∂(μ ∗ ν), a+b ≤ t := by
  rw [Measure.conv,ae_map_iff (by fun_prop) measurableSet_Ici]
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_const (by fun_prop))]
  filter_upwards [hμ] with s hs
  filter_upwards [hν] with t ht
  exact add_le_add hs ht

def sourceConvolutionMeasure (q : ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | k+1 => thetaCuspHigherLikelihoodTiltedMeasure q ∗ sourceConvolutionMeasure q k

theorem sourceConvolutionMeasure_finite {q : ℝ} (hq : 0 < q) (k : ℕ) :
    IsFiniteMeasure (sourceConvolutionMeasure q k) := by
  letI := thetaCuspHigherLikelihoodTiltedMeasure_finite hq
  induction k with
  | zero => change IsFiniteMeasure (Measure.dirac (0:ℝ)); infer_instance
  | succ k ih =>
      letI := ih
      change IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure q ∗ sourceConvolutionMeasure q k)
      infer_instance

theorem integrable_pow_sourceConvolutionMeasure {q : ℝ} (hq : 0 < q) (k j : ℕ) :
    Integrable (fun t : ℝ => t^j) (sourceConvolutionMeasure q k) := by
  letI := thetaCuspHigherLikelihoodTiltedMeasure_finite hq
  induction k generalizing j with
  | zero =>
      change Integrable (fun t : ℝ => t^j) (Measure.dirac 0)
      exact integrable_dirac (by simp)
  | succ k ih =>
      letI := sourceConvolutionMeasure_finite hq k
      exact integrable_pow_measure_conv _ _
        (fun i => integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure i hq) ih j

theorem measureMoment_sourceConvolutionMeasure {q : ℝ} (hq : 0 < q) (k : ℕ)
    {j : ℕ} (hj : j ≤ 8) :
    measureMoment (sourceConvolutionMeasure q k) j=
      spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k j := by
  letI := thetaCuspHigherLikelihoodTiltedMeasure_finite hq
  induction k generalizing j with
  | zero =>
      by_cases hj0 : j=0
      · subst j; norm_num [sourceConvolutionMeasure,measureMoment,spectralPowerMoment]
      · simp [sourceConvolutionMeasure,measureMoment,spectralPowerMoment,
          PowerSeries.coeff_one,hj0]
  | succ k ih =>
      letI := sourceConvolutionMeasure_finite hq k
      rw [sourceConvolutionMeasure,measureMoment_conv _ _
        (fun i => integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure i hq)
        (integrable_pow_sourceConvolutionMeasure hq k),
        spectralPowerMoment_succ _ k hj]
      unfold momentConvolution
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih (by omega : j-i ≤ 8)]
      rfl

theorem ae_lower_sourceConvolutionMeasure {q : ℝ} (hq : 0 < q) (k : ℕ) :
    ∀ᵐ t ∂sourceConvolutionMeasure q k, 3*(k:ℝ) ≤ t := by
  letI := thetaCuspHigherLikelihoodTiltedMeasure_finite hq
  induction k with
  | zero => simp [sourceConvolutionMeasure]
  | succ k ih =>
      letI := sourceConvolutionMeasure_finite hq k
      have hs := ae_add_lower_measure_conv
        (thetaCuspHigherLikelihoodTiltedMeasure q) (sourceConvolutionMeasure q k)
        (ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure q) ih
      change ∀ᵐ t ∂(thetaCuspHigherLikelihoodTiltedMeasure q ∗ sourceConvolutionMeasure q k),
        3*((k+1:ℕ):ℝ) ≤ t
      filter_upwards [hs] with t ht
      push_cast
      linarith

theorem integrable_growthTransferKernel (q : ℝ) (μ : Measure ℝ)
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ) :
    Integrable (growthTransferKernel q) μ := by
  have he : growthTransferKernel q=(fun t => growthTransferFunctional q (fun j => t^j)) := by
    funext t
    exact (growthTransferFunctional_point q t).symm
  rw [he]
  unfold growthTransferFunctional
  exact integrable_finsetSum (Finset.range 6) (fun j _ =>
    ((hμ (j+2)).const_mul _).add ((hμ (j+3)).const_mul _))

theorem integral_growthTransferKernel (q : ℝ) (μ : Measure ℝ)
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ) :
    (∫ t : ℝ, growthTransferKernel q t ∂μ)=growthTransferFunctional q (measureMoment μ) := by
  simp_rw [← growthTransferFunctional_point]
  unfold growthTransferFunctional
  erw [integral_finsetSum (Finset.range 6) (fun j _ =>
    ((hμ (j+2)).const_mul _).add ((hμ (j+3)).const_mul _))]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.add_apply]
  rw [integral_add ((hμ (j+2)).const_mul _) ((hμ (j+3)).const_mul _)]
  simp only [integral_const_mul,measureMoment]

theorem integral_growthTransferKernel_source {q : ℝ} (hq : 0 < q) (k : ℕ) :
    (∫ t : ℝ, growthTransferKernel q t ∂sourceConvolutionMeasure q k)=
      growthTransferFunctional q (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k) := by
  rw [integral_growthTransferKernel q _ (integrable_pow_sourceConvolutionMeasure hq k)]
  unfold growthTransferFunctional
  apply Finset.sum_congr rfl
  intro j hj
  have hj5 : j ≤ 5 := by have := Finset.mem_range.mp hj; omega
  rw [measureMoment_sourceConvolutionMeasure hq k (by omega : j+2 ≤ 8),
    measureMoment_sourceConvolutionMeasure hq k (by omega : j+3 ≤ 8)]

theorem sourceConvolution_transfer_bounds {q : ℝ} (hq : 3/2 ≤ q) {k : ℕ} (hk : 3 ≤ k) :
    0 ≤ growthTransferFunctional q
      (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k) ∧
    growthTransferFunctional q
      (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k) ≤
      growthTransferLeadingCoefficient q*
        spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k 8 := by
  have hq0 : 0 < q := by linarith
  have hdomain : ∀ᵐ t ∂sourceConvolutionMeasure q k, 8 ≤ t := by
    have hkr : (3:ℝ) ≤ k := by exact_mod_cast hk
    filter_upwards [ae_lower_sourceConvolutionMeasure hq0 k] with t ht
    linarith
  constructor
  · rw [← integral_growthTransferKernel_source hq0 k]
    apply integral_nonneg_of_ae
    filter_upwards [hdomain] with t ht
    exact (growthTransferKernel_pos hq ht).le
  · rw [← integral_growthTransferKernel_source hq0 k]
    calc
      (∫ t : ℝ, growthTransferKernel q t ∂sourceConvolutionMeasure q k) ≤
          ∫ t : ℝ, growthTransferLeadingCoefficient q*t^8 ∂sourceConvolutionMeasure q k := by
        apply integral_mono_ae
          (integrable_growthTransferKernel q _ (integrable_pow_sourceConvolutionMeasure hq0 k))
          ((integrable_pow_sourceConvolutionMeasure hq0 k 8).const_mul _)
        filter_upwards [hdomain] with t ht
        exact growthTransferKernel_le_monomial hq ht
      _ = growthTransferLeadingCoefficient q*
          spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k 8 := by
        rw [integral_const_mul]
        change growthTransferLeadingCoefficient q*measureMoment (sourceConvolutionMeasure q k) 8=_
        rw [measureMoment_sourceConvolutionMeasure hq0 k (le_refl 8)]

theorem sourceConvolution_moment_le {q : ℝ} (hq : 0 < q) (k : ℕ)
    {j : ℕ} (hj : j ≤ 8) :
    spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) (k+1) j ≤
      ((k+1:ℕ):ℝ)^j*(thetaCuspHigherLikelihoodSpectralMoment q 0)^k*
        thetaCuspHigherLikelihoodSpectralMoment q j := by
  let m := thetaCuspHigherLikelihoodSpectralMoment q
  have hm : ∀ i, 0 ≤ m i := fun i => thetaCuspHigherLikelihoodSpectralMoment_nonneg i
  change spectralPowerMoment m (k+1) j ≤ ((k+1:ℕ):ℝ)^j*m 0^k*m j
  induction k generalizing j with
  | zero => simpa using (spectralPowerMoment_one m hj).le
  | succ k ih =>
    rw [spectralPowerMoment_succ m (k+1) hj]
    unfold momentConvolution
    simp only [mul_assoc]
    calc
      (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*(m i*spectralPowerMoment m (k+1) (j-i))) ≤
          ∑ i ∈ Finset.range (j+1),
            (j.choose i:ℝ)*(((k+1:ℕ):ℝ)^(j-i)*m 0^(k+1)*m j) := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i+(j-i)=j := by have := Finset.mem_range.mp hi; omega
        have hmij : m i*m (j-i) ≤ m 0*m j := by
          simpa only [hij] using
            thetaCuspHigherLikelihoodSpectralMoment_mul_le_tailMass_mul hq i (j-i)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          m i*spectralPowerMoment m (k+1) (j-i) ≤
              m i*(((k+1:ℕ):ℝ)^(j-i)*m 0^k*m (j-i)) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) (hm i)
          _ = (((k+1:ℕ):ℝ)^(j-i)*m 0^k)*(m i*m (j-i)) := by ring
          _ ≤ (((k+1:ℕ):ℝ)^(j-i)*m 0^k)*(m 0*m j) :=
            mul_le_mul_of_nonneg_left hmij (mul_nonneg (by positivity) (pow_nonneg (hm 0) _))
          _ = ((k+1:ℕ):ℝ)^(j-i)*m 0^(k+1)*m j := by rw [pow_succ]; ring
      _ = ((k+1+1:ℕ):ℝ)^j*m 0^(k+1)*m j := by
        have hbin := pow_add_as_moment_sum 1 ((k+1:ℕ):ℝ) j
        simp only [one_pow,one_mul] at hbin
        calc
          _ = (∑ i ∈ Finset.range (j+1),
              (j.choose i:ℝ)*((k+1:ℕ):ℝ)^(j-i))*m 0^(k+1)*m j := by
            simp only [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = (1+((k+1:ℕ):ℝ))^j*m 0^(k+1)*m j := by rw [←hbin]
          _ = _ := by congr 2; push_cast; ring
      _ = ((k+1+1:ℕ):ℝ)^j*(m 0^(k+1)*m j) := by ring

theorem sourceConvolution_transfer_le {q : ℝ} (hq : 3/2 ≤ q) (k : ℕ)
    (hk : 2 ≤ k) :
    growthTransferFunctional q
      (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) (k+1)) ≤
      growthTransferLeadingCoefficient q*((k+1:ℕ):ℝ)^8*
        (thetaCuspHigherLikelihoodSpectralMoment q 0)^k*
        thetaCuspHigherLikelihoodSpectralMoment q 8 := by
  have hq0 : 0 < q := by linarith
  calc
    _ ≤ growthTransferLeadingCoefficient q*
        spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) (k+1) 8 :=
      (sourceConvolution_transfer_bounds hq (by omega)).2
    _ ≤ growthTransferLeadingCoefficient q*
        (((k+1:ℕ):ℝ)^8*(thetaCuspHigherLikelihoodSpectralMoment q 0)^k*
          thetaCuspHigherLikelihoodSpectralMoment q 8) :=
      mul_le_mul_of_nonneg_left (sourceConvolution_moment_le hq0 k (le_refl 8))
        (growthTransferLeadingCoefficient_pos hq).le
    _ = _ := by ring


theorem spectralPowerMoment_smul (a : ℝ) (m : ℕ → ℝ) (k j : ℕ) :
    spectralPowerMoment (fun i => a*m i) k j=a^k*spectralPowerMoment m k j := by
  have hs : momentSeries (fun i => a*m i)=PowerSeries.C a*momentSeries m := by
    ext i
    simp only [momentSeries,PowerSeries.coeff_mk,PowerSeries.coeff_C_mul]
    ring
  unfold spectralPowerMoment
  rw [hs,mul_pow,←map_pow,PowerSeries.coeff_C_mul]
  ring

theorem growthTransferFunctional_smul (q a : ℝ) (m : ℕ → ℝ) :
    growthTransferFunctional q (fun j => a*m j)=a*growthTransferFunctional q m := by
  unfold growthTransferFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem momentConvolution_succ (m n : ℕ → ℝ) {j : ℕ} (hj : j ≤ 7) :
    momentConvolution m n (j+1)=
      momentConvolution (fun i => m (i+1)) n j+
      momentConvolution m (fun i => n (i+1)) j := by
  interval_cases j <;> norm_num [momentConvolution,Finset.sum_range_succ,Nat.choose] <;> ring

theorem growthSlope_momentConvolution (q : ℝ) (m n : ℕ → ℝ) :
    growthSlope q (momentConvolution m n)=fullPairGrowthSlope q m n := by
  unfold growthSlope fullPairGrowthSlope
  apply Finset.sum_congr rfl
  intro j hj
  have hj5 : j ≤ 5 := by have := Finset.mem_range.mp hj; omega
  rw [show j+3=(j+2)+1 by omega,momentConvolution_succ m n (j := j+2) (by omega)]

theorem growthTransferFunctional_dominant_zero {q : ℝ} (hq : 0 < q) :
    growthTransferFunctional q (atomMoment 2 q)=0 := by
  have hw := growthTransferFunctional_anchor hq (atomMoment 2 q)
  have hp : 0 < dominantAtomScale q/q^9 := div_pos (dominantAtomScale_pos q) (pow_pos hq _)
  nlinarith

theorem growthTransferFunctional_dominant_pair_pos {q : ℝ} (hq : 3/2 ≤ q) :
    0 < growthTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 2) := by
  have hq0 : 0 < q := by linarith
  have he : growthTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 2)=
      growthTransferFunctional q (momentConvolution (atomMoment 2 q) (atomMoment 2 q)) := by
    unfold growthTransferFunctional
    apply Finset.sum_congr rfl
    intro j hj
    have hj5 : j ≤ 5 := by have := Finset.mem_range.mp hj; omega
    rw [spectralPowerMoment_two _ (by omega : j+2 ≤ 8),
      spectralPowerMoment_two _ (by omega : j+3 ≤ 8)]
  rw [he]
  have hw := growthTransferFunctional_anchor hq0
    (momentConvolution (atomMoment 2 q) (atomMoment 2 q))
  rw [growthSlope_momentConvolution] at hw
  have hp := atom_fullPairGrowthCooling_pos hq
  unfold fullPairGrowthCooling fullPairGrowth at hp
  have hf : 0 < dominantAtomScale q/q^9 := div_pos (dominantAtomScale_pos q) (pow_pos hq0 _)
  nlinarith


end
end RHTower.ThetaCuspDefect
