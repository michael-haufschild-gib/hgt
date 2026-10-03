import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthNextConvolution
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthDeepMomentOrdering
/-! Ninth-moment convolution control from positive-measure moment ordering.
A marked deep factor transports the full source moment to the deep tail. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section
private theorem pow_add_as_moment_sum (s t : ℝ) (j : ℕ) :
    (s+t)^j=∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*(s^i*t^(j-i)) := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem spectralPowerMoment_one_nine (m : ℕ → ℝ) {j : ℕ} (hj : j ≤ 9) :
    spectralPowerMoment m 1 j=m j := by
  by_cases h8 : j ≤ 8
  · exact spectralPowerMoment_one m h8
  · have he : j=9 := by omega
    subst j
    norm_num [spectralPowerMoment,momentSeries]
    ring

theorem powerMoment_nine_le (m : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hprod : ∀ i j, m i*m j ≤ m 0*m (i+j)) (k : ℕ)
    {j : ℕ} (hj : j ≤ 9) :
    spectralPowerMoment m (k+1) j ≤ ((k+1:ℕ):ℝ)^j*m 0^k*m j := by
  induction k generalizing j with
  | zero => simpa using (spectralPowerMoment_one_nine m hj).le
  | succ k ih =>
    rw [spectralPowerMoment_succ_nine m (k+1) hj]
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
            hprod i (j-i)
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

theorem sourceConvolution_moment_nine_le {q : ℝ} (hq : 0 < q) (k : ℕ)
    {j : ℕ} (hj : j ≤ 9) :
    spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) (k+1) j ≤
      ((k+1:ℕ):ℝ)^j*thetaCuspHigherLikelihoodSpectralMoment q 0^k*
        thetaCuspHigherLikelihoodSpectralMoment q j := by
  exact powerMoment_nine_le _ (fun i => thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := q) i)
    (thetaCuspHigherLikelihoodSpectralMoment_mul_le_tailMass_mul hq) k hj

open MeasureTheory Filter

theorem measureMoment_mul_le_of_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hi : ∀ r : ℕ, Integrable (fun t : ℝ => t^r) μ)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (i j : ℕ) :
    measureMoment μ i*measureMoment μ j ≤ measureMoment μ 0*measureMoment μ (i+j) := by
  have hprod : ∀ᵐ z : ℝ×ℝ ∂μ.prod μ, 0 ≤ z.1 ∧ 0 ≤ z.2 := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [hμ] with s hs
    filter_upwards [hμ] with t ht
    exact ⟨hs,ht⟩
  have hkernel : ∀ᵐ z : ℝ×ℝ ∂μ.prod μ, 0 ≤ (z.2^j-z.1^j)*(z.2^i-z.1^i) := by
    filter_upwards [hprod] with z hz
    rcases le_total z.1 z.2 with hxy | hyx
    · exact mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hz.1 hxy j))
        (sub_nonneg.mpr (pow_le_pow_left₀ hz.1 hxy i))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (pow_le_pow_left₀ hz.2 hyx j))
        (sub_nonpos.mpr (pow_le_pow_left₀ hz.2 hyx i))
  have h := HTGeometry.integral_mul_integral_le_of_monotoneLikelihoodKernel
    (μ := μ) (f := fun t : ℝ => t^i) (h := fun _ : ℝ => (1:ℝ)) (g := fun t : ℝ => t^j)
    (hi i) (by simpa only [pow_zero] using hi 0)
    (by simpa only [←pow_add,add_comm] using hi (i+j))
    (by simpa only [mul_one] using hi j) (by simpa only [one_mul] using hkernel)
  change (∫ t, t^j*1 ∂μ)*(∫ t, t^i ∂μ) ≤ (∫ t, t^j*t^i ∂μ)*(∫ t, (1:ℝ) ∂μ) at h
  simp only [mul_one,←pow_add] at h
  simpa only [measureMoment,pow_zero,add_comm,mul_comm] using h

theorem dominantMoment_mul_le_mass_mul {q : ℝ} (hq : 0 < q) (i j : ℕ) :
    atomMoment 2 q i*atomMoment 2 q j ≤ atomMoment 2 q 0*atomMoment 2 q (i+j) := by
  let A := componentTilt q thetaCuspSecondAtomSpectralMeasure
  have hi : ∀ r : ℕ, Integrable (fun t : ℝ => t^r) A :=
    integrable_pow_componentTilt q _ (fun r => integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure r hq)
  letI : IsFiniteMeasure A := componentTilt_finite q _
    (fun r => integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure r hq)
  have hA : ∀ᵐ t ∂A, 0 ≤ t :=
    ae_lower_componentTilt q _ ae_nonneg_thetaCuspSecondAtomSpectralMeasure
  have h := measureMoment_mul_le_of_nonneg A hi hA i j
  have he : measureMoment A=atomMoment 2 q := by
    funext r
    rw [measureMoment_componentTilt]
    simp only [atomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul]
  simpa only [he] using h

theorem dominantConvolution_moment_nine_le {q : ℝ} (hq : 0 < q) (k : ℕ)
    {j : ℕ} (hj : j ≤ 9) :
    spectralPowerMoment (atomMoment 2 q) (k+1) j ≤
      ((k+1:ℕ):ℝ)^j*atomMoment 2 q 0^k*atomMoment 2 q j := by
  apply powerMoment_nine_le _ ?_ (dominantMoment_mul_le_mass_mul hq) k hj
  intro i
  simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
    thetaCuspSecondAtomMoment_nonneg q i

theorem deepMarkedConvolution_moment_le {q : ℝ} (hq : 0 < q) (k : ℕ)
    {j : ℕ} (hj : j ≤ 9) :
    momentConvolution (thetaCuspDeepTailMoment q)
      (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) (k+1)) j ≤
        ((k+2:ℕ):ℝ)^j*thetaCuspHigherLikelihoodSpectralMoment q 0^(k+1)*thetaCuspDeepTailMoment q j := by
  let m := thetaCuspHigherLikelihoodSpectralMoment q
  let d := thetaCuspDeepTailMoment q
  have hm : ∀ i, 0 ≤ m i := fun i => thetaCuspHigherLikelihoodSpectralMoment_nonneg i
  have hd : ∀ i, 0 ≤ d i := fun i => thetaCuspDeepTailMoment_nonneg q i
  change momentConvolution d (spectralPowerMoment m (k+1)) j ≤ ((k+2:ℕ):ℝ)^j*m 0^(k+1)*d j
  unfold momentConvolution
  simp only [mul_assoc]
  calc
    (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*(d i*spectralPowerMoment m (k+1) (j-i))) ≤
        ∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*(((k+1:ℕ):ℝ)^(j-i)*m 0^(k+1)*d j) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i+(j-i)=j := by have := Finset.mem_range.mp hi; omega
      have hdm : d i*m (j-i) ≤ m 0*d j := by
        simpa only [hij] using deepMoment_mul_source_le hq i (j-i)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        d i*spectralPowerMoment m (k+1) (j-i) ≤
            d i*(((k+1:ℕ):ℝ)^(j-i)*m 0^k*m (j-i)) :=
          mul_le_mul_of_nonneg_left (sourceConvolution_moment_nine_le hq k (by omega)) (hd i)
        _ = (((k+1:ℕ):ℝ)^(j-i)*m 0^k)*(d i*m (j-i)) := by ring
        _ ≤ (((k+1:ℕ):ℝ)^(j-i)*m 0^k)*(m 0*d j) :=
          mul_le_mul_of_nonneg_left hdm (mul_nonneg (by positivity) (pow_nonneg (hm 0) _))
        _ = ((k+1:ℕ):ℝ)^(j-i)*m 0^(k+1)*d j := by rw [pow_succ]; ring
    _ = ((k+2:ℕ):ℝ)^j*m 0^(k+1)*d j := by
      have hbin := pow_add_as_moment_sum 1 ((k+1:ℕ):ℝ) j
      simp only [one_pow,one_mul] at hbin
      calc
        _ = (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*((k+1:ℕ):ℝ)^(j-i))*m 0^(k+1)*d j := by
          simp only [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (1+((k+1:ℕ):ℝ))^j*m 0^(k+1)*d j := by rw [←hbin]
        _ = _ := by congr 2; push_cast; ring
    _ = ((k+2:ℕ):ℝ)^j*(m 0^(k+1)*d j) := by ring

end
end RHTower.ThetaCuspDefect
