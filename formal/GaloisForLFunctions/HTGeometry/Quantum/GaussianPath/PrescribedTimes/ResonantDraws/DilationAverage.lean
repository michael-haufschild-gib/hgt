import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GaussianDilation
import Mathlib.MeasureTheory.Integral.Prod

/-! # Comparing a Gaussian snapshot to an average on the same rays -/
open MeasureTheory ProbabilityTheory Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
noncomputable section

private abbrev law (ι : Type*) [Fintype ι] := Measure.pi fun _ : ι => gaussianReal 0 1

/-- Expanding every Gaussian coordinate by a common factor changes the
probability of any measurable event by at most the excess Jacobian. -/
theorem dilation_probability_error {ι : Type*} [Fintype ι] (E : Set (ι → ℝ))
    (hE : MeasurableSet E) {a : ℝ} (ha : 1≤a) :
    |(law ι).real ((fun x : ι → ℝ => a • x) ⁻¹' E)-(law ι).real E| ≤
      a^Fintype.card ι-1 := by
  let μ := law ι
  let S := (fun x : ι → ℝ => a • x) ⁻¹' E
  have hS : MeasurableSet S := hE.preimage (measurable_id.const_smul a)
  have h₁ := gaussian_dilation_comparison ha E hE
  have h₂ := gaussian_dilation_comparison ha Eᶜ hE.compl
  change μ.real Eᶜ ≤ _*μ.real Sᶜ at h₂
  rw [measureReal_compl hE,measureReal_compl hS,probReal_univ] at h₂
  have hmass : μ.real S ≤ 1 := (measureReal_mono (subset_univ S)).trans_eq probReal_univ
  have hpos := sub_nonneg.mpr (one_le_pow₀ ha (Fintype.card ι))
  have hu := mul_le_mul_of_nonneg_left hmass hpos
  have hl := mul_nonneg hpos (show 0≤μ.real S from measureReal_nonneg)
  change μ.real E ≤ _*μ.real S at h₁
  change |μ.real S-μ.real E| ≤ _
  exact abs_le.mpr ⟨by linarith only [hu,h₁],by linarith only [hl,h₂]⟩

/-- Time spent on each ray under uniform dilation in [1,b]. -/
def rayMass {ι : Type*} (b : ℝ) (E : Set (ι → ℝ)) (x : ι → ℝ) : ℝ :=
  (volume.restrict (Icc 1 b)).real ((fun a : ℝ => a • x) ⁻¹' E)

theorem measurable_rayMass {ι : Type*} [Fintype ι] (b : ℝ) {E : Set (ι → ℝ)}
    (hE : MeasurableSet E) : Measurable (rayMass b E) :=
  (measurable_measure_prodMk_left (ν:=volume.restrict (Icc 1 b))
    (hE.preimage ((measurable_snd.smul measurable_fst) :
      Measurable (fun p : (ι → ℝ) × ℝ => p.2 • p.1)))).ennreal_toReal

/-- Averaging over rays and then over disorder equals averaging the
probabilities of the dilated events. -/
theorem integral_rayMass {ι : Type*} [Fintype ι] (b : ℝ) (E : Set (ι → ℝ)) (hE : MeasurableSet E) :
    (∫ x, rayMass b E x ∂law ι) = ∫ a in Icc 1 b, (law ι).real ((fun x : ι → ℝ => a • x) ⁻¹' E) := by
  let μ := law ι
  let ν := volume.restrict (Icc 1 b)
  let S := (fun p : (ι → ℝ) × ℝ => p.2 • p.1) ⁻¹' E
  have hS : MeasurableSet S := hE.preimage (measurable_snd.smul measurable_fst)
  change (∫ x, (ν (Prod.mk x ⁻¹' S)).toReal ∂μ) = ∫ y, (μ ((fun x => (x,y)) ⁻¹' S)).toReal ∂ν
  rw [integral_toReal (measurable_measure_prodMk_left hS).aemeasurable
    (ae_of_all _ fun _ => measure_lt_top _ _),←Measure.prod_apply hS,
    integral_toReal (measurable_measure_prodMk_right hS).aemeasurable
    (ae_of_all _ fun _ => measure_lt_top _ _),←Measure.prod_apply_symm hS]

/-- The undilated snapshot costs at most the largest Jacobian on [1,2]
times the Gaussian expectation of the ray occupation. -/
theorem snapshot_le_dyadic_mean {ι : Type*} [Fintype ι] (E : Set (ι → ℝ)) (hE : MeasurableSet E) :
    (law ι).real E ≤ (2:ℝ)^Fintype.card ι * ∫ x, rayMass 2 E x ∂law ι := by
  let μ := law ι
  let ν := volume.restrict (Icc (1:ℝ) 2)
  let q (a : ℝ) := μ.real ((fun x : ι → ℝ => a • x) ⁻¹' E)
  let S := (fun p : (ι → ℝ) × ℝ => p.2 • p.1) ⁻¹' E
  have hS : MeasurableSet S := hE.preimage (measurable_snd.smul measurable_fst)
  have hq : Integrable q ν := Integrable.of_bound
    (measurable_measure_prodMk_right (μ:=μ) hS).ennreal_toReal.aestronglyMeasurable 1
    (ae_of_all _ fun a => by
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤q a from measureReal_nonneg)]
      exact (measureReal_mono (subset_univ _)).trans_eq probReal_univ)
  have hh : ∀ᵐ a ∂ν, μ.real E ≤ (2:ℝ)^Fintype.card ι*q a := by
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Icc (a:=(1:ℝ)) (b:=2))] with a ha
    exact (gaussian_dilation_comparison ha.1 E hE).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (zero_le_one.trans ha.1) ha.2 _) measureReal_nonneg)
  have hi := integral_mono_ae (integrable_const (μ.real E)) (hq.const_mul _) hh
  have hm : ν.real univ=1 := by
    rw [measureReal_restrict_apply_univ,Real.volume_real_Icc_of_le (by norm_num)]; norm_num
  rw [integral_const,hm,one_smul,integral_const_mul] at hi
  rw [integral_rayMass 2 E hE]
  exact hi

/-- Taking the expectation of the ray mass gives the ensemble snapshot
times the dilation width, up to the explicit Gaussian dilation error. -/
theorem mean_rayMass_error {ι : Type*} [Fintype ι] (E : Set (ι → ℝ)) (hE : MeasurableSet E)
    {b : ℝ} (hb : 1<b) :
    |(∫ x, rayMass b E x ∂law ι)/(b-1)-(law ι).real E| ≤ b^Fintype.card ι-1 := by
  let μ := law ι
  let ν := volume.restrict (Icc 1 b)
  let S := (fun p : (ι → ℝ) × ℝ => p.2 • p.1) ⁻¹' E
  let q (a : ℝ) := μ.real ((fun x : ι → ℝ => a • x) ⁻¹' E)
  let p := μ.real E
  let d := b^Fintype.card ι-1
  have hS : MeasurableSet S := hE.preimage (measurable_snd.smul measurable_fst)
  have hm : ν.real univ=b-1 := (measureReal_restrict_apply_univ _).trans (Real.volume_real_Icc_of_le hb.le)
  have he : (∫ x, rayMass b E x ∂μ)=∫ a, q a ∂ν := integral_rayMass b E hE
  have hq : Integrable q ν := Integrable.of_bound
    (measurable_measure_prodMk_right (μ:=μ) hS).ennreal_toReal.aestronglyMeasurable 1
    (ae_of_all _ fun a => by
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤q a from measureReal_nonneg)]
      exact (measureReal_mono (subset_univ _)).trans_eq probReal_univ)
  have hbounds : ∀ᵐ a ∂ν, |q a-p| ≤ d := by
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Icc (a:=1) (b:=b))] with a ha
    exact (dilation_probability_error E hE ha.1).trans (sub_le_sub_right
      (pow_le_pow_left₀ (zero_le_one.trans ha.1) ha.2 _) _)
  have hlo := integral_mono_ae (integrable_const (p-d)) hq
    (hbounds.mono fun a h => by linarith only [(abs_le.mp h).1])
  have hhi := integral_mono_ae hq (integrable_const (p+d))
    (hbounds.mono fun a h => by linarith only [(abs_le.mp h).2])
  rw [integral_const,hm,smul_eq_mul] at hlo hhi
  change |(∫ x, rayMass b E x ∂μ)/(b-1)-p| ≤ d
  rw [he]
  refine abs_le.mpr ⟨?_,?_⟩
  · have hl := (le_div_iff₀ (sub_pos.mpr hb)).mpr ((mul_comm _ _).trans_le hlo)
    linarith only [hl]
  · have hu := (div_le_iff₀ (sub_pos.mpr hb)).mpr (hhi.trans_eq (mul_comm _ _))
    linarith only [hu]

#print axioms dilation_probability_error
#print axioms mean_rayMass_error
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
