import GaloisForLFunctions.HTGeometry.ConstitutiveLocalRenewalActionThreshold

/-!
# Aperture information projection

This module constructs the literal two-piece Radon--Nikodym density that changes only aperture
mass.  It proves probability normalization, prescribed mass, endpoint-complete Bernoulli KL, and
the exact minimum-information property.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real InformationTheory Set ProbabilityTheory Filter Topology
open scoped ENNReal Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Piecewise-constant likelihood ratio of the aperture information projection. -/
def apertureProjectionDensity
    (mu : Measure X) (A : Set X) (alpha : unitInterval) (x : X) : ℝ≥0∞ :=
  by
    classical
    exact if x ∈ A then ENNReal.ofReal (alpha : ℝ) / mu A
      else ENNReal.ofReal (1 - (alpha : ℝ)) / mu Aᶜ

theorem measurable_apertureProjectionDensity
    (mu : Measure X) (A : Set X) (hA : MeasurableSet A) (alpha : unitInterval) :
    Measurable (apertureProjectionDensity mu A alpha) := by
  classical
  unfold apertureProjectionDensity
  exact Measurable.piecewise hA measurable_const measurable_const

/-- Minimum-information renewal candidate with prescribed aperture mass. -/
def apertureProjection
    (mu : Measure X) (A : Set X) (alpha : unitInterval) : Measure X :=
  mu.withDensity (apertureProjectionDensity mu A alpha)

theorem apertureProjection_apply
    (mu : Measure X) [IsProbabilityMeasure mu]
    (A : Set X) (hA : MeasurableSet A) (alpha : unitInterval)
    (hepsilon0 : 0 < mu.real A) :
    apertureProjection mu A alpha A = ENNReal.ofReal (alpha : ℝ) := by
  rw [apertureProjection, withDensity_apply _ hA]
  have hae : apertureProjectionDensity mu A alpha =ᵐ[mu.restrict A]
      fun _ => ENNReal.ofReal (alpha : ℝ) / mu A := by
    filter_upwards [ae_restrict_mem hA] with x hx
    simp [apertureProjectionDensity, hx]
  rw [lintegral_congr_ae hae, setLIntegral_const]
  have hmuA : mu A ≠ 0 := by
    intro hz
    rw [measureReal_def, hz] at hepsilon0
    simp at hepsilon0
  exact ENNReal.div_mul_cancel hmuA (measure_ne_top mu A)

theorem apertureProjection_apply_compl
    (mu : Measure X) [IsProbabilityMeasure mu]
    (A : Set X) (hA : MeasurableSet A) (alpha : unitInterval)
    (hepsilon1 : mu.real A < 1) :
    apertureProjection mu A alpha Aᶜ = ENNReal.ofReal (1 - (alpha : ℝ)) := by
  rw [apertureProjection, withDensity_apply _ hA.compl]
  have hae : apertureProjectionDensity mu A alpha =ᵐ[mu.restrict Aᶜ]
      fun _ => ENNReal.ofReal (1 - (alpha : ℝ)) / mu Aᶜ := by
    filter_upwards [ae_restrict_mem hA.compl] with x hx
    have hxnot : x ∉ A := hx
    simp [apertureProjectionDensity, hxnot]
  rw [lintegral_congr_ae hae, setLIntegral_const]
  have hmuAc : mu Aᶜ ≠ 0 := by
    intro hz
    have hcomp : mu.real Aᶜ = 1 - mu.real A := by
      rw [measureReal_compl hA, probReal_univ]
    rw [measureReal_def, hz] at hcomp
    simp at hcomp
    linarith
  exact ENNReal.div_mul_cancel hmuAc (measure_ne_top mu Aᶜ)

theorem apertureProjection_apply_univ
    (mu : Measure X) [IsProbabilityMeasure mu]
    (A : Set X) (hA : MeasurableSet A) (alpha : unitInterval)
    (hepsilon0 : 0 < mu.real A) (hepsilon1 : mu.real A < 1) :
    apertureProjection mu A alpha univ = 1 := by
  rw [← union_compl_self A,
    measure_union disjoint_compl_right hA.compl,
    apertureProjection_apply mu A hA alpha hepsilon0,
    apertureProjection_apply_compl mu A hA alpha hepsilon1,
    ← ENNReal.ofReal_add alpha.property.1 (sub_nonneg.mpr alpha.property.2)]
  simp

theorem rnDeriv_apertureProjection
    (mu : Measure X) [IsProbabilityMeasure mu]
    (A : Set X) (hA : MeasurableSet A) (alpha : unitInterval) :
    (apertureProjection mu A alpha).rnDeriv mu =ᵐ[mu]
      apertureProjectionDensity mu A alpha := by
  exact Measure.rnDeriv_withDensity mu
    (measurable_apertureProjectionDensity mu A hA alpha)

/-- The aperture projection is a probability measure whenever baseline aperture is nontrivial. -/
theorem isProbabilityMeasure_apertureProjection
    (mu : Measure X) [IsProbabilityMeasure mu]
    (A : Set X) (hA : MeasurableSet A) (alpha : unitInterval)
    (hepsilon0 : 0 < mu.real A) (hepsilon1 : mu.real A < 1) :
    IsProbabilityMeasure (apertureProjection mu A alpha) :=
  ⟨apertureProjection_apply_univ mu A hA alpha hepsilon0 hepsilon1⟩

theorem apertureProjection_real
    (mu : Measure X) [IsProbabilityMeasure mu]
    (A : Set X) (hA : MeasurableSet A) (alpha : unitInterval)
    (hepsilon0 : 0 < mu.real A) :
    (apertureProjection mu A alpha).real A = (alpha : ℝ) := by
  rw [measureReal_def, apertureProjection_apply mu A hA alpha hepsilon0,
    ENNReal.toReal_ofReal alpha.property.1]

theorem apertureProjection_real_compl
    (mu : Measure X) [IsProbabilityMeasure mu]
    (A : Set X) (hA : MeasurableSet A) (alpha : unitInterval)
    (hepsilon1 : mu.real A < 1) :
    (apertureProjection mu A alpha).real Aᶜ = 1 - (alpha : ℝ) := by
  rw [measureReal_def, apertureProjection_apply_compl mu A hA alpha hepsilon1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr alpha.property.2)]

/-! The existing Bernoulli density computation assumed an interior renewed mass.  For the exact
projection theorem we retain the endpoint cases `alpha = 0,1`; only baseline mass must be interior. -/

theorem bernoulli_eq_withDensity_baseline_interior
    (p r : unitInterval) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    Ber(true, false, p) = Ber(true, false, r).withDensity (bernoulliDensity p r) := by
  apply Measure.ext_of_singleton
  intro b
  rw [withDensity_bool_singleton]
  cases b with
  | false =>
      rw [bernoulliMeasure_apply_of_notMem_of_mem p (MeasurableSet.singleton false)
        (by simp) (by simp)]
      rw [bernoulliMeasure_apply_of_notMem_of_mem r (MeasurableSet.singleton false)
        (by simp) (by simp)]
      simp only [bernoulliDensity, Bool.false_eq_true, ↓reduceIte]
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul
          (div_nonneg (sub_nonneg.mpr p.property.2) (sub_nonneg.mpr r.property.2))]
      congr 1
      simp only [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
      field_simp [ne_of_gt (sub_pos.mpr hr1)]
  | true =>
      rw [bernoulliMeasure_apply_of_mem_of_notMem p (MeasurableSet.singleton true)
        (by simp) (by simp)]
      rw [bernoulliMeasure_apply_of_mem_of_notMem r (MeasurableSet.singleton true)
        (by simp) (by simp)]
      simp only [bernoulliDensity, ↓reduceIte]
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (div_nonneg p.property.1 r.property.1)]
      congr 1
      simp only [unitInterval.coe_toNNReal]
      field_simp

theorem bernoulli_ac_baseline_interior
    (p r : unitInterval) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    Ber(true, false, p) ≪ Ber(true, false, r) := by
  rw [bernoulli_eq_withDensity_baseline_interior p r hr0 hr1]
  exact withDensity_absolutelyContinuous _ _

theorem rnDeriv_bernoulli_baseline_interior
    (p r : unitInterval) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    Ber(true, false, p).rnDeriv Ber(true, false, r) =ᵐ[Ber(true, false, r)]
      bernoulliDensity p r := by
  rw [bernoulli_eq_withDensity_baseline_interior p r hr0 hr1]
  exact Measure.rnDeriv_withDensity _ (by fun_prop)

theorem llr_bernoulli_baseline_interior
    (p r : unitInterval) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    llr Ber(true, false, p) Ber(true, false, r) =ᵐ[Ber(true, false, p)]
      fun b => if b then Real.log ((p : ℝ) / (r : ℝ))
        else Real.log ((1 - (p : ℝ)) / (1 - (r : ℝ))) := by
  have hac := bernoulli_ac_baseline_interior p r hr0 hr1
  filter_upwards [(rnDeriv_bernoulli_baseline_interior p r hr0 hr1).filter_mono hac.ae_le]
      with b hb
  rw [llr, hb]
  have hratio : 0 ≤ (p : ℝ) / (r : ℝ) := div_nonneg p.property.1 r.property.1
  have hcomp : 0 ≤ (1 - (p : ℝ)) / (1 - (r : ℝ)) :=
    div_nonneg (sub_nonneg.mpr p.property.2) (sub_nonneg.mpr r.property.2)
  cases b
  · simp [bernoulliDensity, ENNReal.toReal_ofReal hcomp]
  · simp [bernoulliDensity, ENNReal.toReal_ofReal hratio]

theorem toReal_klDiv_bernoulli_baseline_interior
    (p r : unitInterval) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    (klDiv Ber(true, false, p) Ber(true, false, r)).toReal =
      (p : ℝ) * Real.log ((p : ℝ) / (r : ℝ)) +
        (1 - (p : ℝ)) * Real.log ((1 - (p : ℝ)) / (1 - (r : ℝ))) := by
  rw [toReal_klDiv_of_measure_eq
    (bernoulli_ac_baseline_interior p r hr0 hr1) (by simp)]
  rw [integral_congr_ae (llr_bernoulli_baseline_interior p r hr0 hr1)]
  rw [integral_bernoulliMeasure]
  simp only [↓reduceIte, Bool.false_eq_true, smul_eq_mul]

theorem klDiv_bernoulli_ne_top_baseline_interior
    (p r : unitInterval) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    klDiv Ber(true, false, p) Ber(true, false, r) ≠ ⊤ := by
  apply klDiv_ne_top (bernoulli_ac_baseline_interior p r hr0 hr1)
  rw [integrable_congr (llr_bernoulli_baseline_interior p r hr0 hr1)]
  exact integrable_bernoulliMeasure true false p _

/-- Endpoint-complete identity between continuous binary cost and Bernoulli KL. -/
theorem binaryRenewalCost_eq_klDiv_baseline_interior
    (epsilon alpha : unitInterval)
    (hepsilon0 : 0 < (epsilon : ℝ)) (hepsilon1 : (epsilon : ℝ) < 1) :
    binaryRenewalCost epsilon alpha =
      (klDiv Ber(true, false, alpha) Ber(true, false, epsilon)).toReal := by
  rw [toReal_klDiv_bernoulli_baseline_interior alpha epsilon hepsilon0 hepsilon1]
  unfold binaryRenewalCost Real.binEntropy
  by_cases halpha0 : (alpha : ℝ) = 0
  · simp [halpha0]
  by_cases halpha1 : (alpha : ℝ) = 1
  · simp [halpha1]
  · have halpha0' : 0 < (alpha : ℝ) :=
      lt_of_le_of_ne alpha.property.1 (Ne.symm halpha0)
    have halpha1' : (alpha : ℝ) < 1 :=
      lt_of_le_of_ne alpha.property.2 halpha1
    rw [Real.log_div halpha0'.ne' hepsilon0.ne',
      Real.log_div (sub_pos.mpr halpha1').ne' (sub_pos.mpr hepsilon1).ne']
    simp only [Real.log_inv]
    ring

/-- Log-likelihood of the aperture projection, in the exact two-piece density form. -/
def apertureProjectionLogDensity
    (mu : Measure X) (A : Set X) (alpha : unitInterval) (x : X) : ℝ :=
  by
    classical
    exact if x ∈ A then Real.log ((alpha : ℝ) / mu.real A)
      else Real.log ((1 - (alpha : ℝ)) / (1 - mu.real A))

theorem llr_apertureProjection
    (mu : Measure X) [IsProbabilityMeasure mu]
    (A : Set X) (hA : MeasurableSet A) (alpha : unitInterval) :
    llr (apertureProjection mu A alpha) mu =ᵐ[apertureProjection mu A alpha]
      apertureProjectionLogDensity mu A alpha := by
  have hac : apertureProjection mu A alpha ≪ mu :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [(rnDeriv_apertureProjection mu A hA alpha).filter_mono hac.ae_le]
      with x hx
  rw [llr, hx]
  classical
  by_cases hxA : x ∈ A
  · simp only [apertureProjectionDensity, hxA, ↓reduceIte,
      apertureProjectionLogDensity]
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal alpha.property.1, measureReal_def]
  · simp only [apertureProjectionDensity, hxA, ↓reduceIte,
      apertureProjectionLogDensity]
    rw [ENNReal.toReal_div,
      ENNReal.toReal_ofReal (sub_nonneg.mpr alpha.property.2)]
    have hcomp : mu.real Aᶜ = 1 - mu.real A := by
      rw [measureReal_compl hA, probReal_univ]
    rw [← hcomp, measureReal_def]

theorem integrable_llr_apertureProjection
    (mu : Measure X) [IsProbabilityMeasure mu]
    (A : Set X) (hA : MeasurableSet A) (alpha : unitInterval)
    (hepsilon0 : 0 < mu.real A) (hepsilon1 : mu.real A < 1) :
    Integrable (llr (apertureProjection mu A alpha) mu)
      (apertureProjection mu A alpha) := by
  letI : IsProbabilityMeasure (apertureProjection mu A alpha) :=
    isProbabilityMeasure_apertureProjection mu A hA alpha hepsilon0 hepsilon1
  rw [integrable_congr
    (llr_apertureProjection mu A hA alpha)]
  classical
  unfold apertureProjectionLogDensity
  apply Integrable.piecewise hA
  · exact integrableOn_const
  · exact integrableOn_const

/-- The explicit piecewise-density projection pays exactly binary KL, including `alpha=0,1`. -/
theorem klDiv_apertureProjection_eq_bernoulli
    (mu : Measure X) [IsProbabilityMeasure mu]
    (A : Set X) (hA : MeasurableSet A) (alpha : unitInterval)
    (hepsilon0 : 0 < mu.real A) (hepsilon1 : mu.real A < 1) :
    klDiv (apertureProjection mu A alpha) mu =
      klDiv Ber(true, false, alpha) Ber(true, false, apertureProbability mu A) := by
  letI : IsProbabilityMeasure (apertureProjection mu A alpha) :=
    isProbabilityMeasure_apertureProjection mu A hA alpha hepsilon0 hepsilon1
  have hac : apertureProjection mu A alpha ≪ mu :=
    withDensity_absolutelyContinuous _ _
  have hprojFin : klDiv (apertureProjection mu A alpha) mu ≠ ⊤ :=
    klDiv_ne_top hac
      (integrable_llr_apertureProjection mu A hA alpha hepsilon0 hepsilon1)
  have hepsCoe : (apertureProbability mu A : ℝ) = mu.real A := rfl
  have hbinFin := klDiv_bernoulli_ne_top_baseline_interior alpha
    (apertureProbability mu A) (by simpa [hepsCoe]) (by simpa [hepsCoe])
  apply (ENNReal.toReal_eq_toReal_iff' hprojFin hbinFin).mp
  rw [toReal_klDiv_of_measure_eq hac (by simp)]
  rw [integral_congr_ae
    (llr_apertureProjection mu A hA alpha)]
  classical
  unfold apertureProjectionLogDensity
  change (∫ x, A.piecewise
      (fun _ => Real.log ((alpha : ℝ) / mu.real A))
      (fun _ => Real.log ((1 - (alpha : ℝ)) / (1 - mu.real A))) x
        ∂apertureProjection mu A alpha) = _
  rw [integral_piecewise hA integrableOn_const integrableOn_const,
    setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul,
    apertureProjection_real mu A hA alpha hepsilon0,
    apertureProjection_real_compl mu A hA alpha hepsilon1]
  simpa [hepsCoe] using
    (toReal_klDiv_bernoulli_baseline_interior alpha (apertureProbability mu A)
      (by simpa [hepsCoe]) (by simpa [hepsCoe])).symm

/-- The explicit projection is a genuine information projection: among all renewed probability
laws with its aperture mass, it realizes the universal binary lower bound. -/
theorem klDiv_apertureProjection_le
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : Set X) (hA : MeasurableSet A)
    (hepsilon0 : 0 < mu.real A) (hepsilon1 : mu.real A < 1) :
    klDiv (apertureProjection mu A (apertureProbability nu A)) mu ≤ klDiv nu mu := by
  rw [klDiv_apertureProjection_eq_bernoulli mu A hA
    (apertureProbability nu A) hepsilon0 hepsilon1]
  exact aperture_binary_klDiv_le mu nu A hA

end

end GaloisForLFunctions.HTGeometry
