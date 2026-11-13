/-
Residual automorphy and Gauss factorization adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.WeightedResidualFourierTests

/-!
# Residual automorphy and Gauss factorization

Fourier completeness on the period torus identifies `cubicResidualFunction` with the residue
and upgrades the cubic character law to pointwise automorphy. The normalized trace character
`residueTraceQuotientChar` is primitive at every nonzero modulus. CRT and ramified phase
periodicity factor the arithmetic residue sum into the cubic Gauss sum `cubicUnitGaussSum`
times a finite ramified combination of unramified Gauss series.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise

lemma periodFrequencyEquiv_neg (n : Fin 2 → ℤ) :
    periodFrequencyEquiv (-n) = -periodFrequencyEquiv n := by
  apply ringComplex_injective
  change ringComplex (Coordinates.eval (-n 0 + -n 1) (-n 0)) =
    ringComplex (-Coordinates.eval (n 0 + n 1) (n 0))
  rw [map_neg, ringComplex_eval, ringComplex_eval]
  push_cast
  ring

/-- Haar uniqueness supplies the positive coordinate density; its value is irrelevant to uniqueness. -/
def periodCovolumeDensity : ℝ≥0 :=
  Measure.addHaarScalarFactor (Measure.map periodVector volume) (volume : Measure ℂ)

lemma periodCovolumeDensity_pos : 0 < periodCovolumeDensity :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

lemma periodVector_map_volume :
    Measure.map periodVector volume = (periodCovolumeDensity : ℝ≥0∞) • volume :=
  Measure.isAddLeftInvariant_eq_smul _ _

def periodCube : Set (Fin 2 → ℝ) := {x | ∀ i, x i ∈ Set.Ico 0 1}

def periodIocCube : Set (Fin 2 → ℝ) := {x | ∀ i, x i ∈ Set.Ioc 0 (0 + 1)}

lemma periodVector_preimage_domain : periodVector ⁻¹' periodDomain = periodCube := by
  ext x
  change (∀ i, periodBasis.repr (periodBasis.equivFun.symm x) i ∈ Set.Ico 0 1) ↔ _
  simp only [← Module.Basis.equivFun_apply, periodBasis.equivFun.apply_symm_apply]
  rfl

lemma periodDomain_integral_coordinates (f : ℂ → ℂ) :
    (periodCovolumeDensity : ℝ) • (∫ z in periodDomain, f z) =
      ∫ x in periodCube, f (periodVector x) := by
  have h := periodVector.toHomeomorph.toMeasurableEquiv.measurableEmbedding.setIntegral_map
    f periodDomain (μ := (volume : Measure (Fin 2 → ℝ)))
  change (∫ z in periodDomain, f z ∂Measure.map periodVector volume) =
    ∫ x in periodVector ⁻¹' periodDomain, f (periodVector x) at h
  rw [periodVector_map_volume, Measure.restrict_smul, integral_smul_measure,
    ENNReal.coe_toReal, periodVector_preimage_domain] at h
  exact h

lemma periodIocCube_measurable : MeasurableSet periodIocCube :=
  MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)

lemma periodCube_ae_Ioc : periodCube =ᵐ[volume] periodIocCube := by
  rw [volume_pi]
  have h := Measure.ae_eq_set_pi (μ := fun _ : Fin 2 => (volume : Measure ℝ))
    (I := Set.univ) (s := fun _ => Set.Ico (0 : ℝ) 1) (t := fun _ => Set.Ioc (0 : ℝ) 1)
    (fun _ _ => Ico_ae_eq_Ioc)
  simpa only [Set.pi, Set.mem_univ, forall_true_left, periodCube, periodIocCube, zero_add] using h

section PeriodFourierCompleteness

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma periodTorus_integral (f : UnitAddTorus (Fin 2) → ℂ) :
    (∫ t, f t) = (periodCovolumeDensity : ℝ) • (∫ z in periodDomain, f (periodTorus z)) := by
  rw [periodDomain_integral_coordinates, UnitAddTorus.integral_preimage f (fun _ => 0)]
  simp only [periodTorus_periodVector]
  exact setIntegral_congr_set periodCube_ae_Ioc.symm

lemma periodTorus_fourierCoeff (f : UnitAddTorus (Fin 2) → ℂ) (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff f n = (periodCovolumeDensity : ℝ) •
      (∫ z in periodDomain, f (periodTorus z) *
        tracePhase (-cuspFrequency (periodFrequencyEquiv n) * z)) := by
  rw [UnitAddTorus.mFourierCoeff, periodTorus_integral]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [periodTorus_mFourier, periodFrequencyEquiv_neg]
    simp only [cuspFrequency, map_neg, neg_div, smul_eq_mul]
    exact mul_comm _ _)

/-- A measurable choice of representatives transports arbitrary L² functions to the torus. -/
def periodSection (t : UnitAddTorus (Fin 2)) : ℂ :=
  periodVector ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ)) t).val)

lemma periodSection_measurableEmbedding : MeasurableEmbedding periodSection :=
  periodVector.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe periodIocCube_measurable).comp
      (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ))).measurableEmbedding)

lemma periodTorus_measurable : Measurable periodTorus := by
  apply measurable_pi_iff.mpr
  intro i
  exact AddCircle.measurable_mk'.comp
    ((measurable_pi_apply i).comp periodBasis.equivFunL.continuous.measurable)

lemma periodTorus_section (t : UnitAddTorus (Fin 2)) : periodTorus (periodSection t) = t := by
  rw [periodSection, periodTorus_periodVector]
  exact (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ))).symm_apply_apply t

lemma periodSection_measurePreserving :
    MeasurePreserving periodSection volume
      ((periodCovolumeDensity : ℝ≥0∞) • volume.restrict periodDomain) := by
  have hvector : MeasurePreserving periodVector (volume.restrict periodIocCube)
      ((periodCovolumeDensity : ℝ≥0∞) • volume.restrict periodDomain) := by
    refine ⟨periodVector.continuous.measurable, ?_⟩
    rw [← Measure.restrict_congr_set periodCube_ae_Ioc, ← periodVector_preimage_domain,
      ← Measure.restrict_map periodVector.continuous.measurable periodDomain_measurable,
      periodVector_map_volume, Measure.restrict_smul]
  exact hvector.comp ((measurePreserving_subtype_coe periodIocCube_measurable).comp
    (UnitAddTorus.measurePreserving_equivPiIoc (fun _ : Fin 2 => (0 : ℝ))))

lemma periodTorus_measurePreserving :
    MeasurePreserving periodTorus ((periodCovolumeDensity : ℝ≥0∞) • volume.restrict periodDomain) volume := by
  refine ⟨periodTorus_measurable, ?_⟩
  rw [← periodSection_measurePreserving.map_eq,
    Measure.map_map periodTorus_measurable periodSection_measurableEmbedding.measurable]
  have he : periodTorus ∘ periodSection = id := funext periodTorus_section
  rw [he, Measure.map_id]

lemma periodSection_torus_ae :
    (fun z => periodSection (periodTorus z)) =ᵐ[volume.restrict periodDomain] (fun z : ℂ => z) := by
  have hc : (periodCovolumeDensity : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast periodCovolumeDensity_pos.ne'
  apply (Measure.ae_ennreal_smul_measure_iff hc).mp
  rw [← periodSection_measurePreserving.map_eq]
  apply periodSection_measurableEmbedding.ae_map_iff.mpr
  exact Eventually.of_forall (fun t => by dsimp only; rw [periodTorus_section])

lemma periodSection_memLp (f : ℂ → ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    MemLp (f ∘ periodSection) 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  (hf.smul_measure (c := (periodCovolumeDensity : ℝ≥0∞)) (by simp)).comp_measurePreserving
    periodSection_measurePreserving

def periodTorusL2Lift (f : ℂ → ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  (periodSection_memLp f hf).toLp (f ∘ periodSection)

lemma periodTorusL2Lift_pullback (f : ℂ → ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    (fun z => periodTorusL2Lift f hf (periodTorus z)) =ᵐ[volume.restrict periodDomain] f := by
  have hc : (periodCovolumeDensity : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast periodCovolumeDensity_pos.ne'
  have he := periodTorus_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (MemLp.coeFn_toLp (periodSection_memLp f hf))
  have he' := (Measure.ae_ennreal_smul_measure_iff hc).mp he
  filter_upwards [he', periodSection_torus_ae] with z hz hsec
  change periodTorusL2Lift f hf (periodTorus z) = f (periodSection (periodTorus z)) at hz
  rwa [hsec] at hz

/-- All cusp-lattice Fourier coefficients determine an L² function on one period cell. -/
theorem periodDomain_L2_ext (f g : ℂ → ℂ)
    (hf : MemLp f 2 (volume.restrict periodDomain))
    (hg : MemLp g 2 (volume.restrict periodDomain))
    (heq : ∀ h : O,
      (∫ z in periodDomain, f z * tracePhase (-cuspFrequency h * z)) =
        ∫ z in periodDomain, g z * tracePhase (-cuspFrequency h * z)) :
    f =ᵐ[volume.restrict periodDomain] g := by
  have hlift : periodTorusL2Lift f hf = periodTorusL2Lift g hg := by
    apply UnitAddTorus.mFourierBasis.repr.injective
    ext n
    rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr,
      periodTorus_fourierCoeff, periodTorus_fourierCoeff]
    congr 1
    calc
      _ = ∫ z in periodDomain, f z * tracePhase (-cuspFrequency (periodFrequencyEquiv n) * z) :=
        integral_congr_ae ((periodTorusL2Lift_pullback f hf).mul (Eventually.of_forall (fun _ => rfl)))
      _ = ∫ z in periodDomain, g z * tracePhase (-cuspFrequency (periodFrequencyEquiv n) * z) := heq _
      _ = _ := integral_congr_ae
        ((periodTorusL2Lift_pullback g hg).symm.mul (Eventually.of_forall (fun _ => rfl)))
  filter_upwards [periodTorusL2Lift_pullback f hf, periodTorusL2Lift_pullback g hg] with z hz hz'
  rw [← hz, ← hz', hlift]

end PeriodFourierCompleteness

lemma cubicResidualFunction_height_continuous (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => cubicResidualFunction (upperPoint z v hv)) := by
  simpa only [cubicResidualFunction, hyperbolicHeight_upperPoint, hyperbolicHorizontal_upperPoint,
    Pi.add_def] using
    continuous_const.add (cubicResidualNonzeroSeries_height_continuous v hv)

lemma cubicResidualFunction_height_memLp (v : ℝ) (hv : 0 < v) :
    MemLp (fun z : ℂ => cubicResidualFunction (cuspCoordinateLift (v, z))) 2
      (volume.restrict periodDomain) := by
  simp_rw [cuspCoordinateLift_positive v _ hv]
  have hc := cubicResidualFunction_height_continuous v hv
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  apply (((hc.norm.pow 2).continuousOn).integrableOn_compact
    (isCompact_closedBall (0 : ℂ) (∑ i, ‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_mem_periodDomain z hz

/-- Weighted tests determine the residue on almost every positive-height period cell. -/
theorem cubicEisensteinResidue_cell_slices_ae (a b : ℝ) (ha : 0 < a) :
    ∀ᵐ v ∂volume.restrict (Set.Icc a b),
      (fun z : ℂ => cubicEisensteinResidue
        (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v, z))))
      =ᵐ[volume.restrict periodDomain] (fun z => cubicResidualFunction (cuspCoordinateLift (v, z))) := by
  filter_upwards [cubicEisensteinResidue_all_fourier_integrals_ae a b ha,
    kernelCuspSections_memLp a b ha cubicEisensteinResidue,
    ae_restrict_mem measurableSet_Icc] with v hfour hL hv
  have hpos := ha.trans_le hv.1
  apply periodDomain_L2_ext _ _ hL (cubicResidualFunction_height_memLp v hpos)
  intro h
  rw [hfour h]
  symm
  simpa only [cuspCoordinateLift_positive v _ hpos] using cubicResidualFunction_fourier v hpos h

lemma cubicResidualFunction_period (v : ℝ) (hv : 0 < v) (z : ℂ) (n : O) :
    cubicResidualFunction (upperPoint (z + 3 * ringComplex n) v hv) =
      cubicResidualFunction (upperPoint z v hv) := by
  simp only [cubicResidualFunction, hyperbolicHeight_upperPoint, hyperbolicHorizontal_upperPoint]
  congr 1
  apply tsum_congr
  intro h
  simp only [cubicResidualNonzeroTerm]
  split_ifs
  · rfl
  · rw [mul_add, AddChar.map_add_eq_mul, cuspFrequency_period, mul_one]

lemma integralTranslation_three_mem_kernel (n : O) : integralTranslation (3 * n) ∈ globalKubotaKernel := by
  have h3 : Ideal.Quotient.mk (Ideal.span {(3 : O)}) (3 : O) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))
  have hlevel : integralTranslation (3 * n) ∈ levelThree := by
    change Matrix.SpecialLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3 : O)})) (integralTranslation (3 * n)) = 1
    ext i j
    change (Ideal.Quotient.mk (Ideal.span {(3 : O)})) ((integralTranslation (3 * n)) i j) =
      (1 : Matrix (Fin 2) (Fin 2) (O ⧸ Ideal.span {(3 : O)})) i j
    fin_cases i <;> fin_cases j <;> simp [integralTranslation, h3]
  apply (globalKubotaKernel_mem _).mpr
  refine ⟨hlevel, ?_⟩
  change ringComplex (value ⟨integralTranslation (3 * n), hlevel⟩) = 1
  rw [value_zero_lower_left _ (by rfl), map_one]

lemma kernelProjection_upper_period (v : ℝ) (hv : 0 < v) (z : ℂ) (n : O) :
    integralOrbitProjection globalKubotaKernel (upperPoint (z + 3 * ringComplex n) v hv) =
      integralOrbitProjection globalKubotaKernel (upperPoint z v hv) := by
  let M : globalKubotaKernel := ⟨integralTranslation (3 * n), integralTranslation_three_mem_kernel n⟩
  have ha : integralComplexMatrix (M : SL(2, O)) • upperPoint z v hv =
      upperPoint (z + 3 * ringComplex n) v hv := by
    simpa only [M, map_mul, map_ofNat] using integralTranslation_action (3 * n) z v hv
  rw [← ha, integralOrbitProjection_eq]

/-- A periodic null set is null on the plane once it is null on one period cell. -/
lemma ae_eq_of_periodDomain_eq (f g : ℂ → ℂ)
    (hf : ∀ (n : O) (z : ℂ), f (z + 3 * ringComplex n) = f z)
    (hg : ∀ (n : O) (z : ℂ), g (z + 3 * ringComplex n) = g z)
    (he : f =ᵐ[volume.restrict periodDomain] g) : f =ᵐ[volume] g := by
  have hp (p : periodLattice) (z : ℂ) : f (p +ᵥ z) = f z ∧ g (p +ᵥ z) = g z := by
    obtain ⟨n, rfl⟩ := periodEquiv.surjective p
    change f (3 * ringComplex n + z) = f z ∧ g (3 * ringComplex n + z) = g z
    rw [add_comm]
    exact ⟨hf n z, hg n z⟩
  have hi : ∀ p : periodLattice, p +ᵥ {z : ℂ | f z ≠ g z} = {z : ℂ | f z ≠ g z} := by
    intro p
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change (f ((-p) +ᵥ z) ≠ g ((-p) +ᵥ z)) ↔ f z ≠ g z
    rw [(hp (-p) z).1, (hp (-p) z).2]
  have hz : volume ({z : ℂ | f z ≠ g z} ∩ periodDomain) = 0 := by
    change ∀ᵐ z ∂volume.restrict periodDomain, f z = g z at he
    rw [ae_restrict_iff' periodDomain_measurable, ae_iff] at he
    have hs : {z : ℂ | f z ≠ g z} ∩ periodDomain =
        {z : ℂ | ¬(z ∈ periodDomain → f z = g z)} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      tauto
    rw [hs]
    exact he
  rw [Filter.EventuallyEq, ae_iff]
  exact periodDomain_fundamental.measure_zero_of_invariant _ hi hz

lemma positive_height_interval_cover :
    Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) := by
  ext v
  constructor
  · intro hv
    obtain ⟨n, hn⟩ := exists_nat_gt (max v (1 / v))
    have hN : 0 < (n : ℝ) + 1 := by positivity
    have hvN : v ≤ (n : ℝ) + 1 := by linarith only [hn, le_max_left v (1 / v)]
    have hinv : 1 / v ≤ (n : ℝ) + 1 := by linarith only [hn, le_max_right v (1 / v)]
    have hlow : 1 / ((n : ℝ) + 1) ≤ v := by
      apply (div_le_iff₀ hN).mpr
      simpa only [mul_comm] using (div_le_iff₀ (show 0 < v from hv)).mp hinv
    exact Set.mem_iUnion.mpr ⟨n, hlow, hvN⟩
  · intro hv
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hv
    exact lt_of_lt_of_le (by positivity : 0 < (1 : ℝ) / ((n : ℝ) + 1)) hn.1

lemma cuspCoordinateLift_measurable : Measurable cuspCoordinateLift :=
  euclideanToHyperbolic_measurable.comp spatialComplexSplit.symm.measurable

/-- Coordinate null sets remain null after inserting the hyperbolic volume density. -/
lemma hyperbolic_ae_of_coordinate_ae (f g : HyperbolicSpace → ℂ)
    (hf : Measurable f) (hg : Measurable g)
    (he : ∀ᵐ q ∂(volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure ℂ),
      f (cuspCoordinateLift q) = g (cuspCoordinateLift q)) : f =ᵐ[hyperbolicVolume] g := by
  have hm := spatialComplexSplit_preserves_volume.restrict_preimage
    (s := Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)) (measurableSet_Ioi.prod MeasurableSet.univ)
  have htarget : (volume : Measure (ℝ × ℂ)).restrict (Set.Ioi 0 ×ˢ (Set.univ : Set ℂ)) =
      (volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure ℂ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hsource : spatialComplexSplit ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)) = euclideanUpperHalf := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, Set.mem_Ioi,
      spatialComplexSplit_fst, euclideanUpperHalf, Set.mem_setOf_eq]
  rw [htarget, hsource] at hm
  have heuc := hm.quasiMeasurePreserving.ae he
  have heuc' : ∀ᵐ p ∂volume.restrict euclideanUpperHalf,
      f (euclideanToHyperbolic p) = g (euclideanToHyperbolic p) := by
    simpa only [cuspCoordinateLift, spatialComplexSplit.symm_apply_apply] using heuc
  have hweighted : ∀ᵐ p ∂hyperbolicEuclideanVolume,
      f (euclideanToHyperbolic p) = g (euclideanToHyperbolic p) :=
    heuc'.filter_mono (withDensity_absolutelyContinuous
      (volume.restrict euclideanUpperHalf) hyperbolicDensity).ae_le
  change ∀ᵐ w ∂Measure.map euclideanToHyperbolic hyperbolicEuclideanVolume, f w = g w
  exact (ae_map_iff euclideanToHyperbolic_measurable.aemeasurable (measurableSet_eq_fun hf hg)).mpr hweighted

/-- The convergent Fourier series is the actual residual vector almost everywhere. -/
theorem cubicEisensteinResidue_continuous_representative :
    (fun w => cubicEisensteinResidue (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] cubicResidualFunction := by
  have hplanes (a b : ℝ) (ha : 0 < a) : ∀ᵐ v ∂volume.restrict (Set.Icc a b),
      ∀ᵐ z ∂volume, cubicEisensteinResidue
        (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v, z))) =
          cubicResidualFunction (cuspCoordinateLift (v, z)) := by
    filter_upwards [cubicEisensteinResidue_cell_slices_ae a b ha,
      ae_restrict_mem measurableSet_Icc] with v hv hvm
    have hvp := ha.trans_le hvm.1
    apply ae_eq_of_periodDomain_eq _ _ _ _ hv
    · intro n z
      simp only [cuspCoordinateLift_positive v _ hvp, kernelProjection_upper_period]
    · intro n z
      simpa only [cuspCoordinateLift_positive v _ hvp] using cubicResidualFunction_period v hvp z n
  have hheights : ∀ᵐ v ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ∀ᵐ z ∂volume, cubicEisensteinResidue
        (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v, z))) =
          cubicResidualFunction (cuspCoordinateLift (v, z)) := by
    rw [positive_height_interval_cover, ae_restrict_iUnion_iff]
    intro n
    exact hplanes _ _ (by positivity)
  have hf := (MeasureTheory.Lp.stronglyMeasurable cubicEisensteinResidue).measurable.comp
    (measurable_integralOrbitProjection globalKubotaKernel)
  apply hyperbolic_ae_of_coordinate_ae _ _ hf cubicResidualFunction_continuous.measurable
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (hf.comp cuspCoordinateLift_measurable)
    (cubicResidualFunction_continuous.measurable.comp cuspCoordinateLift_measurable))).mpr hheights

lemma kernelProjection_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      hyperbolicVolume (integralQuotientVolume globalKubotaKernel) := by
  let proj := integralOrbitProjection globalKubotaKernel
  have hp : Measurable proj := measurable_integralOrbitProjection _
  refine ⟨hp, Measure.AbsolutelyContinuous.mk fun S hS hzero => ?_⟩
  rw [Measure.map_apply hp hS]
  have hd : hyperbolicVolume ((proj ⁻¹' S) ∩ hyperbolicFundamentalSet globalKubotaKernel) = 0 := by
    simpa only [integralQuotientVolume, proj,
      Measure.map_apply (measurable_integralOrbitProjection _) hS,
      Measure.restrict_apply ((measurable_integralOrbitProjection _) hS)] using hzero
  have hinv : ∀ M : globalKubotaKernel, M • (proj ⁻¹' S) = proj ⁻¹' S := by
    intro M
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      change proj (M • u) ∈ S
      change proj u ∈ S at hu
      rwa [show proj (M • u) = proj u from integralOrbitProjection_eq _ M u]
    · intro hw
      refine ⟨M⁻¹ • w, ?_, smul_inv_smul M w⟩
      change proj (M⁻¹ • w) ∈ S
      rwa [show proj (M⁻¹ • w) = proj w from integralOrbitProjection_eq _ M⁻¹ w]
  exact (globalKubotaKernel_isFundamentalDomain hyperbolicVolume).measure_zero_of_invariant _ hinv hd

/-- Continuity upgrades the residual L² transformation law to pointwise automorphy. -/
theorem cubicResidualFunction_automorphy (M : levelThree) (w : HyperbolicSpace) :
    cubicResidualFunction (complexMatrix M • w) = complexCharacter M * cubicResidualFunction w := by
  have he : (fun q => cubicEisensteinResidue (kernelLevelAction M q))
      =ᵐ[integralQuotientVolume globalKubotaKernel]
        (fun q => complexCharacter M * cubicEisensteinResidue q) := by
    filter_upwards [kernelLevelPullback_ae_eq M cubicEisensteinResidue,
      Lp.coeFn_smul (complexCharacter M) cubicEisensteinResidue] with q hq hs
    rw [cubicEisensteinResidue_character M] at hq
    exact hq.symm.trans hs
  have hl := kernelProjection_quasiMeasurePreserving.ae_eq_comp he
  have hrep := cubicEisensteinResidue_continuous_representative
  have hcomp := (measurePreserving_smul (complexMatrix M)
    hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp hrep
  have hae : (fun p : HyperbolicSpace => cubicResidualFunction (complexMatrix M • p))
      =ᵐ[hyperbolicVolume] (fun p => complexCharacter M * cubicResidualFunction p) := by
    filter_upwards [hcomp, hl, hrep] with p hp hc hr
    simp only [Function.comp_def, kernelLevelAction_mk] at hc
    exact hp.symm.trans (hc.trans (congrArg (fun z => complexCharacter M * z) hr))
  exact congrFun (Measure.eq_of_ae_eq hae
    (cubicResidualFunction_continuous.comp (continuous_hyperbolic_action (complexMatrix M)))
    (continuous_const.mul cubicResidualFunction_continuous)) w

/-- The trace pairing in the real Eisenstein basis is independent of embedding orientation. -/
lemma complexTrace_real_basis_product (a b u v : ℝ) :
    (((a : ℂ) + (b : ℂ) * ringComplex omega) *
        ((u : ℂ) + (v : ℂ) * ringComplex omega) / ringComplex traceLambda) +
      starRingEnd ℂ (((a : ℂ) + (b : ℂ) * ringComplex omega) *
        ((u : ℂ) + (v : ℂ) * ringComplex omega) / ringComplex traceLambda) =
      ((a * v + b * u - b * v : ℝ) : ℂ) := by
  have hd := ringComplex_ne_zero traceLambda_ne_zero
  rw [map_div₀, complex_traceLambda_conjugate]
  simp only [map_mul, map_add, Complex.conj_ofReal, complex_omega_conjugate]
  field_simp [hd]
  simp only [traceLambda, map_add, map_mul, map_one, map_ofNat]
  push_cast
  ring

lemma exp_two_pi_real_eq_one (t : ℝ)
    (h : Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) = 1) : ∃ n : ℤ, t = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have he : (t : ℂ) = (n : ℂ) := mul_left_cancel₀ hc (hn.trans (mul_comm _ _))
  exact_mod_cast he

/-- Triviality of every normalized trace character characterizes the integral lattice. -/
theorem tracePhase_dual_lattice (z : ℂ)
    (h : ∀ n : O, tracePhase (z * ringComplex n / ringComplex traceLambda) = 1) :
    ∃ q : O, ringComplex q = z := by
  obtain ⟨x, hx⟩ := periodVector.surjective (3 * z)
  rw [periodVector_apply] at hx
  have hz : z = (x 0 : ℂ) + (x 1 : ℂ) * ringComplex omega :=
    (mul_left_cancel₀ (by norm_num : (3 : ℂ) ≠ 0) hx).symm
  have htest (u v : ℤ) :
      Complex.exp (2 * Real.pi * Complex.I *
        ((x 0 * v + x 1 * u - x 1 * v : ℝ) : ℂ)) = 1 := by
    have hh := h (Coordinates.eval u v)
    rw [hz, ringComplex_eval] at hh
    change Complex.exp (2 * Real.pi * Complex.I * (_ + starRingEnd ℂ _)) = 1 at hh
    convert hh using 2
    congr 1
    simpa only [Complex.ofReal_intCast] using
      (complexTrace_real_basis_product (x 0) (x 1) u v).symm
  have hb : Complex.exp (2 * Real.pi * Complex.I * (x 1 : ℂ)) = 1 := by
    simpa only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, zero_add, sub_zero] using htest 1 0
  have ha : Complex.exp (2 * Real.pi * Complex.I * ((x 0 - x 1 : ℝ) : ℂ)) = 1 := by
    simpa only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero] using htest 0 1
  obtain ⟨b, hb'⟩ := exp_two_pi_real_eq_one (x 1) hb
  obtain ⟨a, ha'⟩ := exp_two_pi_real_eq_one (x 0 - x 1) ha
  refine ⟨Coordinates.eval (a + b) b, ?_⟩
  rw [ringComplex_eval, hz, hb', show x 0 = (a : ℝ) + b by linarith only [ha', hb']]
  push_cast
  rfl

def residueAdditive (h c d : O) : ℂ :=
  tracePhase (cuspFrequency h * ringComplex d / ringComplex c)

lemma residueAdditive_add (h c d e : O) :
    residueAdditive h c (d + e) = residueAdditive h c d * residueAdditive h c e := by
  unfold residueAdditive
  rw [map_add, mul_add, add_div, AddChar.map_add_eq_mul]

lemma residueAdditive_congr (h c d e : O) (hc : c ≠ 0) (hde : 3 * c ∣ d - e) :
    residueAdditive h c d = residueAdditive h c e := by
  obtain ⟨n, hn⟩ := hde
  have hd : d = e + 3 * c * n := by linear_combination hn
  rw [hd, residueAdditive_add]
  have hphase : residueAdditive h c (3 * c * n) = 1 := by
    have hcn := ringComplex_ne_zero hc
    have he : cuspFrequency h * ringComplex (3 * c * n) / ringComplex c =
        ringComplex (h * n) / ringComplex traceLambda := by
      simp only [cuspFrequency, map_mul, map_ofNat]
      field_simp
    rw [residueAdditive, he, tracePhase_embedding_div_traceLambda]
  rw [hphase, mul_one]

lemma ramifiedElement_ne_zero (u : Oˣ) (n : ℕ) : (u : O) * lambda ^ n ≠ 0 :=
by
  have hl : lambda ≠ 0 := by
    intro hz
    have hh := lambda_sq_dvd_three
    simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_dvd_iff] at hh
    norm_num at hh
  exact mul_ne_zero u.ne_zero (pow_ne_zero _ hl)

lemma ramifiedElement_level (u : Oˣ) (n : ℕ) (hn : 2 ≤ n) : (3 : O) ∣ (u : O) * lambda ^ n :=
  dvd_mul_of_dvd_right (three_dvd_lambda_sq.trans (pow_dvd_pow lambda hn)) _

lemma ramified_denominator_condition (u : Oˣ) (n : ℕ) (d : O)
    (hd : (3 : O) ∣ d - 1) : denominatorCondition ((u : O) * lambda ^ n) d := by
  have hu : IsCoprime (u : O) d := ⟨↑u⁻¹, 0, by simp⟩
  have hl3 : lambda ∣ (3 : O) := (dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0)).trans lambda_sq_dvd_three
  have hld : IsCoprime lambda d := coprime_of_dvd_sub_one lambda d (hl3.trans hd)
  exact ⟨hu.mul_left hld.pow_left, hd⟩

lemma ramified_symbol_congr_mod_nine (u : Oˣ) (n : ℕ) (d e : O)
    (hd : (3 : O) ∣ d - 1) (he : (3 : O) ∣ e - 1) (hde : (9 : O) ∣ d - e) :
    symbol ((u : O) * lambda ^ n) d = symbol ((u : O) * lambda ^ n) e := by
  have hdp := lambda_sq_dvd_three.trans hd
  have hep := lambda_sq_dvd_three.trans he
  rw [symbol_mul_numerator _ _ d, symbol_mul_numerator _ _ e,
    symbol_pow_numerator _ d hdp, symbol_pow_numerator _ e hep,
    symbol_unit_congr_mod_nine u.val d e u.isUnit hdp hep hde,
    symbol_lambda_congr_mod_nine d e hdp hep hde]

lemma primary_add_nine (d w : O) (hd : (3 : O) ∣ d - 1) : (3 : O) ∣ d + 9 * w - 1 := by
  convert dvd_add hd (show (3 : O) ∣ 9 * w from ⟨3 * w, by ring⟩) using 1
  ring

lemma denominatorRep_mk_congr (c d : O) :
    3 * c ∣ denominatorRep c (Ideal.Quotient.mk (Ideal.span {3 * c}) d) - d := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  exact denominatorRep_spec c _

def ramifiedResidueAdd (u : Oˣ) (n : ℕ) (w : O)
    (r : AdmissibleResidue ((u : O) * lambda ^ n)) : AdmissibleResidue ((u : O) * lambda ^ n) :=
  let c := (u : O) * lambda ^ n
  let d := denominatorRep c r.1 + 9 * w
  ⟨Ideal.Quotient.mk (Ideal.span {3 * c}) d,
    (denominatorCondition_congr c _ d (denominatorRep_mk_congr c d)).mpr
      (ramified_denominator_condition u n d (primary_add_nine _ _ r.2.2))⟩

lemma ramifiedResidueAdd_injective (u : Oˣ) (n : ℕ) (w : O) :
    Function.Injective (ramifiedResidueAdd u n w) := by
  intro r q heq
  have hh := congrArg Subtype.val heq
  change Ideal.Quotient.mk (Ideal.span {3 * ((u : O) * lambda ^ n)}) (denominatorRep _ r.1 + 9 * w) =
    Ideal.Quotient.mk (Ideal.span {3 * ((u : O) * lambda ^ n)}) (denominatorRep _ q.1 + 9 * w) at hh
  simp only [map_add, denominatorRep_spec] at hh
  exact Subtype.ext (add_right_cancel hh)

/-- Translation by nine fixes the cubic symbol and diagonalizes the additive phase. -/
theorem ramified_arithmetic_additive_eigen (h : O) (u : Oˣ) (n : ℕ) (hn : 2 ≤ n) (w : O) :
    residueAdditive h ((u : O) * lambda ^ n) (9 * w) * arithmeticResidueSum h ((u : O) * lambda ^ n) =
      arithmeticResidueSum h ((u : O) * lambda ^ n) := by
  let c := (u : O) * lambda ^ n
  have hc : c ≠ 0 := ramifiedElement_ne_zero u n
  have hlevel : (3 : O) ∣ c := ramifiedElement_level u n hn
  letI : Finite (AdmissibleResidue c) := finite_admissibleResidue c hc
  let e : AdmissibleResidue c ≃ AdmissibleResidue c := Equiv.ofBijective (ramifiedResidueAdd u n w)
    ⟨ramifiedResidueAdd_injective u n w, Finite.surjective_of_injective (ramifiedResidueAdd_injective u n w)⟩
  change _ = ∑' r : AdmissibleResidue c, ringComplex (symbol c (denominatorRep c r.1)) *
    residueAdditive h c (denominatorRep c r.1)
  rw [← e.tsum_eq]
  rw [arithmeticResidueSum, ← tsum_mul_left]
  apply tsum_congr
  intro r
  let d := denominatorRep c r.1
  have hrep : 3 * c ∣ denominatorRep c (ramifiedResidueAdd u n w r).1 - (d + 9 * w) :=
    denominatorRep_mk_congr c (d + 9 * w)
  have hdp := primary_add_nine d w r.2.2
  have hchar : symbol c (denominatorRep c (ramifiedResidueAdd u n w r).1) = symbol c d := by
    rw [row_symbol_congr_modulus c _ (d + 9 * w) hlevel hdp hrep]
    exact ramified_symbol_congr_mod_nine u n (d + 9 * w) d hdp r.2.2 ⟨w, by ring⟩
  change _ = ringComplex (symbol c (denominatorRep c (ramifiedResidueAdd u n w r).1)) *
    residueAdditive h c (denominatorRep c (ramifiedResidueAdd u n w r).1)
  rw [hchar, residueAdditive_congr h c _ (d + 9 * w) hc hrep, residueAdditive_add]
  change residueAdditive h c (9 * w) * (ringComplex (symbol c d) * residueAdditive h c d) = _
  ring

/-- Only finitely many ramified powers can contribute at a fixed nonzero frequency. -/
theorem ramified_arithmetic_support (h : O) (u : Oˣ) (n : ℕ) (hn : 2 ≤ n)
    (hA : arithmeticResidueSum h ((u : O) * lambda ^ n) ≠ 0) : (u : O) * lambda ^ n ∣ 3 * h := by
  let c := (u : O) * lambda ^ n
  have hc := ringComplex_ne_zero (ramifiedElement_ne_zero u n)
  change ringComplex c ≠ 0 at hc
  have hp (w : O) : residueAdditive h c (9 * w) = 1 := by
    apply mul_right_cancel₀ hA
    rw [ramified_arithmetic_additive_eigen h u n hn w, one_mul]
  obtain ⟨q, hq⟩ := tracePhase_dual_lattice (ringComplex (3 * h) / ringComplex c) (by
    intro w
    convert hp w using 1
    unfold residueAdditive cuspFrequency
    simp only [map_mul, map_ofNat]
    congr 1
    field_simp
    ring)
  refine ⟨q, ?_⟩
  apply ringComplex_injective
  rw [map_mul ringComplex c q, hq]
  field_simp [hc]

abbrev CubicUnitResidue (b : O) := {r : O ⧸ Ideal.span {b} // IsUnit r}

/-- Coprime CRT separates the primary denominator condition from the unramified unit condition. -/
def denominatorCRTMap (a b : O) (r : AdmissibleResidue (a * b)) :
    AdmissibleResidue a × CubicUnitResidue b :=
  let d := denominatorRep (a * b) r.1
  (⟨Ideal.Quotient.mk (Ideal.span {3 * a}) d,
      (denominatorCondition_congr a _ d (denominatorRep_mk_congr a d)).mpr
        ⟨r.2.1.of_mul_left_left, r.2.2⟩⟩,
   ⟨Ideal.Quotient.mk (Ideal.span {b}) d,
      (isUnit_quotient_span_iff b d).mpr r.2.1.of_mul_left_right⟩)

lemma denominatorCRTMap_bijective (a b : O) (hab : IsCoprime (3 * a) b) :
    Function.Bijective (denominatorCRTMap a b) := by
  constructor
  · intro r t he
    have h1 := congrArg (fun z : AdmissibleResidue a × CubicUnitResidue b => z.1.1) he
    have h2 := congrArg (fun z : AdmissibleResidue a × CubicUnitResidue b => z.2.1) he
    change Ideal.Quotient.mk (Ideal.span {3 * a}) (denominatorRep (a * b) r.1) =
      Ideal.Quotient.mk (Ideal.span {3 * a}) (denominatorRep (a * b) t.1) at h1
    change Ideal.Quotient.mk (Ideal.span {b}) (denominatorRep (a * b) r.1) =
      Ideal.Quotient.mk (Ideal.span {b}) (denominatorRep (a * b) t.1) at h2
    have hdiv : 3 * (a * b) ∣ denominatorRep (a * b) r.1 - denominatorRep (a * b) t.1 := by
      simpa only [mul_assoc] using hab.mul_dvd
        (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h1))
        (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h2))
    apply Subtype.ext
    rw [← denominatorRep_spec (a * b) r.1, ← denominatorRep_spec (a * b) t.1]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr hdiv)
  · rintro ⟨r, t⟩
    obtain ⟨u, v, huv⟩ := hab
    let delta := denominatorRep a r.1
    let xi := principalResidueRep b t.1
    let d := v * b * delta + u * (3 * a) * xi
    have hda : 3 * a ∣ d - delta := by
      refine ⟨u * (xi - delta), ?_⟩
      dsimp [d]
      linear_combination delta * huv
    have hdb : b ∣ d - xi := by
      refine ⟨v * (delta - xi), ?_⟩
      dsimp [d]
      linear_combination xi * huv
    have hxi : IsCoprime b xi := by
      apply (isUnit_quotient_span_iff b xi).mp
      simpa only [xi, principalResidueRep_spec] using t.2
    have had := (denominatorCondition_congr a d delta hda).mpr r.2
    have hbd : IsCoprime b d := by
      obtain ⟨k, hk⟩ := hdb
      have hd : d = xi + b * k := by linear_combination hk
      rwa [hd, IsCoprime.add_mul_left_right_iff]
    have hd : denominatorCondition (a * b) d := ⟨had.1.mul_left hbd, had.2⟩
    let q : AdmissibleResidue (a * b) := ⟨Ideal.Quotient.mk (Ideal.span {3 * (a * b)}) d,
      (denominatorCondition_congr (a * b) _ d (denominatorRep_mk_congr (a * b) d)).mpr hd⟩
    refine ⟨q, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · change Ideal.Quotient.mk (Ideal.span {3 * a}) (denominatorRep (a * b) q.1) = r.1
      rw [← denominatorRep_spec a r.1]
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      apply Ideal.mem_span_singleton.mpr
      have hh : 3 * a ∣ denominatorRep (a * b) q.1 - d :=
        (show 3 * a ∣ 3 * (a * b) from ⟨b, by ring⟩).trans (denominatorRep_mk_congr (a * b) d)
      simpa only [sub_add_sub_cancel] using dvd_add hh hda
    · change Ideal.Quotient.mk (Ideal.span {b}) (denominatorRep (a * b) q.1) = t.1
      rw [← principalResidueRep_spec b t.1]
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      apply Ideal.mem_span_singleton.mpr
      have hh : b ∣ denominatorRep (a * b) q.1 - d :=
        (show b ∣ 3 * (a * b) from ⟨3 * a, by ring⟩).trans (denominatorRep_mk_congr (a * b) d)
      simpa only [sub_add_sub_cancel] using dvd_add hh hdb

def denominatorCRTEquiv (a b : O) (hab : IsCoprime (3 * a) b) :
    AdmissibleResidue (a * b) ≃ AdmissibleResidue a × CubicUnitResidue b :=
  Equiv.ofBijective (denominatorCRTMap a b) (denominatorCRTMap_bijective a b hab)

/-- The finite cubic Gauss sum at the primitive trace normalization. -/
def cubicUnitGaussSum (h b : O) : ℂ :=
  ∑' r : CubicUnitResidue b, ringComplex (symbol (principalResidueRep b r.1) b) *
    residueAdditive (3 * h) b (principalResidueRep b r.1)

lemma residueAdditive_three_congr (h b d e : O) (hb : b ≠ 0) (hde : b ∣ d - e) :
    residueAdditive (3 * h) b d = residueAdditive (3 * h) b e := by
  obtain ⟨n, hn⟩ := hde
  have hd : d = e + b * n := by linear_combination hn
  have he := ringComplex_ne_zero hb
  rw [hd, residueAdditive_add]
  have hp : residueAdditive (3 * h) b (b * n) = 1 := by
    have harg : cuspFrequency (3 * h) * ringComplex (b * n) / ringComplex b =
        cuspFrequency h * (3 * ringComplex n) := by
      simp only [cuspFrequency, map_mul, map_ofNat]
      field_simp
    rw [residueAdditive, harg, cuspFrequency_period]
  rw [hp, mul_one]

lemma residueAdditive_crt (h a b alpha beta d : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hbez : alpha * b + beta * (3 * a) = 1) :
    residueAdditive h (a * b) d =
      residueAdditive (h * alpha) a d * residueAdditive (3 * (h * beta)) b d := by
  unfold residueAdditive
  rw [← AddChar.map_add_eq_mul]
  congr 1
  have hae := ringComplex_ne_zero ha
  have hbe := ringComplex_ne_zero hb
  have hbeq := congrArg ringComplex hbez
  simp only [map_add, map_mul, map_one, map_ofNat] at hbeq
  simp only [cuspFrequency, map_mul, map_ofNat]
  field_simp [hae, hbe, ringComplex_ne_zero traceLambda_ne_zero]
  linear_combination -(ringComplex h * ringComplex d) * hbeq

lemma arithmetic_crt_summand (h a b alpha beta : O)
    (ha : a ≠ 0) (hb : b ≠ 0) (halevel : (3 : O) ∣ a)
    (hbprimary : lambda ^ 2 ∣ b - 1) (hbez : alpha * b + beta * (3 * a) = 1)
    (r : AdmissibleResidue (a * b)) :
    ringComplex (symbol (a * b) (denominatorRep (a * b) r.1)) *
      residueAdditive h (a * b) (denominatorRep (a * b) r.1) =
      (ringComplex (symbol a (denominatorRep a (denominatorCRTMap a b r).1.1)) *
        residueAdditive (h * alpha) a (denominatorRep a (denominatorCRTMap a b r).1.1)) *
      (ringComplex (symbol (principalResidueRep b (denominatorCRTMap a b r).2.1) b) *
        residueAdditive (3 * (h * beta)) b (principalResidueRep b (denominatorCRTMap a b r).2.1)) := by
  let d := denominatorRep (a * b) r.1
  let delta := denominatorRep a (denominatorCRTMap a b r).1.1
  let xi := principalResidueRep b (denominatorCRTMap a b r).2.1
  have hdprimary := lambda_sq_dvd_three.trans r.2.2
  have hdelta : 3 * a ∣ delta - d := denominatorRep_mk_congr a d
  have hxi : b ∣ xi - d := by
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    exact principalResidueRep_spec b _
  have hchar : symbol (a * b) d = symbol a delta * symbol xi b := by
    rw [symbol_mul_numerator a b d, symbol_reciprocity b d hbprimary hdprimary,
      ← symbol_congr hxi, ← row_symbol_congr_modulus a delta d halevel r.2.2 hdelta]
  change ringComplex (symbol (a * b) d) * residueAdditive h (a * b) d =
    (ringComplex (symbol a delta) * residueAdditive (h * alpha) a delta) *
      (ringComplex (symbol xi b) * residueAdditive (3 * (h * beta)) b xi)
  rw [hchar, map_mul, residueAdditive_crt h a b alpha beta d ha hb hbez,
    residueAdditive_congr (h * alpha) a delta d ha hdelta,
    residueAdditive_three_congr (h * beta) b xi d hb hxi]
  ring

/-- CRT and cubic reciprocity factor the actual residue sum into ramified and unramified sums. -/
theorem arithmeticResidueSum_crt (h a b alpha beta : O)
    (ha : a ≠ 0) (hb : b ≠ 0) (halevel : (3 : O) ∣ a)
    (hbprimary : lambda ^ 2 ∣ b - 1) (hbez : alpha * b + beta * (3 * a) = 1) :
    arithmeticResidueSum h (a * b) =
      arithmeticResidueSum (h * alpha) a * cubicUnitGaussSum (h * beta) b := by
  have hab : IsCoprime (3 * a) b := ⟨beta, alpha, by linear_combination hbez⟩
  let f : AdmissibleResidue a → ℂ := fun r =>
    ringComplex (symbol a (denominatorRep a r.1)) * residueAdditive (h * alpha) a (denominatorRep a r.1)
  let g : CubicUnitResidue b → ℂ := fun r =>
    ringComplex (symbol (principalResidueRep b r.1) b) *
      residueAdditive (3 * (h * beta)) b (principalResidueRep b r.1)
  have heq : arithmeticResidueSum h (a * b) =
      ∑' r : AdmissibleResidue (a * b), f (denominatorCRTEquiv a b hab r).1 * g (denominatorCRTEquiv a b hab r).2 :=
    tsum_congr (arithmetic_crt_summand h a b alpha beta ha hb halevel hbprimary hbez)
  rw [heq, (denominatorCRTEquiv a b hab).tsum_eq (fun r => f r.1 * g r.2)]
  letI : Finite (AdmissibleResidue a) := finite_admissibleResidue a ha
  letI : Finite (O ⧸ Ideal.span {b}) := (Ideal.span {b}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr hb)
  letI : Fintype (AdmissibleResidue a) := Fintype.ofFinite _
  letI : Fintype (CubicUnitResidue b) := Fintype.ofFinite _
  change (∑' r : AdmissibleResidue a × CubicUnitResidue b, f r.1 * g r.2) =
    (∑' r : AdmissibleResidue a, f r) * (∑' t : CubicUnitResidue b, g t)
  simp only [tsum_fintype, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

lemma residueAdditive_mul (h c t d : O) :
    residueAdditive h c (t * d) = residueAdditive (h * t) c d := by
  unfold residueAdditive cuspFrequency
  simp only [map_mul]
  congr 1
  ring

lemma residueAdditive_swap (h c d : O) : residueAdditive h c d = residueAdditive d c h := by
  unfold residueAdditive cuspFrequency
  congr 1
  ring

lemma arithmeticResidueSum_frequency_congr (h k c : O) (hc : c ≠ 0)
    (hh : 3 * c ∣ h - k) : arithmeticResidueSum h c = arithmeticResidueSum k c := by
  apply tsum_congr
  intro r
  congr 1
  change residueAdditive h c (denominatorRep c r.1) = residueAdditive k c (denominatorRep c r.1)
  rw [residueAdditive_swap h, residueAdditive_swap k]
  exact residueAdditive_congr _ c h k hc hh

/-- Multiplication by an admissible denominator twists the frequency by its cubic character. -/
theorem arithmeticResidueSum_frequency_twist (h c t : O) (hc : c ≠ 0)
    (hlevel : (3 : O) ∣ c) (ht : denominatorCondition c t) :
    ringComplex (symbol c t) * arithmeticResidueSum (h * t) c = arithmeticResidueSum h c := by
  have heq := (residueMultiplicationEquiv c hc t ht).tsum_eq
    (fun r : AdmissibleResidue c => ringComplex (symbol c (denominatorRep c r.1)) *
      residueAdditive h c (denominatorRep c r.1))
  calc
    _ = ∑' r : AdmissibleResidue c, ringComplex (symbol c t) *
        (ringComplex (symbol c (denominatorRep c r.1)) * residueAdditive (h * t) c (denominatorRep c r.1)) := by
      rw [tsum_mul_left]
      rfl
    _ = ∑' r : AdmissibleResidue c,
        ringComplex (symbol c (denominatorRep c (residueMultiplicationEquiv c hc t ht r).1)) *
          residueAdditive h c (denominatorRep c (residueMultiplicationEquiv c hc t ht r).1) := by
      apply tsum_congr
      intro r
      change _ = ringComplex (symbol c (denominatorRep c (residueMultiplication c t ht r).1)) *
        residueAdditive h c (denominatorRep c (residueMultiplication c t ht r).1)
      rw [residueMultiplication_phase c hlevel t ht r, map_mul]
      dsimp only [residueMultiplication]
      rw [residueAdditive_congr h c _ (t * denominatorRep c r.1) hc
        (denominatorRep_product_congr c t r.1), residueAdditive_mul]
      ring
    _ = _ := heq

lemma cubicUnitGaussSum_frequency_congr (h k b : O) (hb : b ≠ 0)
    (hh : b ∣ h - k) : cubicUnitGaussSum h b = cubicUnitGaussSum k b := by
  apply tsum_congr
  intro r
  congr 1
  have he (u : O) : residueAdditive (3 * u) b (principalResidueRep b r.1) =
      residueAdditive (3 * principalResidueRep b r.1) b u := by
    unfold residueAdditive cuspFrequency
    simp only [map_mul, map_ofNat]
    congr 1
    ring
  rw [he h, he k]
  exact residueAdditive_three_congr _ b h k hb hh

def cubicUnitResidueMul (b t : O) (ht : IsCoprime b t) (r : CubicUnitResidue b) : CubicUnitResidue b :=
  ⟨Ideal.Quotient.mk (Ideal.span {b}) t * r.1, ((isUnit_quotient_span_iff b t).mpr ht).mul r.2⟩

lemma cubicUnitResidueMul_injective (b t : O) (ht : IsCoprime b t) :
    Function.Injective (cubicUnitResidueMul b t ht) := by
  intro r q heq
  apply Subtype.ext
  exact ((isUnit_quotient_span_iff b t).mpr ht).mul_left_cancel (congrArg Subtype.val heq)

def cubicUnitResidueMulEquiv (b t : O) (hb : b ≠ 0) (ht : IsCoprime b t) :
    CubicUnitResidue b ≃ CubicUnitResidue b := by
  letI : Finite (O ⧸ Ideal.span {b}) := (Ideal.span {b}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr hb)
  exact Equiv.ofBijective (cubicUnitResidueMul b t ht)
    ⟨cubicUnitResidueMul_injective b t ht, Finite.surjective_of_injective (cubicUnitResidueMul_injective b t ht)⟩

lemma cubicUnitResidueMul_rep_congr (b t : O) (ht : IsCoprime b t) (r : CubicUnitResidue b) :
    b ∣ principalResidueRep b (cubicUnitResidueMul b t ht r).1 - t * principalResidueRep b r.1 := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [principalResidueRep_spec, map_mul, principalResidueRep_spec]
  rfl

theorem cubicUnitGaussSum_frequency_twist (h b t : O) (hb : b ≠ 0)
    (ht : IsCoprime b t) :
    ringComplex (symbol t b) * cubicUnitGaussSum (h * t) b = cubicUnitGaussSum h b := by
  have heq := (cubicUnitResidueMulEquiv b t hb ht).tsum_eq
    (fun r : CubicUnitResidue b => ringComplex (symbol (principalResidueRep b r.1) b) *
      residueAdditive (3 * h) b (principalResidueRep b r.1))
  calc
    _ = ∑' r : CubicUnitResidue b, ringComplex (symbol t b) *
        (ringComplex (symbol (principalResidueRep b r.1) b) *
          residueAdditive (3 * (h * t)) b (principalResidueRep b r.1)) := by
      rw [tsum_mul_left]
      rfl
    _ = ∑' r : CubicUnitResidue b,
        ringComplex (symbol (principalResidueRep b (cubicUnitResidueMulEquiv b t hb ht r).1) b) *
          residueAdditive (3 * h) b (principalResidueRep b (cubicUnitResidueMulEquiv b t hb ht r).1) := by
      apply tsum_congr
      intro r
      change _ = ringComplex (symbol (principalResidueRep b (cubicUnitResidueMul b t ht r).1) b) *
        residueAdditive (3 * h) b (principalResidueRep b (cubicUnitResidueMul b t ht r).1)
      rw [symbol_congr (cubicUnitResidueMul_rep_congr b t ht r), symbol_mul_numerator, map_mul,
        residueAdditive_three_congr h b _ (t * principalResidueRep b r.1) hb
          (cubicUnitResidueMul_rep_congr b t ht r), residueAdditive_mul]
      rw [show (3 * h) * t = 3 * (h * t) by ring]
      ring
    _ = _ := heq

/-- Frequency twists remove the auxiliary Bezout coefficients from CRT factorization. -/
theorem arithmeticResidueSum_coprime_product (h a b : O)
    (ha : a ≠ 0) (hb : b ≠ 0) (halevel : (3 : O) ∣ a)
    (hbprimary : lambda ^ 2 ∣ b - 1) (hab : IsCoprime (3 * a) b) :
    arithmeticResidueSum h (a * b) = ringComplex (symbol a b) * ringComplex (symbol (3 * a) b) *
      arithmeticResidueSum h a * cubicUnitGaussSum h b := by
  obtain ⟨beta, alpha, hbez⟩ := hab
  have hbez' : alpha * b + beta * (3 * a) = 1 := by linear_combination hbez
  have hab' : IsCoprime (3 * a) b := ⟨beta, alpha, hbez⟩
  have hbt : denominatorCondition a b := ⟨hab'.of_mul_left_right, three_dvd_lambda_sq.trans hbprimary⟩
  have hA := arithmeticResidueSum_frequency_twist (h * alpha) a b ha halevel hbt
  have hAf : 3 * a ∣ (h * alpha) * b - h := ⟨-h * beta, by linear_combination h * hbez'⟩
  rw [arithmeticResidueSum_frequency_congr _ h a ha hAf] at hA
  have hB := cubicUnitGaussSum_frequency_twist (h * beta) b (3 * a) hb hab'.symm
  have hBf : b ∣ (h * beta) * (3 * a) - h := ⟨-h * alpha, by linear_combination h * hbez'⟩
  rw [cubicUnitGaussSum_frequency_congr _ h b hb hBf] at hB
  rw [arithmeticResidueSum_crt h a b alpha beta ha hb halevel hbprimary hbez', ← hA, ← hB]
  ring

lemma ramified_primary_coprime (u : Oˣ) (n : ℕ) (b : O)
    (hb : lambda ^ 2 ∣ b - 1) : IsCoprime (3 * ((u : O) * lambda ^ n)) b := by
  have hl : IsCoprime lambda b := coprime_of_dvd_sub_one lambda b
    ((dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0)).trans hb)
  have hu : IsCoprime (u : O) b := ⟨↑u⁻¹, 0, by simp⟩
  exact ((primary_coprime_three b hb).symm).mul_left (hu.mul_left hl.pow_left)

theorem arithmeticResidueSum_ramified_split (h : O) (u : Oˣ) (n : ℕ) (hn : 2 ≤ n)
    (b : O) (hb : lambda ^ 2 ∣ b - 1) :
    arithmeticResidueSum h (((u : O) * lambda ^ n) * b) =
      ringComplex (symbol ((u : O) * lambda ^ n) b) *
        ringComplex (symbol (3 * ((u : O) * lambda ^ n)) b) *
        arithmeticResidueSum h ((u : O) * lambda ^ n) * cubicUnitGaussSum h b :=
  arithmeticResidueSum_coprime_product h _ b (ramifiedElement_ne_zero u n)
    (primary_ne_zero b hb) (ramifiedElement_level u n hn) hb (ramified_primary_coprime u n b hb)

lemma ramifiedElement_absNorm (u : Oˣ) (n : ℕ) :
    Ideal.absNorm (Ideal.span {(u : O) * lambda ^ n}) = 3 ^ n := by
  have hu : Ideal.span {(u : O)} = (1 : Ideal O) := by
    rw [Ideal.one_eq_top]
    exact Ideal.span_singleton_eq_top.mpr u.isUnit
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul, hu, map_one, one_mul,
    ← Ideal.span_singleton_pow, map_pow, absNorm_span_lambda]

lemma cubic_three_absNorm : Ideal.absNorm (Ideal.span {(3 : O)}) = 9 := by
  have he : (3 : O) = Coordinates.eval 3 0 := by simp [Coordinates.eval]
  rw [he, Ideal.absNorm_span_singleton, Coordinates.norm_eval]
  norm_num

/-- The ramified support has an explicit frequency-dependent norm bound. -/
theorem ramified_arithmetic_norm_bound (h : O) (hh : h ≠ 0) (u : Oˣ)
    (n : ℕ) (hn : 2 ≤ n) (hA : arithmeticResidueSum h ((u : O) * lambda ^ n) ≠ 0) :
    3 ^ n ≤ 9 * Ideal.absNorm (Ideal.span {h}) := by
  have hI : (Ideal.span {h} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hh
  have hN : 0 < Ideal.absNorm (Ideal.span {h}) :=
    Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  apply Nat.le_of_dvd (by positivity)
  obtain ⟨v, hv⟩ := ramified_arithmetic_support h u n hn hA
  refine ⟨Ideal.absNorm (Ideal.span {v}), ?_⟩
  calc
    _ = Ideal.absNorm (Ideal.span {(3 : O) * h}) := by
      rw [← Ideal.span_singleton_mul_span_singleton, map_mul, cubic_three_absNorm]
    _ = Ideal.absNorm (Ideal.span {((u : O) * lambda ^ n) * v}) := by rw [hv]
    _ = _ := by rw [← Ideal.span_singleton_mul_span_singleton, map_mul, ramifiedElement_absNorm]

/-- The exponent cutoff forced by the ramified additive character. -/
def ramifiedFrequencyBound (h : O) : ℕ := Nat.log 3 (9 * Ideal.absNorm (Ideal.span {h}))

theorem arithmeticResidueSum_ramified_index_bound (h : O) (hh : h ≠ 0)
    (u : Oˣ) (n : ℕ) (hn : 2 ≤ n) (b : O) (hb : lambda ^ 2 ∣ b - 1)
    (hA : arithmeticResidueSum h (((u : O) * lambda ^ n) * b) ≠ 0) :
    n ≤ ramifiedFrequencyBound h := by
  have ha : arithmeticResidueSum h ((u : O) * lambda ^ n) ≠ 0 := by
    intro hz
    apply hA
    rw [arithmeticResidueSum_ramified_split h u n hn b hb, hz, mul_zero, zero_mul]
  exact Nat.le_log_of_pow_le (by decide) (ramified_arithmetic_norm_bound h hh u n hn ha)

lemma arithmeticDirichletTerm_ramified_vanish (s : ℂ) (h : O) (hh : h ≠ 0)
    (u : Oˣ) (n : ℕ) (hn : 2 ≤ n) (b : O) (hb : lambda ^ 2 ∣ b - 1)
    (hout : ramifiedFrequencyBound h < n) :
    arithmeticDirichletTerm s h
      ⟨((u : O) * lambda ^ n) * b, dvd_mul_of_dvd_left (ramifiedElement_level u n hn) b⟩ = 0 := by
  have hA : arithmeticResidueSum h (((u : O) * lambda ^ n) * b) = 0 := by
    by_contra hA
    exact (not_le_of_gt hout) (arithmeticResidueSum_ramified_index_bound h hh u n hn b hb hA)
  simp only [arithmeticDirichletTerm, hA, mul_zero, ite_self]

abbrev NonzeroLevelLower := {c : LevelLower // c.1 ≠ 0}

/-- Unit, ramified power, and canonical unramified ideal generator of a nonzero level-three modulus. -/
def ramifiedLower (u : Oˣ) (n : ℕ) (I : GoodIdeal) : O :=
  ((u : O) * lambda ^ (n + 2)) * primaryIdealGenerator I.1

lemma ramifiedLower_ne_zero (u : Oˣ) (n : ℕ) (I : GoodIdeal) : ramifiedLower u n I ≠ 0 :=
  mul_ne_zero (ramifiedElement_ne_zero u (n + 2)) I.2

lemma ramifiedLower_level (u : Oˣ) (n : ℕ) (I : GoodIdeal) : (3 : O) ∣ ramifiedLower u n I :=
  dvd_mul_of_dvd_left (ramifiedElement_level u (n + 2) (by omega)) _

lemma ramifiedLower_span (u : Oˣ) (n : ℕ) (I : GoodIdeal) :
    Ideal.span {ramifiedLower u n I} = ramifiedIdeal ^ (n + 2) * I.1 := by
  unfold ramifiedLower
  rw [mul_assoc, Ideal.span_singleton_mul_left_unit u.isUnit, lambdaFactor_generator_span]

def ramifiedLowerMap (p : Oˣ × ℕ × GoodIdeal) : NonzeroLevelLower :=
  ⟨⟨ramifiedLower p.1 p.2.1 p.2.2, ramifiedLower_level _ _ _⟩, ramifiedLower_ne_zero _ _ _⟩

lemma ramifiedLowerMap_bijective : Function.Bijective ramifiedLowerMap := by
  constructor
  · rintro ⟨u, n, I⟩ ⟨v, m, J⟩ h
    have hc : ramifiedLower u n I = ramifiedLower v m J := congrArg (fun c : NonzeroLevelLower => c.1.1) h
    have hs := congrArg (fun x : O => Ideal.span {x}) hc
    rw [ramifiedLower_span, ramifiedLower_span] at hs
    have he := lambdaFactorMap_bijective.1 (show lambdaFactorMap (n + 2, I) =
      lambdaFactorMap (m + 2, J) from Subtype.ext hs)
    have hnm : n = m := Nat.add_right_cancel (congrArg Prod.fst he)
    have hIJ : I = J := congrArg Prod.snd he
    subst m
    subst J
    have hl : lambda ^ (n + 2) ≠ 0 := by simpa only [Units.val_one, one_mul] using ramifiedElement_ne_zero 1 (n + 2)
    have huv : u = v := by
      apply Units.ext
      apply mul_right_cancel₀ (mul_ne_zero hl I.2)
      simpa only [ramifiedLower, mul_assoc] using hc
    subst v
    rfl
  · intro c
    let C : NonzeroIdeal := ⟨Ideal.span {c.1.1}, Ideal.span_singleton_eq_bot.not.mpr c.2⟩
    obtain ⟨⟨k, I⟩, hCI⟩ := lambdaFactorMap_bijective.2 C
    have hfact : ramifiedIdeal ^ k * I.1 = Ideal.span {c.1.1} := congrArg Subtype.val hCI
    have hp2 : ramifiedIdeal ^ 2 ∣ ramifiedIdeal ^ k * I.1 := by
      rw [hfact]
      change (Ideal.span {lambda} : Ideal O) ^ 2 ∣ _
      rw [Ideal.span_singleton_pow, Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton]
      exact lambda_sq_dvd_three.trans c.1.2
    have hk : 2 ≤ k := by
      by_contra hh
      have hnot := (goodIdeal_iff_not_ramified I.1).mp I.2
      have hcases : k = 0 ∨ k = 1 := by omega
      rcases hcases with rfl | rfl
      · simp only [pow_zero, one_mul] at hp2
        exact hnot ((dvd_pow_self ramifiedIdeal (by decide : (2 : ℕ) ≠ 0)).trans hp2)
      · rw [pow_one, pow_two] at hp2
        exact hnot ((mul_dvd_mul_iff_left ramifiedIdeal_prime.ne_zero).mp hp2)
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hk
    have hk' : k = n + 2 := by omega
    subst k
    have hspan : Ideal.span {lambda ^ (n + 2) * primaryIdealGenerator I.1} = Ideal.span {c.1.1} :=
      (lambdaFactor_generator_span (n + 2) I).trans (by simpa only [Nat.add_comm] using hfact)
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
    refine ⟨(u, n, I), Subtype.ext (Subtype.ext ?_)⟩
    change ramifiedLower u n I = c.1.1
    simpa only [ramifiedLower, mul_assoc, mul_comm, mul_left_comm] using hu

def ramifiedLowerEquiv : Oˣ × ℕ × GoodIdeal ≃ NonzeroLevelLower :=
  Equiv.ofBijective ramifiedLowerMap ramifiedLowerMap_bijective

lemma arithmeticDirichlet_support_nonzero (s : ℂ) (h : O) :
    Function.support (arithmeticDirichletTerm s h) ⊆ {c : LevelLower | c.1 ≠ 0} := by
  intro c hc hz
  exact hc (by simp only [arithmeticDirichletTerm, hz, ite_true])

theorem arithmeticDirichletSeries_ramified_reindex (s : ℂ) (hs : 2 < s.re) (h : O) :
    arithmeticDirichletSeries s h = ∑' u : Oˣ, ∑' n : ℕ, ∑' I : GoodIdeal,
      arithmeticDirichletTerm s h (ramifiedLowerMap (u, n, I)).1 := by
  have hsum := (arithmeticDirichletTerm_summable_norm s hs h).of_norm
  have hsub : Summable (fun c : NonzeroLevelLower => arithmeticDirichletTerm s h c.1) := hsum.subtype _
  have hp := ramifiedLowerEquiv.summable_iff.mpr hsub
  change Summable (fun p : Oˣ × ℕ × GoodIdeal => arithmeticDirichletTerm s h (ramifiedLowerMap p).1) at hp
  calc
    _ = ∑' c : NonzeroLevelLower, arithmeticDirichletTerm s h c.1 :=
      (tsum_subtype_eq_of_support_subset (arithmeticDirichlet_support_nonzero s h)).symm
    _ = ∑' p : Oˣ × ℕ × GoodIdeal, arithmeticDirichletTerm s h (ramifiedLowerMap p).1 :=
      (ramifiedLowerEquiv.tsum_eq _).symm
    _ = _ := by
      rw [hp.tsum_prod]
      exact tsum_congr (fun u => (hp.prod_factor u).tsum_prod)

/-- At nonzero frequency the ramified index in the scattering series is a finite sum. -/
theorem arithmeticDirichletSeries_finite_ramified (s : ℂ) (hs : 2 < s.re) (h : O) (hh : h ≠ 0) :
    arithmeticDirichletSeries s h =
      ∑' u : Oˣ, ∑ n ∈ Finset.range (ramifiedFrequencyBound h + 1), ∑' I : GoodIdeal,
        arithmeticDirichletTerm s h (ramifiedLowerMap (u, n, I)).1 := by
  rw [arithmeticDirichletSeries_ramified_reindex s hs h]
  apply tsum_congr
  intro u
  apply tsum_eq_sum
  intro n hn
  have hout : ramifiedFrequencyBound h < n + 2 := by
    have hnot : ¬ n < ramifiedFrequencyBound h + 1 := by simpa only [Finset.mem_range] using hn
    omega
  have hzero (I : GoodIdeal) : arithmeticDirichletTerm s h (ramifiedLowerMap (u, n, I)).1 = 0 :=
    arithmeticDirichletTerm_ramified_vanish s h hh u (n + 2) (by omega)
      (primaryIdealGenerator I.1) (primaryIdealGenerator_spec I.1 I.2).2 hout
  simp only [hzero, tsum_zero]

/-- The scattering series is a finite ramified combination of unramified cubic Gauss series. -/
theorem arithmeticDirichletSeries_gauss_expansion (s : ℂ) (hs : 2 < s.re) (h : O) (hh : h ≠ 0) :
    arithmeticDirichletSeries s h =
      ∑' u : Oˣ, ∑ n ∈ Finset.range (ramifiedFrequencyBound h + 1), ∑' I : GoodIdeal,
        ((‖ringComplex (ramifiedLower u n I)‖ ^ 2 : ℝ) : ℂ) ^ (-s) *
          (ringComplex (symbol ((u : O) * lambda ^ (n + 2)) (primaryIdealGenerator I.1)) *
           ringComplex (symbol (3 * ((u : O) * lambda ^ (n + 2))) (primaryIdealGenerator I.1)) *
           arithmeticResidueSum h ((u : O) * lambda ^ (n + 2)) * cubicUnitGaussSum h (primaryIdealGenerator I.1)) := by
  rw [arithmeticDirichletSeries_finite_ramified s hs h hh]
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro n hn
  apply tsum_congr
  intro I
  change arithmeticDirichletTerm s h ⟨ramifiedLower u n I, ramifiedLower_level u n I⟩ = _
  rw [arithmeticDirichletTerm, if_neg (ramifiedLower_ne_zero u n I)]
  dsimp only [ramifiedLower]
  rw [arithmeticResidueSum_ramified_split h u (n + 2) (by omega)
    (primaryIdealGenerator I.1) (primaryIdealGenerator_spec I.1 I.2).2]

lemma principalAddChar_congr (c : O) (χ : AddChar O ℂ)
    (hχ : ∀ x ∈ Ideal.span {c}, χ x = 1) (x y : O) (hxy : c ∣ x - y) : χ x = χ y := by
  calc
    χ x = χ ((x - y) + y) := by rw [sub_add_cancel]
    _ = χ (x - y) * χ y := AddChar.map_add_eq_mul χ _ _
    _ = χ y := by rw [hχ _ (Ideal.mem_span_singleton.mpr hxy), one_mul]

/-- Descent of an additive character trivial on a principal ideal. -/
def principalQuotientAddChar (c : O) (χ : AddChar O ℂ)
    (hχ : ∀ x ∈ Ideal.span {c}, χ x = 1) : AddChar (O ⧸ Ideal.span {c}) ℂ where
  toFun x := χ (principalResidueRep c x)
  map_zero_eq_one' := hχ _ (Ideal.Quotient.eq_zero_iff_mem.mp (principalResidueRep_spec c 0))
  map_add_eq_mul' x y := by
    rw [← AddChar.map_add_eq_mul]
    apply principalAddChar_congr c χ hχ
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    simp only [principalResidueRep_spec, map_add]

lemma principalQuotientAddChar_mk (c : O) (χ : AddChar O ℂ)
    (hχ : ∀ x ∈ Ideal.span {c}, χ x = 1) (x : O) :
    principalQuotientAddChar c χ hχ (Ideal.Quotient.mk (Ideal.span {c}) x) = χ x := by
  apply principalAddChar_congr c χ hχ
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  exact principalResidueRep_spec c _

/-- The normalized trace phase as an additive character of the integral lattice. -/
def residueTraceLinearChar (h c : O) : AddChar O ℂ where
  toFun x := residueAdditive (3 * h) c x
  map_zero_eq_one' := by
    simp only [residueAdditive, map_zero, mul_zero, zero_div, AddChar.map_zero_eq_one]
  map_add_eq_mul' := residueAdditive_add (3 * h) c

lemma residueTraceLinearChar_period (h c : O) (hc : c ≠ 0) (x : O) (hx : x ∈ Ideal.span {c}) :
    residueTraceLinearChar h c x = 1 := by
  have he := residueAdditive_three_congr h c x 0 hc
    (by simpa only [sub_zero] using Ideal.mem_span_singleton.mp hx)
  change residueAdditive (3 * h) c x = 1
  simpa only [residueAdditive, map_zero, mul_zero, zero_div,
    AddChar.map_zero_eq_one] using he

def residueTraceQuotientChar (h c : O) (hc : c ≠ 0) : AddChar (O ⧸ Ideal.span {c}) ℂ :=
  principalQuotientAddChar c (residueTraceLinearChar h c) (residueTraceLinearChar_period h c hc)

lemma residueTraceQuotientChar_mk (h c : O) (hc : c ≠ 0) (x : O) :
    residueTraceQuotientChar h c hc (Ideal.Quotient.mk (Ideal.span {c}) x) = residueAdditive (3 * h) c x :=
  principalQuotientAddChar_mk c _ _ x

/-- The geometric dual-lattice identity proves primitivity at every nonzero modulus. -/
theorem residueTraceQuotientChar_primitive (c : O) (hc : c ≠ 0) :
    (residueTraceQuotientChar 1 c hc).IsPrimitive := by
  intro r hr he
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hc' := ringComplex_ne_zero hc
  obtain ⟨q, hq⟩ := tracePhase_dual_lattice (ringComplex a / ringComplex c) (by
    intro w
    have hh := congrArg (fun ψ : AddChar (O ⧸ Ideal.span {c}) ℂ => ψ (Ideal.Quotient.mk _ w)) he
    simp only [AddChar.mulShift_apply, ← map_mul, residueTraceQuotientChar_mk,
      AddChar.one_apply] at hh
    convert hh using 1
    unfold residueAdditive cuspFrequency
    simp only [map_mul, map_ofNat, mul_one]
    congr 1
    field_simp)
  apply hr
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨q, ?_⟩
  apply ringComplex_injective
  rw [map_mul, hq]
  field_simp [hc']

/-- The ramified cubic phase is additive on the affine primary coordinates modulo three. -/
def ramifiedLinearChar (u : Oˣ) (n : ℕ) : AddChar O ℂ where
  toFun x := ringComplex (symbol ((u : O) * lambda ^ n) (1 + 3 * x))
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    have hp (z : O) : (3 : O) ∣ 1 + 3 * z - 1 := ⟨z, by ring⟩
    have hprod : (3 : O) ∣ (1 + 3 * x) * (1 + 3 * y) - 1 := ⟨x + y + 3 * x * y, by ring⟩
    rw [ramified_symbol_congr_mod_nine u n (1 + 3 * (x + y))
      ((1 + 3 * x) * (1 + 3 * y)) (hp _) hprod ⟨-x * y, by ring⟩,
      symbol_mul_denominator, map_mul]

lemma ramifiedLinearChar_period (u : Oˣ) (n : ℕ) (x : O) (hx : x ∈ Ideal.span {(3 : O)}) :
    ramifiedLinearChar u n x = 1 := by
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp hx
  change ringComplex (symbol ((u : O) * lambda ^ n) (1 + 3 * (3 * w))) = 1
  rw [ramified_symbol_congr_mod_nine u n _ 1 ⟨3 * w, by ring⟩ (by simp) ⟨w, by ring⟩]
  simp

def ramifiedQuotientChar (u : Oˣ) (n : ℕ) : AddChar (O ⧸ Ideal.span {(3 : O)}) ℂ :=
  principalQuotientAddChar 3 (ramifiedLinearChar u n) (ramifiedLinearChar_period u n)

def ramifiedFrequencyChar (k : O) (u : Oˣ) (n : ℕ) : AddChar (O ⧸ Ideal.span {(3 : O)}) ℂ :=
  ramifiedQuotientChar u n * residueTraceQuotientChar k 3 (by norm_num)

lemma ramifiedFrequencyChar_rep (k : O) (u : Oˣ) (n : ℕ) (x : O ⧸ Ideal.span {(3 : O)}) :
    ramifiedFrequencyChar k u n x =
      ringComplex (symbol ((u : O) * lambda ^ n) (1 + 3 * principalResidueRep 3 x)) *
        residueAdditive k 3 (3 * principalResidueRep 3 x) := by
  change ringComplex (symbol ((u : O) * lambda ^ n) (1 + 3 * principalResidueRep 3 x)) *
    residueAdditive (3 * k) 3 (principalResidueRep 3 x) = _
  rw [residueAdditive_mul, mul_comm k 3]

def ramifiedNineSum (k : O) (u : Oˣ) (n : ℕ) : ℂ :=
  ∑' x : O ⧸ Ideal.span {(3 : O)},
    ringComplex (symbol ((u : O) * lambda ^ n) (1 + 3 * principalResidueRep 3 x)) *
      residueAdditive k 3 (1 + 3 * principalResidueRep 3 x)

/-- Orthogonality reduces the nine residue classes to a single character test. -/
theorem ramifiedNineSum_eq_character_test (k : O) (u : Oˣ) (n : ℕ) :
    ramifiedNineSum k u n =
      if ramifiedFrequencyChar k u n = 1 then 9 * residueAdditive k 3 1 else 0 := by
  letI : Finite (O ⧸ Ideal.span {(3 : O)}) := (Ideal.span {(3 : O)}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  letI : Fintype (O ⧸ Ideal.span {(3 : O)}) := Fintype.ofFinite _
  have hcard : (Fintype.card (O ⧸ Ideal.span {(3 : O)}) : ℂ) = 9 := by
    have hh := cubic_three_absNorm
    change Nat.card (O ⧸ Ideal.span {(3 : O)}) = 9 at hh
    exact_mod_cast (show Fintype.card (O ⧸ Ideal.span {(3 : O)}) = 9 by
      simpa only [Nat.card_eq_fintype_card] using hh)
  have he : ramifiedNineSum k u n =
      residueAdditive k 3 1 * ∑' x : O ⧸ Ideal.span {(3 : O)}, ramifiedFrequencyChar k u n x := by
    rw [ramifiedNineSum, ← tsum_mul_left]
    apply tsum_congr
    intro x
    rw [ramifiedFrequencyChar_rep, residueAdditive_add]
    ring
  rw [he, tsum_fintype]
  split_ifs with hchar
  · rw [AddChar.sum_eq_card_of_eq_one hchar, hcard]
    ring
  · rw [AddChar.sum_eq_zero_of_ne_one hchar, mul_zero]

lemma ramified_affine_isUnit (u : Oˣ) (n : ℕ)
    (x : O ⧸ Ideal.span {(u : O) * lambda ^ n}) : IsUnit (1 + 3 * x) := by
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hd := ramified_denominator_condition u n (1 + 3 * d) ⟨d, by ring⟩
  simpa only [map_add, map_one, map_mul, map_ofNat] using
    (isUnit_quotient_span_iff _ _).mpr hd.1

/-- All affine primary classes are units at the ramified prime. -/
def ramifiedAffineEquiv (u : Oˣ) (n : ℕ) :
    (O ⧸ Ideal.span {(u : O) * lambda ^ n}) ≃ AdmissibleResidue ((u : O) * lambda ^ n) :=
  (Equiv.subtypeUnivEquiv (ramified_affine_isUnit u n)).symm.trans (affineResidueEquiv _)

lemma ramified_arithmetic_affine (h : O) (u : Oˣ) (n : ℕ) (hn : 2 ≤ n) :
    arithmeticResidueSum h ((u : O) * lambda ^ n) =
      ∑' x : O ⧸ Ideal.span {(u : O) * lambda ^ n},
        ringComplex (symbol ((u : O) * lambda ^ n) (1 + 3 * principalResidueRep _ x)) *
          residueAdditive h ((u : O) * lambda ^ n) (1 + 3 * principalResidueRep _ x) := by
  rw [arithmeticResidueSum, ← (ramifiedAffineEquiv u n).tsum_eq]
  apply tsum_congr
  intro x
  have hrep : 3 * ((u : O) * lambda ^ n) ∣
      denominatorRep _ ((ramifiedAffineEquiv u n) x).1 -
        (1 + 3 * principalResidueRep ((u : O) * lambda ^ n) x) :=
    denominatorRep_mk_congr _ _
  change ringComplex (symbol ((u : O) * lambda ^ n)
    (denominatorRep _ ((ramifiedAffineEquiv u n) x).1)) *
      residueAdditive h _ (denominatorRep _ ((ramifiedAffineEquiv u n) x).1) = _
  rw [row_symbol_congr_modulus _ _ _ (ramifiedElement_level u n hn) ⟨_, by ring⟩ hrep,
    residueAdditive_congr h _ _ _ (ramifiedElement_ne_zero u n) hrep]

/-- Reduction from a ramified modulus divisible by three to the nine-element residue ring. -/
def ramifiedReduction (u : Oˣ) (n : ℕ) (hn : 2 ≤ n) :
    (O ⧸ Ideal.span {(u : O) * lambda ^ n}) →+* (O ⧸ Ideal.span {(3 : O)}) :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (ramifiedElement_level u n hn))

lemma ramifiedReduction_surjective (u : Oˣ) (n : ℕ) (hn : 2 ≤ n) :
    Function.Surjective (ramifiedReduction u n hn) := Ideal.Quotient.factor_surjective _

lemma ramifiedReduction_rep (u : Oˣ) (n : ℕ) (hn : 2 ≤ n)
    (x : O ⧸ Ideal.span {(u : O) * lambda ^ n}) :
    (3 : O) ∣ principalResidueRep ((u : O) * lambda ^ n) x -
      principalResidueRep 3 (ramifiedReduction u n hn x) := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [principalResidueRep_spec]
  exact congrArg (ramifiedReduction u n hn) (principalResidueRep_spec _ x)

lemma residueAdditive_ramified_scale (h k a d : O) (ha : a ≠ 0) (hk : 3 * h = a * k) :
    residueAdditive h a d = residueAdditive k 3 d := by
  have he := congrArg ringComplex hk
  simp only [map_mul, map_ofNat] at he
  have ha' := ringComplex_ne_zero ha
  have hl := ringComplex_ne_zero traceLambda_ne_zero
  unfold residueAdditive cuspFrequency
  simp only [map_ofNat]
  congr 1
  field_simp [ha', hl]
  linear_combination ringComplex d * he

/-- On its divisibility support, a ramified sum is a complete additive-character sum. -/
theorem ramified_arithmetic_character_test (h k : O) (u : Oˣ) (n : ℕ) (hn : 2 ≤ n)
    (hk : 3 * h = ((u : O) * lambda ^ n) * k) :
    arithmeticResidueSum h ((u : O) * lambda ^ n) =
      if ramifiedFrequencyChar k u n = 1 then ((3 ^ n : ℕ) : ℂ) * residueAdditive k 3 1 else 0 := by
  let a : O := (u : O) * lambda ^ n
  let f := ramifiedReduction u n hn
  let ψ : AddChar (O ⧸ Ideal.span {a}) ℂ :=
    { toFun := fun x => ramifiedFrequencyChar k u n (f x)
      map_zero_eq_one' := by rw [map_zero, AddChar.map_zero_eq_one]
      map_add_eq_mul' := fun x y => by rw [map_add, AddChar.map_add_eq_mul] }
  have htrivial : ψ = 1 ↔ ramifiedFrequencyChar k u n = 1 := by
    constructor
    · intro he
      ext x
      obtain ⟨y, rfl⟩ := ramifiedReduction_surjective u n hn x
      exact congrArg (fun χ : AddChar (O ⧸ Ideal.span {a}) ℂ => χ y) he
    · intro he
      ext x
      change ramifiedFrequencyChar k u n (f x) = 1
      rw [he, AddChar.one_apply]
  have hpoint (x : O ⧸ Ideal.span {a}) :
      ringComplex (symbol a (1 + 3 * principalResidueRep a x)) *
        residueAdditive h a (1 + 3 * principalResidueRep a x) = residueAdditive k 3 1 * ψ x := by
    let d := 1 + 3 * principalResidueRep a x
    let e := 1 + 3 * principalResidueRep 3 (f x)
    have hd : (3 : O) ∣ d - 1 := ⟨_, by dsimp [d]; ring⟩
    have he : (3 : O) ∣ e - 1 := ⟨_, by dsimp [e]; ring⟩
    have h9 : (9 : O) ∣ d - e := by
      obtain ⟨w, hw⟩ := ramifiedReduction_rep u n hn x
      refine ⟨w, ?_⟩
      dsimp [d, e, f, a]
      linear_combination 3 * hw
    change ringComplex (symbol a d) * residueAdditive h a d = _
    rw [ramified_symbol_congr_mod_nine u n d e hd he h9,
      residueAdditive_ramified_scale h k a d (ramifiedElement_ne_zero u n) hk,
      residueAdditive_congr k 3 d e (by norm_num) (by convert h9 using 1; norm_num)]
    change ringComplex (symbol a e) * residueAdditive k 3 e =
      residueAdditive k 3 1 * ramifiedFrequencyChar k u n (f x)
    rw [ramifiedFrequencyChar_rep]
    dsimp [e]
    rw [residueAdditive_add]
    ring
  letI : Finite (O ⧸ Ideal.span {a}) := (Ideal.span {a}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (ramifiedElement_ne_zero u n))
  letI : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  have hcard : (Fintype.card (O ⧸ Ideal.span {a}) : ℂ) = ((3 ^ n : ℕ) : ℂ) := by
    have hc := ramifiedElement_absNorm u n
    change Nat.card (O ⧸ Ideal.span {a}) = 3 ^ n at hc
    exact_mod_cast (show Fintype.card (O ⧸ Ideal.span {a}) = 3 ^ n by
      simpa only [Nat.card_eq_fintype_card] using hc)
  rw [ramified_arithmetic_affine h u n hn]
  have hsum : (∑' x : O ⧸ Ideal.span {a},
      ringComplex (symbol a (1 + 3 * principalResidueRep a x)) *
        residueAdditive h a (1 + 3 * principalResidueRep a x)) =
      residueAdditive k 3 1 * ∑' x, ψ x := by
    rw [← tsum_mul_left]
    exact tsum_congr hpoint
  rw [hsum, tsum_fintype]
  by_cases hchar : ramifiedFrequencyChar k u n = 1
  · rw [AddChar.sum_eq_card_of_eq_one (htrivial.mpr hchar), hcard, if_pos hchar]
    exact mul_comm _ _
  · rw [AddChar.sum_eq_zero_of_ne_one (fun hh => hchar (htrivial.mp hh)), mul_zero, if_neg hchar]

/-- The unramified Dirichlet series with the normalized trace phase. -/
def unramifiedCubicGaussSeries (s : ℂ) (h : O) : ℂ :=
  ∑' I : GoodIdeal, unramifiedNormWeight s I.1 * cubicUnitGaussSum h (primaryIdealGenerator I.1)

/-- Cubic frequency factors disappear away from the modulus. -/
theorem cubicUnitGaussSum_cube_shift (h c t : O) (hc : c ≠ 0)
    (hp : lambda ^ 2 ∣ c - 1) (ht : IsCoprime c t) :
    cubicUnitGaussSum (h * t ^ 3) c = cubicUnitGaussSum h c := by
  have he := cubicUnitGaussSum_frequency_twist h c (t ^ 3) hc ht.pow_right
  rw [symbol_pow_numerator t c hp, symbol_cube_of_isCoprime t c hp ht.symm,
    map_one, one_mul] at he
  exact he

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
