import GaloisForLFunctions.RHTower.ProlateSmallApertureMomentFlag
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Uniform all-rung small-aperture moment fields

For every moment rung `k`, orthogonal removal of all lower aperture moments does
more than expose a pointwise Taylor coefficient.  The rescaled projected Fourier
field converges uniformly on the whole physical unit interval to its nonzero
`k`th coefficient.  Passing through the continuous-map-to-`L²` embedding and
Bochner synthesis upgrades this to norm convergence of rectangular operators.
The limiting synthesis operator is nonzero and has rectangular rank at most one.

This is the operator-level perturbation seed required by the small-aperture
prolate problem.  It does not identify that seed with an actual indexed Slepian
eigenline; that requires the subsequent hierarchical min--max/deflation lift.
-/

open MeasureTheory Filter Topology Set Complex

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry


abbrev UnitPhysicalInterval := Set.Icc (-1 : ℝ) 1

attribute [local instance] Measure.Subtype.measureSpace

noncomputable instance unitPhysicalIntervalVolumeFinite :
    IsFiniteMeasure (volume : Measure UnitPhysicalInterval) := by
  constructor
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

theorem unitPhysicalInterval_volume_isOpenPosMeasure :
    (volume : Measure UnitPhysicalInterval).IsOpenPosMeasure := by
  constructor
  intro U hU hUne hzero
  rcases hUne with ⟨x, hxU⟩
  rcases isOpen_induced_iff.mp hU with ⟨V, hVopen, hVU⟩
  have hxV : (x : ℝ) ∈ V := by
    rw [← Set.mem_preimage, hVU]
    exact hxU
  have hxClosure : (x : ℝ) ∈ closure (Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact x.property
  have hnonempty : (V ∩ Ioo (-1 : ℝ) 1).Nonempty :=
    mem_closure_iff.mp hxClosure V hVopen hxV
  have hopen : IsOpen (V ∩ Ioo (-1 : ℝ) 1) := hVopen.inter isOpen_Ioo
  have himageZero : volume (((↑) : UnitPhysicalInterval → ℝ) '' U) = 0 :=
    Measure.volume_subtype_coe_eq_zero_of_volume_eq_zero
      (u := Icc (-1 : ℝ) 1) (t := U) measurableSet_Icc.nullMeasurableSet hzero
  have hsub : V ∩ Ioo (-1 : ℝ) 1 ⊆
      ((↑) : UnitPhysicalInterval → ℝ) '' U := by
    intro y hy
    let ys : UnitPhysicalInterval := ⟨y, ⟨hy.2.1.le, hy.2.2.le⟩⟩
    refine ⟨ys, ?_, rfl⟩
    rw [← hVU]
    exact hy.1
  exact (hopen.measure_ne_zero volume hnonempty)
    (measure_mono_null hsub himageZero)

noncomputable local instance :
    (volume : Measure UnitPhysicalInterval).IsOpenPosMeasure :=
  unitPhysicalInterval_volume_isOpenPosMeasure

noncomputable local instance apertureMeasureOneIsSeparable :
    IsSeparable (apertureMeasure 1) := by
  rw [apertureMeasure_one_eq]
  infer_instance

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

def apertureMomentFieldCoeff (k n : ℕ) :
    C(UnitPhysicalInterval, UnitApertureL2) where
  toFun x := (((x : ℝ) ^ n : ℝ) : ℂ) •
    fourierGroundVector 1 (apertureMomentResidual k) n
  continuous_toFun := by fun_prop

@[simp] theorem apertureMomentFieldCoeff_apply (k n : ℕ)
    (x : UnitPhysicalInterval) :
    apertureMomentFieldCoeff k n x = (((x : ℝ) ^ n : ℝ) : ℂ) •
      fourierGroundVector 1 (apertureMomentResidual k) n := rfl

theorem norm_apertureMomentFieldCoeff_le (k n : ℕ) :
    ‖apertureMomentFieldCoeff k n‖ ≤
      ‖fourierGroundVector 1 (apertureMomentResidual k) n‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro x
  change ‖(((x : ℝ) ^ n : ℝ) : ℂ) •
    fourierGroundVector 1 (apertureMomentResidual k) n‖ ≤ _
  rw [norm_smul, Complex.norm_real, norm_pow, Real.norm_eq_abs]
  have hx : |(x : ℝ)| ≤ 1 := by
    exact abs_le.mpr x.2
  have hpow : |(x : ℝ)| ^ n ≤ 1 := by
    simpa using (pow_le_one₀ (abs_nonneg (x : ℝ)) hx : |(x : ℝ)| ^ n ≤ 1)
  exact mul_le_of_le_one_left (norm_nonneg _) hpow

theorem summable_norm_apertureMomentFieldCoeff (k : ℕ) :
    Summable (fun n => ‖apertureMomentFieldCoeff k n‖) := by
  have hbase := summable_norm_fourierGroundVector zero_le_one
    (apertureMomentResidual k) (R := 1) zero_le_one
  have hbase' : Summable (fun n =>
      ‖fourierGroundVector 1 (apertureMomentResidual k) n‖) := by
    simpa using hbase
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_apertureMomentFieldCoeff_le k n) hbase'

noncomputable def apertureMomentFourierField (k : ℕ) (c : ℝ) :
    C(UnitPhysicalInterval, UnitApertureL2) :=
  ∑' n : ℕ, c ^ n • apertureMomentFieldCoeff k n

theorem hasSum_apertureMomentFourierField (k : ℕ) (c : ℝ) :
    HasSum (fun n : ℕ => c ^ n • apertureMomentFieldCoeff k n)
      (apertureMomentFourierField k c) := by
  apply Summable.hasSum
  have hbase := summable_norm_apertureMomentFieldCoeff k
  have hmul : Summable (fun n => |c| ^ n *
      ‖apertureMomentFieldCoeff k n‖) := by
    -- factorial decay gives every radius, not only the unit disk
    have hground := summable_norm_fourierGroundVector zero_le_one
      (apertureMomentResidual k) (R := |c|) (abs_nonneg c)
    apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hground
    calc
      |c| ^ n * ‖apertureMomentFieldCoeff k n‖ ≤
          |c| ^ n * ‖fourierGroundVector 1 (apertureMomentResidual k) n‖ :=
        mul_le_mul_of_nonneg_left (norm_apertureMomentFieldCoeff_le k n)
          (pow_nonneg (abs_nonneg c) n)
      _ = ‖fourierGroundVector 1 (apertureMomentResidual k) n‖ * |c| ^ n := by ring
  apply Summable.of_norm
  simpa [norm_smul, Real.norm_eq_abs, abs_pow] using hmul

theorem apertureMomentFourierField_apply (k : ℕ) (c : ℝ)
    (x : UnitPhysicalInterval) :
    apertureMomentFourierField k c x =
      apertureMomentResidual k (apertureFourierL2 1 (c * (x : ℝ))) := by
  have hfield := (ContinuousMap.evalCLM ℂ x).hasSum
    (hasSum_apertureMomentFourierField k c)
  have hfourier := (hasSum_apertureFourierL2 zero_le_one (c * (x : ℝ))).mapL
    (apertureMomentResidual k)
  have hfourier' : HasSum (fun n : ℕ =>
      ((-((c * (x : ℝ) : ℝ) : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ)) •
        apertureMomentResidual k (apertureComplexMonomialL2 1 n))
      (apertureMomentResidual k (apertureFourierL2 1 (c * (x : ℝ)))) := by
    simpa only [map_smul] using hfourier
  have hfield' : HasSum (fun n : ℕ =>
      ((-((c * (x : ℝ) : ℝ) : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ)) •
        apertureMomentResidual k (apertureComplexMonomialL2 1 n))
      (apertureMomentFourierField k c x) := by
    refine hfield.congr_fun (fun n => ?_)
    simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply,
      apertureMomentFieldCoeff_apply, fourierGroundVector]
    have hcoef : ((-((c * (x : ℝ) : ℝ) : ℂ) * Complex.I) ^ n /
        (Nat.factorial n : ℂ)) =
      (((c ^ n : ℝ) : ℂ) * (((x : ℝ) ^ n : ℝ) : ℂ) *
        ((-Complex.I) ^ n / (Nat.factorial n : ℂ))) := by
      push_cast
      rw [mul_pow]
      ring
    rw [hcoef]
    module
  exact tendsto_nhds_unique hfield' hfourier'

theorem apertureMomentFieldCoeff_eq_zero {j k : ℕ} (hjk : j < k) :
    apertureMomentFieldCoeff k j = 0 := by
  apply ContinuousMap.ext
  intro x
  change (((x : ℝ) ^ j : ℝ) : ℂ) •
    fourierGroundVector 1 (apertureMomentResidual k) j = 0
  have hground : fourierGroundVector 1 (apertureMomentResidual k) j = 0 := by
    rw [fourierGroundVector, apertureMomentResidual_monomial_eq_zero hjk, smul_zero]
  rw [hground, smul_zero]

theorem apertureMomentFieldCoeff_ne_zero (k : ℕ) :
    apertureMomentFieldCoeff k k ≠ 0 := by
  intro hzero
  have happ := congrArg (fun f : C(UnitPhysicalInterval, UnitApertureL2) =>
    f (⟨1, by simp⟩ : UnitPhysicalInterval)) hzero
  apply fourierGroundVector_apertureMomentResidual_ne_zero k
  simpa [apertureMomentFieldCoeff] using happ

theorem tendsto_apertureMomentFourierField (k : ℕ) :
    Tendsto (fun c : ℝ => (c ^ k)⁻¹ • apertureMomentFourierField k c)
      (𝓝[≠] (0 : ℝ)) (𝓝 (apertureMomentFieldCoeff k k)) := by
  apply tendsto_smul_inv_pow_of_hasSum_punctured (R := 1) zero_lt_one
    (by simpa using summable_norm_apertureMomentFieldCoeff k)
    (fun j hj => apertureMomentFieldCoeff_eq_zero hj)
  intro c _ _
  exact hasSum_apertureMomentFourierField k c

abbrev UnitPhysicalMomentFieldL2 :=
  Lp UnitApertureL2 2 (volume : Measure UnitPhysicalInterval)

abbrev UnitPhysicalScalarL2 :=
  Lp ℂ 2 (volume : Measure UnitPhysicalInterval)

def apertureMomentFieldToL2 :
    C(UnitPhysicalInterval, UnitApertureL2) →L[ℂ] UnitPhysicalMomentFieldL2 :=
  ContinuousMap.toLp 2 (volume : Measure UnitPhysicalInterval) ℂ

noncomputable def apertureMomentFourierFieldL2 (k : ℕ) (c : ℝ) :
    UnitPhysicalMomentFieldL2 :=
  apertureMomentFieldToL2 (apertureMomentFourierField k c)

noncomputable def apertureMomentLeadingFieldL2 (k : ℕ) :
    UnitPhysicalMomentFieldL2 :=
  apertureMomentFieldToL2 (apertureMomentFieldCoeff k k)

theorem apertureMomentLeadingFieldL2_ne_zero (k : ℕ) :
    apertureMomentLeadingFieldL2 k ≠ 0 := by
  intro hzero
  apply apertureMomentFieldCoeff_ne_zero k
  apply ContinuousMap.toLp_injective (E := UnitApertureL2) (p := 2)
    (𝕜 := ℂ) (volume : Measure UnitPhysicalInterval)
  simpa [apertureMomentLeadingFieldL2, apertureMomentFieldToL2] using hzero

theorem tendsto_apertureMomentFourierFieldL2 (k : ℕ) :
    Tendsto (fun c : ℝ => (c ^ k)⁻¹ • apertureMomentFourierFieldL2 k c)
      (𝓝[≠] (0 : ℝ)) (𝓝 (apertureMomentLeadingFieldL2 k)) := by
  let L := apertureMomentFieldToL2
  have h := L.continuous.continuousAt.tendsto.comp
    (tendsto_apertureMomentFourierField k)
  have hfun : (fun c : ℝ => (c ^ k)⁻¹ • apertureMomentFourierFieldL2 k c) =
      fun c : ℝ => L ((c ^ k)⁻¹ • apertureMomentFourierField k c) := by
    funext c
    exact (L.map_smul_of_tower (c ^ k)⁻¹ (apertureMomentFourierField k c)).symm
  rw [hfun]
  simpa [L, apertureMomentLeadingFieldL2, Function.comp_def] using h

def apertureMomentSynthesisMap :
    UnitPhysicalMomentFieldL2 →L[ℂ]
      (UnitPhysicalScalarL2 →L[ℂ] UnitApertureL2) :=
  ContinuousLinearMap.flip
    ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ]
      UnitApertureL2 →L[ℂ] UnitApertureL2).lpPairing
        (volume : Measure UnitPhysicalInterval) 2 2)

theorem apertureMomentSynthesisMap_apply (u : UnitPhysicalMomentFieldL2) :
    apertureMomentSynthesisMap u =
      l2Synthesis (volume : Measure UnitPhysicalInterval) u := rfl

noncomputable def apertureMomentFourierSynthesis (k : ℕ) (c : ℝ) :
    UnitPhysicalScalarL2 →L[ℂ] UnitApertureL2 :=
  apertureMomentSynthesisMap (apertureMomentFourierFieldL2 k c)

noncomputable def apertureMomentLeadingSynthesis (k : ℕ) :
    UnitPhysicalScalarL2 →L[ℂ] UnitApertureL2 :=
  apertureMomentSynthesisMap (apertureMomentLeadingFieldL2 k)

theorem apertureMomentLeadingSynthesis_ne_zero (k : ℕ) :
    apertureMomentLeadingSynthesis k ≠ 0 := by
  intro hzero
  have henergy :=
    hsNormSq_l2Synthesis_eq_norm_sq
      (volume : Measure UnitPhysicalInterval) (apertureMomentLeadingFieldL2 k)
  have hsynth : l2Synthesis
      (volume : Measure UnitPhysicalInterval) (apertureMomentLeadingFieldL2 k) = 0 := by
    simpa [apertureMomentLeadingSynthesis, apertureMomentSynthesisMap_apply] using hzero
  have henergyZero : ‖apertureMomentLeadingFieldL2 k‖ ^ 2 = 0 := by
    rw [← henergy]
    exact (ContinuousLinearMap.hsNormSq_eq_zero_iff
      (l2Synthesis_isHilbertSchmidt
        (volume : Measure UnitPhysicalInterval) (apertureMomentLeadingFieldL2 k))).2 hsynth
  exact apertureMomentLeadingFieldL2_ne_zero k
    (norm_eq_zero.mp (sq_eq_zero_iff.mp henergyZero))

theorem hasRectRankLE_apertureMomentLeadingSynthesis (k : ℕ) :
    HasRectRankLE (apertureMomentLeadingSynthesis k) 1 := by
  let q : UnitApertureL2 :=
    fourierGroundVector 1 (apertureMomentResidual k) k
  let S : Submodule ℂ UnitApertureL2 := Submodule.span ℂ ({q} : Set UnitApertureL2)
  refine ⟨S, FiniteDimensional.span_of_finite ℂ (Set.finite_singleton q), ?_, ?_⟩
  · exact (finrank_span_le_card ({q} : Set UnitApertureL2)).trans (by simp)
  · intro f
    rw [apertureMomentLeadingSynthesis, apertureMomentSynthesisMap_apply,
      l2Synthesis_apply]
    have hfield : (apertureMomentLeadingFieldL2 k :
        UnitPhysicalInterval → UnitApertureL2) =ᵐ[volume]
        fun x => apertureMomentFieldCoeff k k x := by
      exact ContinuousMap.coeFn_toLp
        (𝕜 := ℂ) (p := (2 : ENNReal))
        (μ := (volume : Measure UnitPhysicalInterval))
        (apertureMomentFieldCoeff k k)
    have hintegral :
        (∫ x, f x • apertureMomentLeadingFieldL2 k x
          ∂(volume : Measure UnitPhysicalInterval)) =
        ∫ x, (f x * (((x : ℝ) ^ k : ℝ) : ℂ)) • q
          ∂(volume : Measure UnitPhysicalInterval) := by
      apply integral_congr_ae
      filter_upwards [hfield] with x hx
      rw [hx, apertureMomentFieldCoeff_apply]
      simp only [q]
      rw [smul_smul]
    have hright :
        (∫ x, (f x * (((x : ℝ) ^ k : ℝ) : ℂ)) • q
          ∂(volume : Measure UnitPhysicalInterval)) ∈ S := by
      rw [integral_smul_const]
      exact S.smul_mem _ (Submodule.subset_span (Set.mem_singleton q))
    exact hintegral.symm ▸ hright

theorem tendsto_apertureMomentFourierSynthesis (k : ℕ) :
    Tendsto (fun c : ℝ => (c ^ k)⁻¹ • apertureMomentFourierSynthesis k c)
      (𝓝[≠] (0 : ℝ)) (𝓝 (apertureMomentLeadingSynthesis k)) := by
  let L := apertureMomentSynthesisMap
  have h := L.continuous.continuousAt.tendsto.comp
    (tendsto_apertureMomentFourierFieldL2 k)
  have hfun : (fun c : ℝ => (c ^ k)⁻¹ • apertureMomentFourierSynthesis k c) =
      fun c : ℝ => L ((c ^ k)⁻¹ • apertureMomentFourierFieldL2 k c) := by
    funext c
    exact (L.map_smul_of_tower (c ^ k)⁻¹ (apertureMomentFourierFieldL2 k c)).symm
  rw [hfun]
  simpa [L, apertureMomentLeadingSynthesis, Function.comp_def] using h

end RHTower

