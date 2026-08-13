import GaloisForLFunctions.RHTower.FieldOneFiniteStageIdeleFundamentalDomain
import GaloisForLFunctions.RHTower.FieldOneFiniteStageIdeleLocusMeasure
import GaloisForLFunctions.RHTower.FieldOneFiniteStageIdeleClassHaarSplitting
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Multiplicative Haar from additive Haar on the finite-stage idele locus

Connes--Marcolli's unfolding formula uses the local identity `da = |a| d* a`.  This file proves
its global finite-stage measure-theoretic foundation on the literal adelic objects.  The
coordinatewise value map is an open embedding from ideles onto the conull idele locus.  Pulling
additive Haar back along this embedding gives the exact scaling law under idele multiplication.
Dividing that pullback measure by the module will therefore produce multiplicative Haar.
-/

open scoped ENNReal NNReal Pointwise

namespace GaloisForLFunctions.RHTower

noncomputable section

open Function IsDedekindDomain MeasureTheory MeasureTheory.Measure Set Topology

noncomputable instance fieldOneRealUnitsBorelSpace : BorelSpace ℝˣ := by
  constructor
  unfold Units.instMeasurableSpace
  calc
    MeasurableSpace.comap Units.val
        (inferInstance : MeasurableSpace ℝ) =
        MeasurableSpace.comap Units.val (borel ℝ) :=
      congrArg (MeasurableSpace.comap Units.val)
        (BorelSpace.measurable_eq (α := ℝ))
    _ = borel ℝˣ := by
      rw [Units.isEmbedding_val₀.toIsInducing.eq_induced]
      exact borel_comap.symm

noncomputable instance fieldOneAdicCompletionUnitsBorelSpace
    (v : HeightOneSpectrum ℤ) :
    BorelSpace (v.adicCompletion ℚ)ˣ := by
  constructor
  unfold Units.instMeasurableSpace
  calc
    MeasurableSpace.comap Units.val
        (inferInstance : MeasurableSpace (v.adicCompletion ℚ)) =
      MeasurableSpace.comap Units.val (borel (v.adicCompletion ℚ)) :=
        congrArg (MeasurableSpace.comap Units.val)
          (BorelSpace.measurable_eq (α := v.adicCompletion ℚ))
    _ = borel (v.adicCompletion ℚ)ˣ := by
      rw [Units.isEmbedding_val₀.toIsInducing.eq_induced]
      exact borel_comap.symm

/-- Coordinatewise units are homeomorphic to the coordinatewise nonzero adelic locus. -/
def fieldOneFiniteStageIdeleLocusHomeomorph
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageIdele S ≃ₜ ↥(fieldOneFiniteStageIdeleLocus S) where
  toFun u := ⟨fieldOneFiniteStageIdeleVal S u,
    ⟨Units.ne_zero u.1, fun v => Units.ne_zero (u.2 v)⟩⟩
  invFun x :=
    (Units.mk0 x.1.1 x.2.1,
      fun v => Units.mk0 (x.1.2 v) (x.2.2 v))
  left_inv u := by
    apply Prod.ext
    · apply Units.ext
      rfl
    · funext v
      apply Units.ext
      rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    exact (fieldOneFiniteStageIdeleVal_continuous S).subtype_mk _
  continuous_invFun := by
    apply Continuous.prodMk
    · have hbase : Continuous
          ((fun x : ↥(fieldOneFiniteStageIdeleLocus S) =>
            ⟨x.1.1, x.2.1⟩) :
            ↥(fieldOneFiniteStageIdeleLocus S) → ↥({r : ℝ | r ≠ 0})) :=
        Continuous.subtype_mk
        (continuous_fst.comp continuous_subtype_val) _
      have h := (unitsHomeomorphNeZero (G₀ := ℝ)).symm.continuous.comp hbase
      convert h using 1
      funext x
      apply Units.ext
      symm
      exact congrArg Subtype.val <|
        (unitsHomeomorphNeZero (G₀ := ℝ)).apply_symm_apply
          ⟨x.1.1, x.2.1⟩
    · apply continuous_pi
      intro v
      have hbase : Continuous
          ((fun x : ↥(fieldOneFiniteStageIdeleLocus S) =>
            ⟨x.1.2 v, x.2.2 v⟩) :
            ↥(fieldOneFiniteStageIdeleLocus S) →
              ↥({r : v.1.adicCompletion ℚ | r ≠ 0})) :=
        Continuous.subtype_mk
        ((continuous_apply v).comp
          (continuous_snd.comp continuous_subtype_val)) _
      have h := (unitsHomeomorphNeZero
        (G₀ := v.1.adicCompletion ℚ)).symm.continuous.comp hbase
      convert h using 1
      funext x
      apply Units.ext
      symm
      exact congrArg Subtype.val <|
        (unitsHomeomorphNeZero
          (G₀ := v.1.adicCompletion ℚ)).apply_symm_apply
            ⟨x.1.2 v, x.2.2 v⟩

theorem fieldOneFiniteStageIdeleVal_isOpenEmbedding
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsOpenEmbedding (fieldOneFiniteStageIdeleVal S) := by
  have hlocus : IsOpenEmbedding
      (fun x : ↥(fieldOneFiniteStageIdeleLocus S) =>
        (x.1 : FieldOneFiniteStageAdele S)) :=
    IsOpen.isOpenEmbedding_subtypeVal (fieldOneFiniteStageIdeleLocus_isOpen S)
  have hcomp := hlocus.comp
    (fieldOneFiniteStageIdeleLocusHomeomorph S).isOpenEmbedding
  change IsOpenEmbedding
    ((fun x : ↥(fieldOneFiniteStageIdeleLocus S) => x.1) ∘
      fieldOneFiniteStageIdeleLocusHomeomorph S)
  exact hcomp

/-- Additive Haar restricted to the idele locus, expressed on the idele group itself. -/
def fieldOneFiniteStageIdeleAdditivePullbackMeasure
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageIdele S) :=
  (fieldOneFiniteStageProductAddHaar S).comap
    (fieldOneFiniteStageIdeleVal S)

instance fieldOneFiniteStageProductAddHaar_isAddHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsAddHaarMeasure (fieldOneFiniteStageProductAddHaar S) := by
  change IsAddHaarMeasure
    ((addHaar : Measure ℝ).prod
      (Measure.pi fun v : ↥S =>
        (addHaar : Measure (v.1.adicCompletion ℚ))))
  infer_instance

instance fieldOneFiniteStageIdeleAdditivePullback_isFiniteOnCompacts
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsFiniteMeasureOnCompacts
      (fieldOneFiniteStageIdeleAdditivePullbackMeasure S) :=
  IsFiniteMeasureOnCompacts.comap'
    (fieldOneFiniteStageProductAddHaar S)
    (fieldOneFiniteStageIdeleVal_continuous S)
    (fieldOneFiniteStageIdeleVal_isOpenEmbedding S).measurableEmbedding

instance fieldOneFiniteStageIdeleAdditivePullback_isOpenPos
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsOpenPosMeasure
      (fieldOneFiniteStageIdeleAdditivePullbackMeasure S) :=
  IsOpenPosMeasure.comap
    (fieldOneFiniteStageProductAddHaar S)
    (fieldOneFiniteStageIdeleVal_isOpenEmbedding S)

/-- Pullback additive Haar scales under left multiplication by the inverse module. -/
theorem fieldOneFiniteStageIdeleAdditivePullback_map_mul_left
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) :
    Measure.map (u * ·)
        (fieldOneFiniteStageIdeleAdditivePullbackMeasure S) =
      (fieldOneFiniteStageModule S u⁻¹ : ℝ≥0∞) •
        fieldOneFiniteStageIdeleAdditivePullbackMeasure S := by
  apply Measure.ext
  intro s hs
  have hmul : Measurable (u * ·) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hmul hs,
    fieldOneFiniteStageIdeleAdditivePullbackMeasure,
    (fieldOneFiniteStageIdeleVal_isOpenEmbedding S).measurableEmbedding.comap_apply,
    Measure.smul_apply]
  have himage :
      fieldOneFiniteStageIdeleVal S '' ((u * ·) ⁻¹' s) =
        u⁻¹ • (fieldOneFiniteStageIdeleVal S '' s) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨fieldOneFiniteStageIdeleVal S (u * v), ⟨u * v, hv, rfl⟩, ?_⟩
      rw [fieldOneFiniteStageIdeleVal_mul]
      simp
    · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨u⁻¹ * v, ?_, ?_⟩
      · simpa using hv
      · rw [fieldOneFiniteStageIdeleVal_mul]
  rw [himage, fieldOneFiniteStage_measure_smul]
  rw [(fieldOneFiniteStageIdeleVal_isOpenEmbedding S).measurableEmbedding.comap_apply]
  rfl

private theorem map_withDensity_measurableEquiv
    {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (μ : Measure α) (f : α → ℝ≥0∞)
    (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (f ∘ e.symm) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs]
  let g : α → ℝ≥0∞ := s.indicator (f ∘ e.symm)
  have hg : Measurable g :=
    (hf.comp e.symm.measurable).indicator hs
  calc
    (∫⁻ x in e ⁻¹' s, f x ∂μ) =
        ∫⁻ x, (e ⁻¹' s).indicator f x ∂μ :=
      (lintegral_indicator (hs.preimage e.measurable) _).symm
    _ = ∫⁻ x, g (e x) ∂μ := by
      apply lintegral_congr
      intro x
      by_cases hx : e x ∈ s
      · simp [g, hx]
      · simp [g, hx]
    _ = ∫⁻ y, g y ∂Measure.map e μ :=
      (lintegral_map hg e.measurable).symm
    _ = ∫⁻ y in s, f (e.symm y) ∂Measure.map e μ :=
      lintegral_indicator hs _

/-- Reciprocal module, the exact Radon--Nikodym density `d* a = da / |a|`. -/
def fieldOneFiniteStageIdeleModuleInvDensity
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) : ℝ≥0∞ :=
  ((fieldOneFiniteStageModule S u)⁻¹ : ℝ≥0)

theorem fieldOneFiniteStageModule_ne_zero
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageModule S u ≠ 0 := by
  intro hu
  have h := map_mul_eq_one (fieldOneFiniteStageModule S) (mul_inv_cancel u)
  rw [hu, zero_mul] at h
  exact zero_ne_one h

theorem fieldOneFiniteStageIdeleModuleInvDensity_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageIdeleModuleInvDensity S) := by
  exact ENNReal.continuous_coe.comp
    ((fieldOneFiniteStageModule_continuous S).inv₀
      (fieldOneFiniteStageModule_ne_zero S))

theorem fieldOneFiniteStageIdeleModuleInvDensity_mul_left
    (S : Finset (HeightOneSpectrum ℤ))
    (u x : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageIdeleModuleInvDensity S (u⁻¹ * x) =
      (fieldOneFiniteStageModule S u : ℝ≥0∞) *
        fieldOneFiniteStageIdeleModuleInvDensity S x := by
  simp [fieldOneFiniteStageIdeleModuleInvDensity, map_mul,
    MonoidHom.map_inv, mul_comm]

/-- Multiplicative measure obtained by dividing pulled-back additive Haar by the module. -/
def fieldOneFiniteStageIdeleMultiplicativeFromAdditive
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageIdele S) :=
  (fieldOneFiniteStageIdeleAdditivePullbackMeasure S).withDensity
    (fieldOneFiniteStageIdeleModuleInvDensity S)

instance fieldOneFiniteStageIdeleMultiplicativeFromAdditive_isMulLeftInvariant
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsMulLeftInvariant
      (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S) where
  map_mul_left_eq_self u := by
    let e : FieldOneFiniteStageIdele S ≃ᵐ FieldOneFiniteStageIdele S :=
      (Homeomorph.mulLeft u).toMeasurableEquiv
    have he : (e : FieldOneFiniteStageIdele S → FieldOneFiniteStageIdele S) =
        (u * ·) := rfl
    have hesymm : (e.symm : FieldOneFiniteStageIdele S →
        FieldOneFiniteStageIdele S) = (u⁻¹ * ·) := rfl
    have hdensityMeas : Measurable
        (fieldOneFiniteStageIdeleModuleInvDensity S) :=
      (fieldOneFiniteStageIdeleModuleInvDensity_continuous S).measurable
    rw [fieldOneFiniteStageIdeleMultiplicativeFromAdditive,
      ← he, map_withDensity_measurableEquiv e _ _
        hdensityMeas,
      he, fieldOneFiniteStageIdeleAdditivePullback_map_mul_left,
      withDensity_smul_measure, hesymm]
    have hdensity :
        fieldOneFiniteStageIdeleModuleInvDensity S ∘ (u⁻¹ * ·) =
          (fieldOneFiniteStageModule S u : ℝ≥0∞) •
            fieldOneFiniteStageIdeleModuleInvDensity S := by
      funext x
      exact fieldOneFiniteStageIdeleModuleInvDensity_mul_left S u x
    rw [hdensity, withDensity_smul _ hdensityMeas,
      smul_smul]
    have hu0 : (fieldOneFiniteStageModule S u : ℝ≥0∞) ≠ 0 := by
      exact ENNReal.coe_ne_zero.2 (fieldOneFiniteStageModule_ne_zero S u)
    have huTop : (fieldOneFiniteStageModule S u : ℝ≥0∞) ≠ ∞ :=
      ENNReal.coe_ne_top
    rw [show (fieldOneFiniteStageModule S u⁻¹ : ℝ≥0∞) =
        (fieldOneFiniteStageModule S u : ℝ≥0∞)⁻¹ by
      rw [MonoidHom.map_inv]
      exact ENNReal.coe_inv (fieldOneFiniteStageModule_ne_zero S u),
      ENNReal.inv_mul_cancel hu0 huTop, one_smul]

theorem fieldOneFiniteStageIdeleMultiplicativeFromAdditive_open_pos
    (S : Finset (HeightOneSpectrum ℤ))
    {U : Set (FieldOneFiniteStageIdele S)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    fieldOneFiniteStageIdeleMultiplicativeFromAdditive S U ≠ 0 := by
  rw [fieldOneFiniteStageIdeleMultiplicativeFromAdditive,
    withDensity_apply _ hU.measurableSet]
  apply ne_of_gt
  rw [setLIntegral_pos_iff
    (fieldOneFiniteStageIdeleModuleInvDensity_continuous S).measurable]
  have hsupport : Function.support
      (fieldOneFiniteStageIdeleModuleInvDensity S) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ENNReal.coe_ne_zero.2 <|
      inv_ne_zero (fieldOneFiniteStageModule_ne_zero S x)
  rw [hsupport, Set.univ_inter]
  exact pos_iff_ne_zero.2 <| IsOpenPosMeasure.open_pos U hU hne

theorem fieldOneFiniteStageIdeleMultiplicativeFromAdditive_compact_lt_top
    (S : Finset (HeightOneSpectrum ℤ))
    {K : Set (FieldOneFiniteStageIdele S)} (hK : IsCompact K) :
    fieldOneFiniteStageIdeleMultiplicativeFromAdditive S K < ∞ := by
  let dNN : FieldOneFiniteStageIdele S → ℝ≥0 := fun u =>
    (fieldOneFiniteStageModule S u)⁻¹
  have hdNN : Continuous dNN :=
    (fieldOneFiniteStageModule_continuous S).inv₀
      (fieldOneFiniteStageModule_ne_zero S)
  obtain ⟨C, hC⟩ := (hK.bddAbove_image hdNN.continuousOn)
  have hbound : ∀ x ∈ K,
      fieldOneFiniteStageIdeleModuleInvDensity S x ≤ (C : ℝ≥0∞) := by
    intro x hx
    exact ENNReal.coe_le_coe.2 (hC ⟨x, hx, rfl⟩)
  calc
    fieldOneFiniteStageIdeleMultiplicativeFromAdditive S K =
        ∫⁻ x in K, fieldOneFiniteStageIdeleModuleInvDensity S x
          ∂fieldOneFiniteStageIdeleAdditivePullbackMeasure S := by
      rw [fieldOneFiniteStageIdeleMultiplicativeFromAdditive,
        withDensity_apply _ hK.measurableSet]
    _ ≤ ∫⁻ _x in K, (C : ℝ≥0∞)
        ∂fieldOneFiniteStageIdeleAdditivePullbackMeasure S :=
      setLIntegral_mono measurable_const hbound
    _ = (C : ℝ≥0∞) * fieldOneFiniteStageIdeleAdditivePullbackMeasure S K :=
      setLIntegral_const K (C : ℝ≥0∞)
    _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top hK.measure_lt_top

instance fieldOneFiniteStageIdeleMultiplicativeFromAdditive_isHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsHaarMeasure
      (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S) where
  lt_top_of_isCompact := by
    intro K hK
    exact fieldOneFiniteStageIdeleMultiplicativeFromAdditive_compact_lt_top S hK
  open_pos := by
    intro U hU hne
    exact fieldOneFiniteStageIdeleMultiplicativeFromAdditive_open_pos S hU hne

/-! ## Fundamental-domain product Haar and uniqueness -/

noncomputable instance fieldOneFiniteStageSUnitImageCountable
    (S : Finset (HeightOneSpectrum ℤ)) :
    Countable (fieldOneFiniteStageSUnitImage S) := by
  letI : Countable ℚˣ := Units.val_injective.countable
  letI : Countable (fieldOneSUnitSubgroup S) := Subtype.countable
  let f : fieldOneSUnitSubgroup S → fieldOneFiniteStageSUnitImage S :=
    fun q => ⟨fieldOneFiniteStageDiagonalUnit S q.1,
      fieldOneFiniteStageDiagonalUnit_mem_sUnitImage S q⟩
  apply Function.Surjective.countable (f := f)
  intro u
  have hu := u.2
  change u.1 ∈ Subgroup.map
    (fieldOneFiniteStageDiagonalUnit S) (fieldOneSUnitSubgroup S) at hu
  rw [Subgroup.mem_map] at hu
  obtain ⟨q, hq, hqu⟩ := hu
  exact ⟨⟨q, hq⟩, Subtype.ext hqu⟩

instance fieldOneFiniteStageSUnitImageCount_isOpenPos
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsOpenPosMeasure (count : Measure (fieldOneFiniteStageSUnitImage S)) where
  open_pos U _hU hne := Measure.count_ne_zero hne

instance fieldOneFiniteStageSUnitImageCount_isHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsHaarMeasure (count : Measure (fieldOneFiniteStageSUnitImage S)) where
  lt_top_of_isCompact := by
    intro K hK
    rw [Measure.count_apply_finite K hK.finite_of_discrete]
    exact ENNReal.natCast_lt_top _

/-- Counting measure on the diagonal lattice times the exact split Haar fundamental domain. -/
def fieldOneFiniteStageIdeleFundamentalProductMeasure
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (fieldOneFiniteStageSUnitImage S ×
      (FieldOneFiniteStageModuleOneClass S × NNRealˣ)) :=
  (count : Measure (fieldOneFiniteStageSUnitImage S)).prod
    (fieldOneFiniteStageSplitProductHaarMeasure S)

instance fieldOneFiniteStageIdeleFundamentalProduct_isHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsHaarMeasure (fieldOneFiniteStageIdeleFundamentalProductMeasure S) := by
  change IsHaarMeasure
    ((count : Measure (fieldOneFiniteStageSUnitImage S)).prod
      (fieldOneFiniteStageSplitProductHaarMeasure S))
  infer_instance

/-- Product fundamental-domain Haar transported to the literal idele group. -/
def fieldOneFiniteStageIdeleFundamentalHaarMeasure
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageIdele S) :=
  Measure.map (fieldOneFiniteStageIdeleImageFundamentalContinuousMulEquiv S)
    (fieldOneFiniteStageIdeleFundamentalProductMeasure S)

instance fieldOneFiniteStageIdeleFundamentalHaar_isHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsHaarMeasure (fieldOneFiniteStageIdeleFundamentalHaarMeasure S) :=
  (fieldOneFiniteStageIdeleImageFundamentalContinuousMulEquiv S).isHaarMeasure_map
    (fieldOneFiniteStageIdeleFundamentalProductMeasure S)

/-- Exact global form of `d* a = da / |a|`: the multiplicative measure derived from additive Haar
is a finite positive scalar multiple of counting measure on `Q_S^*` times Haar on the canonical
fundamental domain.  No quotient-measure premise is used. -/
theorem fieldOneFiniteStageIdeleMultiplicativeFromAdditive_eq_fundamentalHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageIdeleMultiplicativeFromAdditive S =
      haarScalarFactor
          (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S)
          (fieldOneFiniteStageIdeleFundamentalHaarMeasure S) •
        fieldOneFiniteStageIdeleFundamentalHaarMeasure S :=
  isMulLeftInvariant_eq_smul _ _

theorem fieldOneFiniteStageIdeleMultiplicative_fundamentalScalar_pos
    (S : Finset (HeightOneSpectrum ℤ)) :
    0 < haarScalarFactor
      (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S)
      (fieldOneFiniteStageIdeleFundamentalHaarMeasure S) :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

/-- Exact Tonelli unfolding over the literal diagonal `S`-unit lattice and canonical idele-class
fundamental domain.  This is the nonnegative measure identity underlying Connes--Marcolli
equations (2.250)--(2.251). -/
theorem fieldOneFiniteStageIdeleMultiplicative_lintegral_fundamental
    (S : Finset (HeightOneSpectrum ℤ))
    (F : FieldOneFiniteStageIdele S → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u, F u ∂fieldOneFiniteStageIdeleMultiplicativeFromAdditive S) =
      (haarScalarFactor
          (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S)
          (fieldOneFiniteStageIdeleFundamentalHaarMeasure S) : ℝ≥0∞) *
        ∫⁻ z,
          ∑' h : fieldOneFiniteStageSUnitImage S,
            F (h.1 * fieldOneFiniteStageIdeleFundamentalSection S z)
          ∂fieldOneFiniteStageSplitProductHaarMeasure S := by
  let c := haarScalarFactor
    (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S)
    (fieldOneFiniteStageIdeleFundamentalHaarMeasure S)
  change (∫⁻ u, F u
      ∂fieldOneFiniteStageIdeleMultiplicativeFromAdditive S) =
    (c : ℝ≥0∞) * _
  have hmeasure :=
    fieldOneFiniteStageIdeleMultiplicativeFromAdditive_eq_fundamentalHaar S
  change fieldOneFiniteStageIdeleMultiplicativeFromAdditive S =
      c • fieldOneFiniteStageIdeleFundamentalHaarMeasure S at hmeasure
  conv_lhs => rw [hmeasure]
  rw [lintegral_smul_measure]
  change (c : ℝ≥0∞) •
      (∫⁻ u, F u ∂fieldOneFiniteStageIdeleFundamentalHaarMeasure S) = _
  rw [fieldOneFiniteStageIdeleFundamentalHaarMeasure]
  simp only [smul_eq_mul]
  have hmap := lintegral_map
    (μ := fieldOneFiniteStageIdeleFundamentalProductMeasure S)
    hF (fieldOneFiniteStageIdeleImageFundamentalContinuousMulEquiv S).measurable
  have hfun :
      (fieldOneFiniteStageIdeleImageFundamentalContinuousMulEquiv S :
        _ → FieldOneFiniteStageIdele S) =
      (fieldOneFiniteStageIdeleImageFundamentalContinuousMulEquiv S).toHomeomorph := by
    funext x
    rfl
  have hmap' :
      (∫⁻ u, F u
        ∂Measure.map
          (fieldOneFiniteStageIdeleImageFundamentalContinuousMulEquiv S :
            _ → FieldOneFiniteStageIdele S)
          (fieldOneFiniteStageIdeleFundamentalProductMeasure S)) =
        ∫⁻ x,
          F (fieldOneFiniteStageIdeleImageFundamentalContinuousMulEquiv S x)
          ∂fieldOneFiniteStageIdeleFundamentalProductMeasure S := by
    rw [hfun]
    exact hmap
  rw [hmap']
  change (c : ℝ≥0∞) *
      (∫⁻ x,
        F (fieldOneFiniteStageIdeleImageFundamentalMap S x)
        ∂fieldOneFiniteStageIdeleFundamentalProductMeasure S) = _
  rw [fieldOneFiniteStageIdeleFundamentalProductMeasure,
    lintegral_prod_symm']
  · congr 2
    funext z
    rw [lintegral_count]
    rfl
  · exact hF.comp
      (fieldOneFiniteStageIdeleImageFundamentalMap_continuous S).measurable

end

end GaloisForLFunctions.RHTower
