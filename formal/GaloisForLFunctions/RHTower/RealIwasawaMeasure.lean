import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainVolume
import GaloisForLFunctions.RHTower.RealSL2Haar
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-!
# Iwasawa coordinates and the actual real Haar measure

The orbit section identifies SL(2,R) with the upper half-plane times its compact
stabilizer. Its actual cocycle proves that hyperbolic volume times normalized
stabilizer Haar is left invariant. Haar uniqueness identifies the previously
constructed group measure with a positive scalar multiple of this product.

Inversion invariance then makes the inverse image of the modular cell a
finite-measure set, ready for finite-index quotient covers.
-/

open MeasureTheory UpperHalfPlane Topology Set
open scoped NNReal
namespace GaloisForLFunctions.RHTower

instance stabilizerCompactSpace : CompactSpace upperHalfPlaneStabilizer := by
  apply isCompact_iff_compactSpace.mp
  exact UpperHalfPlane.isProperMap_smul_I.isCompact_preimage isCompact_singleton

noncomputable def realIwasawaHomeomorph : SL2R ≃ₜ ℍ × upperHalfPlaneStabilizer where
  toFun g := (g • UpperHalfPlane.I, orbitSectionCocycle g)
  invFun p := UpperHalfPlane.toSL2R p.1 * p.2
  left_inv := orbitSectionCocycle_identity
  right_inv p := by
    obtain ⟨z, k⟩ := p
    have hk : (k : SL2R) • UpperHalfPlane.I = UpperHalfPlane.I :=
      MulAction.mem_stabilizer_iff.mp k.2
    apply Prod.ext
    · simp [mul_smul, hk, UpperHalfPlane.toSL2R_smul_I]
    · apply Subtype.ext
      simp [orbitSectionCocycle, mul_smul, hk, UpperHalfPlane.toSL2R_smul_I]
  continuous_toFun := by
    apply Continuous.prodMk (continuous_id.smul continuous_const)
    apply Continuous.subtype_mk
    exact (UpperHalfPlane.continuous_toSL2R.comp
      (continuous_id.smul continuous_const)).inv.mul continuous_id
  continuous_invFun := (UpperHalfPlane.continuous_toSL2R.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

noncomputable def realStabilizerHaar : Measure upperHalfPlaneStabilizer :=
  Measure.haarMeasure ⊤

instance realStabilizerHaar_isHaarMeasure : realStabilizerHaar.IsHaarMeasure :=
  inferInstanceAs (Measure.haarMeasure ⊤ : Measure upperHalfPlaneStabilizer).IsHaarMeasure

instance realStabilizerHaar_probability : IsProbabilityMeasure realStabilizerHaar :=
  ⟨Measure.haarMeasure_self⟩

noncomputable def realIwasawaMeasure : Measure SL2R :=
  ((volume : Measure ℍ).prod realStabilizerHaar).map realIwasawaHomeomorph.symm

theorem sectionCocycle_continuous (g : SL2R) : Continuous (sectionCocycle g) := by
  apply Continuous.subtype_mk
  exact ((UpperHalfPlane.continuous_toSL2R.comp (continuous_const_smul g)).inv.mul
    continuous_const).mul UpperHalfPlane.continuous_toSL2R

theorem iwasawaSkew_preserving (g : SL2R) :
    MeasurePreserving (fun p : ℍ × upperHalfPlaneStabilizer =>
      (g • p.1, sectionCocycle g p.1 * p.2))
      ((volume : Measure ℍ).prod realStabilizerHaar)
      ((volume : Measure ℍ).prod realStabilizerHaar) := by
  have hbase : MeasurePreserving (fun z : ℍ => g • z) volume volume := by
    exact measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ g) volume
  exact hbase.skew_product (g := fun z k => sectionCocycle g z * k)
    (((sectionCocycle_continuous g).comp continuous_fst).mul continuous_snd).measurable
    (Filter.Eventually.of_forall fun z => map_mul_left_eq_self realStabilizerHaar _)

instance realIwasawaMeasure_leftInvariant : realIwasawaMeasure.IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    let ν := (volume : Measure ℍ).prod realStabilizerHaar
    let T := fun p : ℍ × upperHalfPlaneStabilizer =>
      (g • p.1, sectionCocycle g p.1 * p.2)
    have heq : (fun x : SL2R => g * x) ∘ realIwasawaHomeomorph.symm =
        realIwasawaHomeomorph.symm ∘ T := by
      funext p
      change g * (UpperHalfPlane.toSL2R p.1 * p.2) =
        UpperHalfPlane.toSL2R (g • p.1) * ((sectionCocycle g p.1 : SL2R) * p.2)
      simpa only [mul_assoc] using congrArg (fun a : SL2R => a * p.2)
        (sectionCocycle_identity g p.1).symm
    change Measure.map (g * ·) (Measure.map realIwasawaHomeomorph.symm ν) =
      Measure.map realIwasawaHomeomorph.symm ν
    rw [Measure.map_map (measurable_const_mul g) realIwasawaHomeomorph.symm.measurable, heq,
      ← Measure.map_map realIwasawaHomeomorph.symm.measurable (iwasawaSkew_preserving g).measurable,
      (iwasawaSkew_preserving g).map_eq]

instance realIwasawaMeasure_isHaarMeasure : realIwasawaMeasure.IsHaarMeasure where
  toIsMulLeftInvariant := inferInstance
  toIsFiniteMeasureOnCompacts := Measure.IsFiniteMeasureOnCompacts.map
    ((volume : Measure ℍ).prod realStabilizerHaar) realIwasawaHomeomorph.symm
  toIsOpenPosMeasure := realIwasawaHomeomorph.symm.continuous.isOpenPosMeasure_map
    realIwasawaHomeomorph.symm.surjective

noncomputable def realIwasawaHaarScale : ℝ≥0 :=
  Measure.haarScalarFactor realSL2Haar realIwasawaMeasure

theorem realIwasawaHaarScale_pos : 0 < realIwasawaHaarScale :=
  Measure.haarScalarFactor_pos_of_isHaarMeasure realSL2Haar realIwasawaMeasure

theorem realSL2Haar_eq_iwasawa : realSL2Haar = realIwasawaHaarScale • realIwasawaMeasure :=
  Measure.isMulLeftInvariant_eq_smul realSL2Haar realIwasawaMeasure

theorem realIwasawaHomeomorph_measurePreserving :
    MeasurePreserving realIwasawaHomeomorph realIwasawaMeasure
      ((volume : Measure ℍ).prod realStabilizerHaar) := by
  refine ⟨realIwasawaHomeomorph.measurable, ?_⟩
  rw [realIwasawaMeasure, Measure.map_map realIwasawaHomeomorph.measurable
    realIwasawaHomeomorph.symm.measurable]
  simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using
    (Measure.map_id' (μ := (volume : Measure ℍ).prod realStabilizerHaar))

theorem realIwasawaOrbit_measurePreserving :
    MeasurePreserving (fun g : SL2R => g • UpperHalfPlane.I) realIwasawaMeasure volume :=
  measurePreserving_fst.comp realIwasawaHomeomorph_measurePreserving

theorem realSL2Haar_map_orbit :
    Measure.map (fun g : SL2R => g • UpperHalfPlane.I) realSL2Haar =
      realIwasawaHaarScale • (volume : Measure ℍ) := by
  rw [realSL2Haar_eq_iwasawa, Measure.map_smul, realIwasawaOrbit_measurePreserving.map_eq]

instance realSL2Haar_invInvariant : realSL2Haar.IsInvInvariant := by
  constructor
  let c : ENNReal := Measure.haarScalarFactor realSL2Haar.inv realSL2Haar
  have hc : realSL2Haar.inv = c • realSL2Haar :=
    Measure.isMulLeftInvariant_eq_smul realSL2Haar.inv realSL2Haar
  have htwice : Measure.map Inv.inv (Measure.map Inv.inv realSL2Haar) =
      c ^ 2 • realSL2Haar := by
    rw [← Measure.inv_def realSL2Haar, hc, Measure.map_smul,
      ← Measure.inv_def realSL2Haar, hc, smul_smul, pow_two]
  have hμ : realSL2Haar = c ^ 2 • realSL2Haar := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at htwice
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using htwice
  let K : TopologicalSpace.PositiveCompacts SL2R := Classical.arbitrary _
  have heq : c ^ 2 * realSL2Haar K = 1 ^ 2 * realSL2Haar K := by
    conv_rhs => rw [hμ]
    simp
  have hc2 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).mp heq
  have hc1 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective hc2
  rw [hc, hc1, one_smul]

noncomputable def inverseModularCell : Set SL2R :=
  {g | g⁻¹ • UpperHalfPlane.I ∈ ModularGroup.fd}

theorem inverseModularCell_measurable : MeasurableSet inverseModularCell :=
  ModularGroup.isClosed_fd.measurableSet.preimage
    (continuous_inv.smul continuous_const).measurable

theorem inverseModularCell_haar : realSL2Haar inverseModularCell =
    realIwasawaHaarScale * volume ModularGroup.fd := by
  have horbit : Measurable (fun g : SL2R => g • UpperHalfPlane.I) :=
    (continuous_id.smul continuous_const).measurable
  have hinvOrbit : Measurable (fun g : SL2R => g⁻¹ • UpperHalfPlane.I) :=
    horbit.comp continuous_inv.measurable
  have h : Measure.map (fun g : SL2R => g⁻¹ • UpperHalfPlane.I) realSL2Haar =
      realIwasawaHaarScale • (volume : Measure ℍ) := by
    rw [show (fun g : SL2R => g⁻¹ • UpperHalfPlane.I) =
      (fun g : SL2R => g • UpperHalfPlane.I) ∘ Inv.inv from rfl,
      ← Measure.map_map horbit continuous_inv.measurable, Measure.map_inv_eq_self, realSL2Haar_map_orbit]
  have hset := congrArg (fun μ : Measure ℍ => μ ModularGroup.fd) h
  rw [Measure.map_apply hinvOrbit
    ModularGroup.isClosed_fd.measurableSet] at hset
  exact hset

theorem inverseModularCell_haar_ne_top : realSL2Haar inverseModularCell ≠ ⊤ := by
  rw [inverseModularCell_haar]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top
    GaloisForLFunctions.HTGeometry.volume_fd_ne_top

end GaloisForLFunctions.RHTower
