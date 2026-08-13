import GaloisForLFunctions.RHTower.FieldOneFiniteStageBruhatHalfDensityL2
import GaloisForLFunctions.RHTower.ProfiniteLocallyConstantL2Density
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Angular density and exact finite-place extension

The compact module-one factor in the finite-stage Connes--Marcolli fundamental domain is
profinite.  Its locally constant functions are therefore dense in Haar `L²`.  Moreover every
such function extends, by zero off the local unit locus, to a compactly supported locally constant
function on the literal finite local-field product.

The zero extension is deliberately supported on the exact unit locus: along a rational `S`-unit
orbit only the sign pair `±1` can meet that support.  This is the arithmetic mechanism behind the
dense-range proof of Proposition 2.30.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Function IsDedekindDomain MeasureTheory Set Topology

noncomputable instance fieldOneAdicCompletionTotallyDisconnected
    (v : HeightOneSpectrum ℤ) :
    TotallyDisconnectedSpace (v.adicCompletion ℚ) := by
  letI : IsUltrametricDist (v.adicCompletion ℚ) := inferInstance
  infer_instance

noncomputable instance fieldOneAdicNormOneUnitsTotallyDisconnected
    (v : HeightOneSpectrum ℤ) :
    TotallyDisconnectedSpace (FieldOneAdicNormOneUnits v) := by
  let e := fieldOneAdicNormOneUnitsSphereHomeomorph v
  constructor
  intro s hs hpre x hx y hy
  apply e.injective
  have himg : IsPreconnected (e '' s) :=
    hpre.image e e.continuous.continuousOn
  exact himg.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

noncomputable instance fieldOneFiniteStageNormOneTorusTotallyDisconnected
    (S : Finset (HeightOneSpectrum ℤ)) :
    TotallyDisconnectedSpace (FieldOneFiniteStageNormOneTorus S) :=
  Pi.totallyDisconnectedSpace

noncomputable instance fieldOneFiniteStageModuleOneClassTotallyDisconnected
    (S : Finset (HeightOneSpectrum ℤ)) :
    TotallyDisconnectedSpace (FieldOneFiniteStageModuleOneClass S) := by
  let e := (fieldOneFiniteStageNormOneTorusHomeomorph S).symm
  constructor
  intro s hs hpre x hx y hy
  apply e.injective
  have himg : IsPreconnected (e '' s) :=
    hpre.image e e.continuous.continuousOn
  exact himg.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

/-- The module-one class embedded in the finite local-field product by its unique norm-one
representative. -/
def fieldOneFiniteStageAngularFiniteEmbedding
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S) :
    FieldOneFiniteStageFinitePart S :=
  fun v => (((fieldOneFiniteStageAngularTorusRepresentative S k v).1 :
    (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ)

theorem fieldOneFiniteStageAngularFiniteEmbedding_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageAngularFiniteEmbedding S) := by
  apply continuous_pi
  intro v
  exact Units.continuous_val.comp <|
    continuous_subtype_val.comp <|
      (continuous_apply v).comp
        (fieldOneFiniteStageAngularTorusRepresentative_continuous S)

theorem fieldOneFiniteStageAngularFiniteEmbedding_injective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Injective (fieldOneFiniteStageAngularFiniteEmbedding S) := by
  intro k l h
  apply (fieldOneFiniteStageNormOneTorusContinuousMulEquiv S).symm.injective
  funext v
  apply Subtype.ext
  apply Units.ext
  exact congrFun h v

theorem fieldOneFiniteStageAngularFiniteEmbedding_isClosedEmbedding
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsClosedEmbedding (fieldOneFiniteStageAngularFiniteEmbedding S) :=
  (fieldOneFiniteStageAngularFiniteEmbedding_continuous S).isClosedEmbedding
    (fieldOneFiniteStageAngularFiniteEmbedding_injective S)

/-- Exact unit locus in the selected finite local fields. -/
def fieldOneFiniteStageAngularUnitLocus
    (S : Finset (HeightOneSpectrum ℤ)) :
    Set (FieldOneFiniteStageFinitePart S) :=
  {x | ∀ v, ‖x v‖ = 1}

theorem fieldOneFiniteStageAngularUnitLocus_isClopen
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsClopen (fieldOneFiniteStageAngularUnitLocus S) := by
  have hset : fieldOneFiniteStageAngularUnitLocus S =
      ⋂ v : ↥S, (fun x : FieldOneFiniteStageFinitePart S => x v) ⁻¹'
        Metric.sphere 0 1 := by
    ext x
    simp [fieldOneFiniteStageAngularUnitLocus, mem_sphere_zero_iff_norm]
  rw [hset]
  constructor
  · exact isClosed_iInter fun v =>
      (Metric.isClosed_sphere : IsClosed (Metric.sphere
        (0 : v.1.adicCompletion ℚ) 1)).preimage (continuous_apply v)
  · apply isOpen_iInter_of_finite
    intro v
    letI : IsUltrametricDist (v.1.adicCompletion ℚ) := inferInstance
    exact (IsUltrametricDist.isOpen_sphere
      (0 : v.1.adicCompletion ℚ) one_ne_zero).preimage (continuous_apply v)

theorem fieldOneFiniteStageAngularFiniteEmbedding_range
    (S : Finset (HeightOneSpectrum ℤ)) :
    range (fieldOneFiniteStageAngularFiniteEmbedding S) =
      fieldOneFiniteStageAngularUnitLocus S := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩ v
    exact (fieldOneFiniteStageAngularTorusRepresentative S k v).2
  · intro hx
    let u : FieldOneFiniteStageNormOneTorus S := fun v =>
      ⟨Units.mk0 (x v) (by
          intro hzero
          have := hx v
          rw [hzero, norm_zero] at this
          norm_num at this), hx v⟩
    let k : FieldOneFiniteStageModuleOneClass S :=
      fieldOneFiniteStageNormOneTorusContinuousMulEquiv S u
    refine ⟨k, ?_⟩
    funext v
    change (((fieldOneFiniteStageAngularTorusRepresentative S k v).1 :
      (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ) = x v
    change (((((fieldOneFiniteStageNormOneTorusContinuousMulEquiv S).symm
      ((fieldOneFiniteStageNormOneTorusContinuousMulEquiv S) u)) v).1 :
        (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ) = x v
    simp [u]

/-- The source angular factor as a dense linear subspace of its probability-Haar `L²`. -/
def fieldOneFiniteStageAngularLocallyConstantToL2
    (S : Finset (HeightOneSpectrum ℤ)) :
    LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ →ₗ[ℂ]
      Lp ℂ 2 (fieldOneFiniteStageModuleOneProbabilityHaarMeasure S) :=
  profiniteLocallyConstantToL2

theorem fieldOneFiniteStageAngularLocallyConstantToL2_denseRange
    (S : Finset (HeightOneSpectrum ℤ)) :
    DenseRange (fieldOneFiniteStageAngularLocallyConstantToL2 S) :=
  profiniteLocallyConstantToL2_denseRange

/-- Homeomorphism from the compact angular factor onto its exact local unit locus. -/
def fieldOneFiniteStageAngularUnitLocusHomeomorph
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageModuleOneClass S ≃ₜ
      fieldOneFiniteStageAngularUnitLocus S :=
  (fieldOneFiniteStageAngularFiniteEmbedding_isClosedEmbedding S).toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (fieldOneFiniteStageAngularFiniteEmbedding_range S))

/-- Locally constant zero extension from the compact angular unit locus to the full finite part. -/
def fieldOneFiniteStageAngularZeroExtensionLocallyConstant
    (S : Finset (HeightOneSpectrum ℤ))
    (h : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ) :
    LocallyConstant (FieldOneFiniteStageFinitePart S) ℂ := by
  classical
  let U := fieldOneFiniteStageAngularUnitLocus S
  let hU : IsClopen U := fieldOneFiniteStageAngularUnitLocus_isClopen S
  let hOnU : LocallyConstant U ℂ :=
    LocallyConstant.comap
      ⟨(fieldOneFiniteStageAngularUnitLocusHomeomorph S).symm,
        (fieldOneFiniteStageAngularUnitLocusHomeomorph S).symm.continuous⟩ h
  exact LocallyConstant.piecewise hU.1 hU.compl.1 (union_compl_self U)
    hOnU (LocallyConstant.const (↥(Uᶜ)) 0)
    (by intro x hx; exact (hx.2 hx.1).elim)

theorem fieldOneFiniteStageAngularZeroExtension_apply_embedding
    (S : Finset (HeightOneSpectrum ℤ))
    (h : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ)
    (k : FieldOneFiniteStageModuleOneClass S) :
    fieldOneFiniteStageAngularZeroExtensionLocallyConstant S h
        (fieldOneFiniteStageAngularFiniteEmbedding S k) = h k := by
  rw [fieldOneFiniteStageAngularZeroExtensionLocallyConstant]
  rw [LocallyConstant.piecewise_apply_left]
  change h ((fieldOneFiniteStageAngularUnitLocusHomeomorph S).symm
    ⟨fieldOneFiniteStageAngularFiniteEmbedding S k, ?_⟩) = h k
  · congr 1
    exact (fieldOneFiniteStageAngularUnitLocusHomeomorph S).symm_apply_apply k

theorem fieldOneFiniteStageAngularZeroExtension_eq_zero_off_locus
    (S : Finset (HeightOneSpectrum ℤ))
    (h : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ)
    {x : FieldOneFiniteStageFinitePart S}
    (hx : x ∉ fieldOneFiniteStageAngularUnitLocus S) :
    fieldOneFiniteStageAngularZeroExtensionLocallyConstant S h x = 0 := by
  rw [fieldOneFiniteStageAngularZeroExtensionLocallyConstant]
  rw [LocallyConstant.piecewise_apply_right]
  rfl
  exact hx

theorem fieldOneFiniteStageAngularZeroExtension_hasCompactSupport
    (S : Finset (HeightOneSpectrum ℤ))
    (h : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ) :
    HasCompactSupport
      (fieldOneFiniteStageAngularZeroExtensionLocallyConstant S h :
        FieldOneFiniteStageFinitePart S → ℂ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_range (fieldOneFiniteStageAngularFiniteEmbedding_continuous S))
  change support
    (fieldOneFiniteStageAngularZeroExtensionLocallyConstant S h :
      FieldOneFiniteStageFinitePart S → ℂ) ⊆
    range (fieldOneFiniteStageAngularFiniteEmbedding S)
  intro x hx
  rw [fieldOneFiniteStageAngularFiniteEmbedding_range]
  by_contra hnot
  exact hx (fieldOneFiniteStageAngularZeroExtension_eq_zero_off_locus S h hnot)

/-- Exact compactly supported finite-place lift of an angular locally constant function. -/
def fieldOneFiniteStageAngularBruhatExtension
    (S : Finset (HeightOneSpectrum ℤ)) :
    LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ →ₗ[ℂ]
      FieldOneFiniteStageFiniteBruhatSchwartz S where
  toFun h :=
    ⟨fieldOneFiniteStageAngularZeroExtensionLocallyConstant S h, by
      change HasCompactSupport
        (fieldOneFiniteStageAngularZeroExtensionLocallyConstant S h :
          FieldOneFiniteStageFinitePart S → ℂ)
      exact fieldOneFiniteStageAngularZeroExtension_hasCompactSupport S h⟩
  map_add' h g := by
    apply Subtype.ext
    change fieldOneFiniteStageAngularZeroExtensionLocallyConstant S (h + g) =
      fieldOneFiniteStageAngularZeroExtensionLocallyConstant S h +
        fieldOneFiniteStageAngularZeroExtensionLocallyConstant S g
    ext x
    change fieldOneFiniteStageAngularZeroExtensionLocallyConstant S (h + g) x =
      fieldOneFiniteStageAngularZeroExtensionLocallyConstant S h x +
        fieldOneFiniteStageAngularZeroExtensionLocallyConstant S g x
    by_cases hx : x ∈ fieldOneFiniteStageAngularUnitLocus S
    · rw [← fieldOneFiniteStageAngularFiniteEmbedding_range] at hx
      obtain ⟨k, rfl⟩ := hx
      rw [fieldOneFiniteStageAngularZeroExtension_apply_embedding,
        fieldOneFiniteStageAngularZeroExtension_apply_embedding,
        fieldOneFiniteStageAngularZeroExtension_apply_embedding]
      rfl
    · rw [fieldOneFiniteStageAngularZeroExtension_eq_zero_off_locus S (h + g) hx,
        fieldOneFiniteStageAngularZeroExtension_eq_zero_off_locus S h hx,
        fieldOneFiniteStageAngularZeroExtension_eq_zero_off_locus S g hx]
      simp
  map_smul' c h := by
    apply Subtype.ext
    change fieldOneFiniteStageAngularZeroExtensionLocallyConstant S (c • h) =
      c • fieldOneFiniteStageAngularZeroExtensionLocallyConstant S h
    ext x
    change fieldOneFiniteStageAngularZeroExtensionLocallyConstant S (c • h) x =
      c • fieldOneFiniteStageAngularZeroExtensionLocallyConstant S h x
    by_cases hx : x ∈ fieldOneFiniteStageAngularUnitLocus S
    · rw [← fieldOneFiniteStageAngularFiniteEmbedding_range] at hx
      obtain ⟨k, rfl⟩ := hx
      rw [fieldOneFiniteStageAngularZeroExtension_apply_embedding,
        fieldOneFiniteStageAngularZeroExtension_apply_embedding]
      rfl
    · rw [fieldOneFiniteStageAngularZeroExtension_eq_zero_off_locus S (c • h) hx,
        fieldOneFiniteStageAngularZeroExtension_eq_zero_off_locus S h hx]
      simp

@[simp]
theorem fieldOneFiniteStageAngularBruhatExtension_apply_embedding
    (S : Finset (HeightOneSpectrum ℤ))
    (h : LocallyConstant (FieldOneFiniteStageModuleOneClass S) ℂ)
    (k : FieldOneFiniteStageModuleOneClass S) :
    (fieldOneFiniteStageAngularBruhatExtension S h).1
        (fieldOneFiniteStageAngularFiniteEmbedding S k) = h k :=
  fieldOneFiniteStageAngularZeroExtension_apply_embedding S h k

end

end GaloisForLFunctions.RHTower
