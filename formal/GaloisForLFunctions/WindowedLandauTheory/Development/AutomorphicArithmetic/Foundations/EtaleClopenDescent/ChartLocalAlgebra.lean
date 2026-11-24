import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalValueDenominators
import GaloisForLFunctions.HTGeometry.AlgebraPointResidueField

/-! The local ring of a chart evaluation inside its ambient field. -/

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace GlobalTheory.WH

variable {k L : Type} [Field k] [Field L] [Algebra k L]
  (B : Subalgebra k L) (e : B →ₐ[k] k)

private abbrev denoms := (RingHom.ker e.toRingHom).primeCompl
private abbrev LocalRing := Localization (denoms B e)

private theorem isUnit_coe_of_denoms (a : denoms B e) : IsUnit (a.val : L) := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  apply a.2
  change e a.val = 0
  rw [show a.val = 0 from Subtype.ext h, map_zero]

/-- Embed the localization at the evaluation kernel into the field. -/
def localChartEmbedding : LocalRing B e →ₐ[k] L :=
  IsLocalization.liftAlgHom (f := B.val) (isUnit_coe_of_denoms B e)

theorem localChartEmbedding_algebraMap (a : B) :
    localChartEmbedding B e (algebraMap B (LocalRing B e) a) = (a : L) :=
  IsLocalization.lift_eq (isUnit_coe_of_denoms B e) a

theorem localChartEmbedding_injective : Function.Injective (localChartEmbedding B e) :=
  (IsLocalization.lift_injective_iff (isUnit_coe_of_denoms B e)).mpr (by
    intro a b
    constructor
    · intro h
      have he := congrArg (fun z : LocalRing B e => localChartEmbedding B e z) h
      change (a : L) = (b : L)
      simpa only [localChartEmbedding_algebraMap] using he
    · intro h
      exact congrArg (algebraMap B (LocalRing B e)) (Subtype.ext h))

/-- The rational functions regular at an evaluation form a subalgebra
of the function field. -/
abbrev loc : Subalgebra k L := (localChartEmbedding B e).range

private def localChartRangeEquiv : LocalRing B e ≃ₐ[k] loc B e :=
  AlgEquiv.ofInjective (localChartEmbedding B e) (localChartEmbedding_injective B e)

/-- Evaluation on the ordinary localization at the point. -/
def localizedEvaluation : LocalRing B e →ₐ[k] k where
  toRingHom := algebraPointLocalizationToField e
  commutes' a := by
    change algebraPointLocalizationToField e (algebraMap k (LocalRing B e) a) = algebraMap k k a
    rw [IsScalarTower.algebraMap_apply k B (LocalRing B e), algebraPointLocalizationToField_algebraMap,
      e.commutes]

/-- The value at the point of a rational function in the local chart algebra. -/
def locEval : loc B e →ₐ[k] k := (localizedEvaluation B e).comp (localChartRangeEquiv B e).symm.toAlgHom

theorem locEval_localChartEmbedding (a : LocalRing B e) :
    locEval B e ⟨localChartEmbedding B e a, ⟨a, rfl⟩⟩ = localizedEvaluation B e a := by
  change localizedEvaluation B e ((localChartRangeEquiv B e).symm
    (localChartRangeEquiv B e a)) = localizedEvaluation B e a
  rw [AlgEquiv.symm_apply_apply]

theorem le_loc : B ≤ loc B e :=
  fun a ha => ⟨algebraMap B (LocalRing B e) ⟨a, ha⟩,
    localChartEmbedding_algebraMap B e ⟨a, ha⟩⟩

/-- Inclusion of the chart into its point-local algebra in the
function field. -/
abbrev localChartAlgebra : Algebra B (loc B e) :=
  (Subalgebra.inclusion (le_loc B e)).toRingHom.toAlgebra

theorem localChart_tower :
    letI := localChartAlgebra B e
    IsScalarTower B (loc B e) L := by
  letI := localChartAlgebra B e
  exact .of_algebraMap_eq fun _ => rfl

theorem localChart_baseTower :
    letI := localChartAlgebra B e
    IsScalarTower k B (loc B e) := by
  letI := localChartAlgebra B e
  exact .of_algebraMap_eq fun _ => rfl

/-- The local subalgebra of the function field has the ordinary
localization universal property. -/
theorem localChart_isLocalization :
    letI := localChartAlgebra B e
    IsLocalization (RingHom.ker e.toRingHom).primeCompl (loc B e) := by
  letI := localChartAlgebra B e
  let f : LocalRing B e ≃ₐ[B] loc B e :=
    { (localChartRangeEquiv B e).toRingEquiv with
      commutes' := fun a => Subtype.ext (localChartEmbedding_algebraMap B e a) }
  exact IsLocalization.isLocalization_of_algEquiv _ f

theorem localizedEvaluation_algebraMap (a : B) :
    localizedEvaluation B e (algebraMap B (LocalRing B e) a) = e a :=
  algebraPointLocalizationToField_algebraMap e a

theorem locEval_inclusion (a : B) :
    locEval B e (Subalgebra.inclusion (le_loc B e) a) = e a := by
  have he : Subalgebra.inclusion (le_loc B e) a =
      localChartRangeEquiv B e (algebraMap B (LocalRing B e) a) :=
    Subtype.ext (localChartEmbedding_algebraMap B e a).symm
  rw [he, locEval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
  exact localizedEvaluation_algebraMap B e a

theorem isUnit_loc_of_eval_ne_zero (a : loc B e) (ha : locEval B e a ≠ 0) : IsUnit a := by
  let b := (localChartRangeEquiv B e).symm a
  have hb : IsUnit b := by
    by_contra hn
    have hm : b ∈ IsLocalRing.maximalIdeal (LocalRing B e) := by
      rwa [IsLocalRing.mem_maximalIdeal]
    rw [← algebraPointLocalizationToField_ker e, RingHom.mem_ker] at hm
    exact ha hm
  have he : localChartRangeEquiv B e b = a := (localChartRangeEquiv B e).apply_symm_apply a
  exact he ▸ hb.map (localChartRangeEquiv B e).toMonoidHom

theorem val_iff_loc (v : L) (c : k) :
    Val B e v c ↔ ∃ hv : v ∈ loc B e, locEval B e ⟨v, hv⟩ = c := by
  have h₁ : Val B e v c ↔ ∃ z : LocalRing B e,
      localChartEmbedding B e z = v ∧ localizedEvaluation B e z = c := by
    constructor
    · rintro ⟨b, hb, hnum, hne, hvalue⟩
      let a : B := ⟨b * v, hnum⟩
      let s : denoms B e := ⟨⟨b, hb⟩, hne⟩
      let z := IsLocalization.mk' (LocalRing B e) a s
      have hz : algebraMap B (LocalRing B e) s.val * z = algebraMap B (LocalRing B e) a :=
        IsLocalization.mk'_spec' _ a s
      have hb₀ : b ≠ 0 := (isUnit_coe_of_denoms B e s).ne_zero
      refine ⟨z, mul_left_cancel₀ hb₀ ?_, mul_left_cancel₀ hne ?_⟩
      · simpa only [map_mul, localChartEmbedding_algebraMap] using congrArg (localChartEmbedding B e) hz
      · simpa only [map_mul, localizedEvaluation_algebraMap, a, s, hvalue]
          using congrArg (localizedEvaluation B e) hz
    · rintro ⟨z, hz, hv⟩
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (denoms B e) z
      have hmul : (s.val : L) * v = a := by
        simpa only [map_mul, localChartEmbedding_algebraMap, hz, mul_comm v]
          using congrArg (localChartEmbedding B e) h
      refine ⟨s.val, s.val.2, hmul.symm ▸ a.2, s.2, ?_⟩
      rw [show (⟨_, _⟩ : B) = a from Subtype.ext hmul]
      simpa only [map_mul, localizedEvaluation_algebraMap, hv, mul_comm c]
        using (congrArg (localizedEvaluation B e) h).symm
  rw [h₁]
  constructor
  · rintro ⟨z, rfl, hz⟩
    exact ⟨⟨z, rfl⟩, by
      change localizedEvaluation B e ((localChartRangeEquiv B e).symm
        (localChartRangeEquiv B e z)) = c
      rwa [AlgEquiv.symm_apply_apply]⟩
  · rintro ⟨h, he⟩
    let z := (localChartRangeEquiv B e).symm ⟨v, h⟩
    exact ⟨z, congrArg Subtype.val ((localChartRangeEquiv B e).apply_symm_apply ⟨v, h⟩), he⟩

theorem val_chartElement (a : B) : Val B e (a : L) (e a) :=
  (val_iff_loc B e _ _).mpr ⟨le_loc B e a.property, locEval_inclusion B e a⟩

theorem val_value_unique {v : L} {a b : k} (ha : Val B e v a) (hb : Val B e v b) : a = b := by
  obtain ⟨h₁, he₁⟩ := (val_iff_loc B e v a).mp ha
  obtain ⟨h₂, he₂⟩ := (val_iff_loc B e v b).mp hb
  exact he₁.symm.trans he₂

theorem val_add {u v : L} {a b : k} (hu : Val B e u a) (hv : Val B e v b) :
    Val B e (u + v) (a + b) := by
  obtain ⟨hu, heu⟩ := (val_iff_loc B e u a).mp hu
  obtain ⟨hv, hev⟩ := (val_iff_loc B e v b).mp hv
  refine (val_iff_loc B e _ _).mpr ⟨add_mem hu hv, ?_⟩
  change locEval B e (⟨u, hu⟩ + ⟨v, hv⟩) = a + b
  rw [map_add, heu, hev]

theorem val_mul {u v : L} {a b : k} (hu : Val B e u a) (hv : Val B e v b) :
    Val B e (u * v) (a * b) := by
  obtain ⟨hu, heu⟩ := (val_iff_loc B e u a).mp hu
  obtain ⟨hv, hev⟩ := (val_iff_loc B e v b).mp hv
  refine (val_iff_loc B e _ _).mpr ⟨mul_mem hu hv, ?_⟩
  change locEval B e (⟨u, hu⟩ * ⟨v, hv⟩) = a * b
  rw [map_mul, heu, hev]

/-- Two evaluations with the same rational values define the same
local subalgebra of the function field. -/
theorem loc_eq_of_val_iff {C : Subalgebra k L} {f : C →ₐ[k] k}
    (h : ∀ v c, Val B e v c ↔ Val C f v c) : loc B e = loc C f := by
  ext v
  constructor
  · intro hv
    exact ((val_iff_loc C f _ _).mp ((h _ _).mp
      ((val_iff_loc B e _ _).mpr ⟨hv, rfl⟩))).choose
  · intro hv
    exact ((val_iff_loc B e _ _).mp ((h _ _).mpr
      ((val_iff_loc C f _ _).mpr ⟨hv, rfl⟩))).choose

end GlobalTheory.WH
