import GaloisForLFunctions.RHTower.XiPairedFieldIntersection
import GaloisForLFunctions.RHTower.XiStripReflection
import GaloisForLFunctions.HTGeometry.InvariantFieldEmbedding

noncomputable section
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry

theorem pairedRadicand_reflect (j : Bool × ℕ) :
    planeReflectEquiv 1 (pairedRadicand j) = pairedRadicand (!j.1, j.2) := by
  rcases j with ⟨b, n⟩
  cases b with
  | false =>
    rw [pairedRadicand, map_mul, planeReflectEquiv_xiElement]
    rfl
  | true =>
    rw [pairedRadicand, map_mul, planeReflectEquiv_xiElement]
    change xiElement * planeReflectEquiv 1
      (planeReflectEquiv 1 (factorElement (n + 2))) = xiElement * factorElement (n + 2)
    rw [planeReflectEquiv_involutive]

theorem stripClosureEmbedding_pairedRoot_mem (j : Bool × ℕ) :
    stripClosureEmbedding (pairedRoot j) ∈ stripQuadraticField := by
  rcases j with ⟨b, n⟩
  cases b with
  | false => exact stripClosureEmbedding_root_mem n
  | true =>
    have hr : stripClosureEmbedding (pairedRoot (true, n)) *
        stripClosureEmbedding (pairedRoot (true, n)) =
        algebraMap StripField StripClosure (algebraMap K StripField (pairedRadicand (true, n))) := by
      rw [← map_mul, pairedRoot_sq, AlgHom.commutes,
        IsScalarTower.algebraMap_apply K StripField StripClosure]
    apply (root_mem_iff_isSquare hr stripQuadraticField).mpr
    change IsSquare (algebraMap StripField stripQuadraticField
      (algebraMap K StripField (xiElement * reflectedElement (n + 2))))
    rw [map_mul, map_mul]
    exact stripQuadratic_xi_isSquare.mul ((strip_reflected_factor_isSquare
      (n := n + 2) (by omega)).map (algebraMap StripField stripQuadraticField))

private theorem pairedField_le_strip_preimage :
    pairedMarkedField ≤ (stripQuadraticField.restrictScalars K).comap stripClosureEmbedding := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro x ⟨j, rfl⟩
  exact stripClosureEmbedding_pairedRoot_mem j

def stripPairedEmbedding : pairedMarkedField →ₐ[K] stripQuadraticField where
  toFun a := ⟨stripClosureEmbedding (a : Ω), pairedField_le_strip_preimage a.property⟩
  map_one' := Subtype.ext stripClosureEmbedding.map_one
  map_zero' := Subtype.ext stripClosureEmbedding.map_zero
  map_add' a b := Subtype.ext (stripClosureEmbedding.map_add (a : Ω) (b : Ω))
  map_mul' a b := Subtype.ext (stripClosureEmbedding.map_mul (a : Ω) (b : Ω))
  commutes' a := Subtype.ext (stripClosureEmbedding.commutes a)

def pairedMarkedRoot (j : Bool × ℕ) : pairedMarkedField :=
  ⟨pairedRoot j, IntermediateField.subset_adjoin K _ ⟨j, rfl⟩⟩

theorem pairedMarkedRoot_sq (j : Bool × ℕ) :
    pairedMarkedRoot j * pairedMarkedRoot j = algebraMap K pairedMarkedField (pairedRadicand j) :=
  Subtype.ext (pairedRoot_sq j)

theorem stripPairedEmbedding_reflect_root (j : Bool × ℕ) :
    stripQuadraticReflection (stripPairedEmbedding (pairedMarkedRoot j)) =
      stripPairedEmbedding (pairedMarkedRoot (!j.1, j.2)) ∨
    stripQuadraticReflection (stripPairedEmbedding (pairedMarkedRoot j)) =
      -stripPairedEmbedding (pairedMarkedRoot (!j.1, j.2)) := by
  apply mul_self_eq_mul_self_iff.mp
  rw [← map_mul, ← map_mul, pairedMarkedRoot_sq, AlgHom.commutes,
    stripQuadraticReflection_global_base, pairedRadicand_reflect,
    ← map_mul, pairedMarkedRoot_sq, AlgHom.commutes]

private theorem stripPairedEmbedding_reflection_stable (x : pairedMarkedField) :
    ∃ y : pairedMarkedField, stripPairedEmbedding y =
      stripQuadraticReflection (stripPairedEmbedding x) := by
  change stripQuadraticReflection (stripPairedEmbedding x) ∈ stripPairedEmbedding.fieldRange
  let S : Subfield pairedMarkedField := stripPairedEmbedding.fieldRange.toSubfield.comap
    (stripQuadraticReflection.toRingHom.comp stripPairedEmbedding.toRingHom)
  let T : Subfield Ω := S.map pairedMarkedField.toSubfield.subtype
  have hT : pairedMarkedField.toSubfield ≤ T := by
    change Subfield.closure (Set.range (algebraMap K Ω) ∪ Set.range pairedRoot) ≤ T
    apply Subfield.closure_le.mpr
    rintro a (⟨b, rfl⟩ | ⟨j, rfl⟩)
    · refine ⟨algebraMap K pairedMarkedField b, ?_, rfl⟩
      change stripQuadraticReflection (stripPairedEmbedding
        (algebraMap K pairedMarkedField b)) ∈ stripPairedEmbedding.fieldRange
      rw [AlgHom.commutes, stripQuadraticReflection_global_base]
      exact stripPairedEmbedding.fieldRange.algebraMap_mem _
    · refine ⟨pairedMarkedRoot j, ?_, rfl⟩
      change stripQuadraticReflection (stripPairedEmbedding (pairedMarkedRoot j)) ∈
        stripPairedEmbedding.fieldRange
      rcases stripPairedEmbedding_reflect_root j with he | he
      · rw [he]
        exact ⟨pairedMarkedRoot (!j.1, j.2), rfl⟩
      · rw [he]
        exact stripPairedEmbedding.fieldRange.neg_mem ⟨pairedMarkedRoot (!j.1, j.2), rfl⟩
  obtain ⟨y, hy, hyx⟩ := hT x.property
  have he : y = x := Subtype.ext hyx
  change stripQuadraticReflection (stripPairedEmbedding y) ∈ stripPairedEmbedding.fieldRange at hy
  exact he ▸ hy

/-- An involutive functional reflection on the actual paired global completion. -/
def pairedReflection : pairedMarkedField ≃+* pairedMarkedField :=
  ringEquivOfInvariantEmbedding stripPairedEmbedding.toRingHom stripQuadraticReflection
    stripPairedEmbedding_reflection_stable stripQuadraticReflection_involutive

theorem pairedReflection_embedding (x : pairedMarkedField) :
    stripPairedEmbedding (pairedReflection x) =
      stripQuadraticReflection (stripPairedEmbedding x) :=
  ringEquivOfInvariantEmbedding_map stripPairedEmbedding.toRingHom stripQuadraticReflection
    stripPairedEmbedding_reflection_stable stripQuadraticReflection_involutive x

theorem pairedReflection_involutive : Function.Involutive pairedReflection :=
  ringEquivOfInvariantEmbedding_involutive stripPairedEmbedding.toRingHom stripQuadraticReflection
    stripPairedEmbedding_reflection_stable stripQuadraticReflection_involutive

theorem pairedReflection_base (a : K) :
    pairedReflection (algebraMap K pairedMarkedField a) =
      algebraMap K pairedMarkedField (planeReflectEquiv 1 a) := by
  apply stripPairedEmbedding.injective
  change stripPairedEmbedding (pairedReflection (algebraMap K pairedMarkedField a)) =
    stripPairedEmbedding (algebraMap K pairedMarkedField (planeReflectEquiv 1 a))
  rw [pairedReflection_embedding, AlgHom.commutes,
    stripQuadraticReflection_global_base, AlgHom.commutes]

theorem pairedReflection_root (j : Bool × ℕ) :
    pairedReflection (pairedMarkedRoot j) = pairedMarkedRoot (!j.1, j.2) ∨
      pairedReflection (pairedMarkedRoot j) = -pairedMarkedRoot (!j.1, j.2) := by
  rcases stripPairedEmbedding_reflect_root j with h | h
  · exact Or.inl (stripPairedEmbedding.injective ((pairedReflection_embedding _).trans h))
  · exact Or.inr (stripPairedEmbedding.injective
      ((pairedReflection_embedding _).trans (h.trans (map_neg _ _).symm)))

/-- Normalize reflected signs using the involution itself; original roots stay fixed as choices. -/
def normalizedReflectedRoot (n : ℕ) : pairedMarkedField :=
  pairedReflection (pairedMarkedRoot (false, n))

theorem normalizedReflectedRoot_sq (n : ℕ) :
    normalizedReflectedRoot n * normalizedReflectedRoot n =
      algebraMap K pairedMarkedField (pairedRadicand (true, n)) := by
  rw [normalizedReflectedRoot, ← map_mul, pairedMarkedRoot_sq,
    pairedReflection_base, pairedRadicand_reflect]
  rfl

theorem pairedReflection_normalizedReflectedRoot (n : ℕ) :
    pairedReflection (normalizedReflectedRoot n) = pairedMarkedRoot (false, n) :=
  pairedReflection_involutive _

theorem normalizedReflectedRoot_eq_or_neg (n : ℕ) :
    normalizedReflectedRoot n = pairedMarkedRoot (true, n) ∨
      normalizedReflectedRoot n = -pairedMarkedRoot (true, n) := pairedReflection_root (false, n)

def stripPairedCompositum : IntermediateField StripField StripClosure :=
  IntermediateField.adjoin StripField
    (Set.range fun a : pairedMarkedField => stripClosureEmbedding (a : Ω))

/-- Adding the global reflected family does not enlarge the analytic strip compositum. -/
theorem stripPairedCompositum_eq : stripPairedCompositum = stripQuadraticField := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨a, rfl⟩
    exact pairedField_le_strip_preimage a.property
  · rw [← stripMarkedCompositum_eq]
    apply IntermediateField.adjoin.mono StripField _ _
    rintro x ⟨a, rfl⟩
    exact ⟨⟨(a : Ω), markedExtension_le_paired a.property⟩, rfl⟩

theorem stripPairedCompositum_finrank : Module.finrank StripField stripPairedCompositum = 2 := by
  rw [stripPairedCompositum_eq]
  exact stripQuadraticField_finrank

end RHTower.XiGlobalKummer
