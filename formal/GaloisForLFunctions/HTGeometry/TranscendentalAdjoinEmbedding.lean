import GaloisForLFunctions.HTGeometry.TranscendentalMobius

/-!
# Embedding a simple transcendental field with prescribed generator

A transcendental singleton adjoin is a rational function field.  Consequently any second
transcendental element over the same base determines a unique field embedding sending the source
generator to that element.  This is the free terminal-state step in the actual cascade tower.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A prescribed transcendental target extends the base algebra map to the corresponding simple
transcendental field. -/
theorem exists_adjoinSimple_algHom_of_transcendental
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] (x : L) (hx : Transcendental K x)
    (y : M) (hy : Transcendental K y) :
    ∃ e : (IntermediateField.adjoin K {x}) →ₐ[K] M,
      e (IntermediateField.AdjoinSimple.gen K x) = y := by
  let ex : RatFunc K ≃ₐ[K] IntermediateField.adjoin K {x} :=
    RatFunc.algEquivOfTranscendental x hx
  let ey : RatFunc K ≃ₐ[K] IntermediateField.adjoin K {y} :=
    RatFunc.algEquivOfTranscendental y hy
  let inc : IntermediateField.adjoin K {y} →ₐ[K] M :=
    (IntermediateField.adjoin K {y}).val
  let e : (IntermediateField.adjoin K {x}) →ₐ[K] M :=
    inc.comp (ey.toAlgHom.comp ex.symm.toAlgHom)
  refine ⟨e, ?_⟩
  change inc (ey (ex.symm (IntermediateField.AdjoinSimple.gen K x))) = y
  have hxgen : ex RatFunc.X = IntermediateField.AdjoinSimple.gen K x := by
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X x hx
  have hygen : ey RatFunc.X = IntermediateField.AdjoinSimple.gen K y := by
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X y hy
  rw [← hxgen, ex.symm_apply_apply, hygen]
  rfl

end


end GaloisForLFunctions.HTGeometry
