import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdeleCoordinates

/-! A family of local units, integral at almost every finite place, determines an idele. -/

noncomputable section

open NumberField IsDedekindDomain Filter
open scoped RestrictedProduct

namespace GlobalTheory.Reciprocity.IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- Finite local units integral outside a finite set of places. -/
abbrev FiniteLocalUnitFamily :=
  Πʳ v : HeightOneSpectrum (𝓞 K),
    [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]

/-- An idele with the given finite and infinite components. -/
def ofLocalUnits (f : FiniteLocalUnitFamily K)
    (g : ∀ w : InfinitePlace K, (w.Completion)ˣ) : IdeleGroup K where
  val := (fun w => (g w).val, ⟨fun v => (f v).val,
    f.2.mono fun _ hv => ((Submonoid.mem_units_iff _ _).mp hv).1⟩)
  inv := (fun w => (g w).inv, ⟨fun v => (f v).inv,
    f.2.mono fun _ hv => ((Submonoid.mem_units_iff _ _).mp hv).2⟩)
  val_inv := Prod.ext (funext fun w => (g w).val_inv) (Subtype.ext (funext fun v => (f v).val_inv))
  inv_val := Prod.ext (funext fun w => (g w).inv_val) (Subtype.ext (funext fun v => (f v).inv_val))

@[simp] theorem finiteProj_ofLocalUnits (f : FiniteLocalUnitFamily K)
    (g : ∀ w : InfinitePlace K, (w.Completion)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finiteProj v (ofLocalUnits f g) = f v := Units.ext rfl

@[simp] theorem infiniteProj_ofLocalUnits (f : FiniteLocalUnitFamily K)
    (g : ∀ w : InfinitePlace K, (w.Completion)ˣ) (w : InfinitePlace K) :
    infiniteProj w (ofLocalUnits f g) = g w := Units.ext rfl

theorem ext_of_localUnits {x y : IdeleGroup K}
    (hf : ∀ v, finiteProj v x = finiteProj v y) (hg : ∀ w, infiniteProj w x = infiniteProj w y) :
    x = y := by
  apply Units.ext
  refine Prod.ext (funext fun w => congrArg Units.val (hg w)) (Subtype.ext ?_)
  exact funext fun v => congrArg Units.val (hf v)

theorem eventually_finiteProj_integralUnits (x : IdeleGroup K) :
    ∀ᶠ v in cofinite, finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  refine ((x : AdeleRing (𝓞 K) K).2.2.and
    ((x⁻¹ : IdeleGroup K) : AdeleRing (𝓞 K) K).2.2).mono fun v hv => ?_
  rw [Submonoid.mem_units_iff, ← map_inv, coe_finiteProj, coe_finiteProj]
  exact hv

end GlobalTheory.Reciprocity.IdeleGroup
