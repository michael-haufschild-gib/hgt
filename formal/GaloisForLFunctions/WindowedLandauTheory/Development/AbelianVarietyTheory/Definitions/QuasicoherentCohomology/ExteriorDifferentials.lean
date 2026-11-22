import GaloisForLFunctions.HTGeometry.KaehlerAlgHomGenericVanishing
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExteriorBaseChange

/-! Functoriality of exterior powers of relative Kähler differentials. -/

noncomputable section

namespace GlobalTheory.SchemeCohomology

open GaloisForLFunctions.HTGeometry

variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- Relative differential forms of degree `n` on a section ring. -/
abbrev ExteriorDifferentials (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] (n : ℕ) :=
  ⋀[A]^n Ω[A⁄k]

namespace ExteriorDifferentials

private def mapLinear (f : A →ₐ[k] B) (n : ℕ) :
    letI : Module A (ExteriorDifferentials k B n) := Module.compHom _ f.toRingHom
    ExteriorDifferentials k A n →ₗ[A] ExteriorDifferentials k B n := by
  letI : Algebra A B := algHomTargetAlgebra f
  letI : Module A Ω[B⁄k] := Module.compHom _ f.toRingHom
  letI : Module A (ExteriorDifferentials k B n) := Module.compHom _ f.toRingHom
  letI : IsScalarTower A B Ω[B⁄k] := IsScalarTower.of_compHom A B Ω[B⁄k]
  let df : Ω[A⁄k] →ₗ[A] Ω[B⁄k] :=
    { algHomKaehlerMap f with
      map_smul' := algHomKaehlerMap_smul f }
  exact exteriorMapOver n df

/-- Pullback on forms applies the Kähler differential map to every factor. -/
def map (f : A →ₐ[k] B) (n : ℕ) :
    ExteriorDifferentials k A n →ₛₗ[f.toRingHom] ExteriorDifferentials k B n := by
  letI : Module A (ExteriorDifferentials k B n) := Module.compHom _ f.toRingHom
  let F := mapLinear f n
  exact { toFun := F, map_add' := F.map_add, map_smul' := F.map_smul }

@[simp] theorem map_ιMulti (f : A →ₐ[k] B) (n : ℕ) (v : Fin n → Ω[A⁄k]) :
    map f n (exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (fun i => algHomKaehlerMap f (v i)) := by
  letI : Module A (ExteriorDifferentials k B n) := Module.compHom _ f.toRingHom
  change mapLinear f n (exteriorPower.ιMulti A n v) = _
  simp only [mapLinear, exteriorMapOver_ιMulti, LinearMap.coe_mk, LinearMap.coe_toAddHom]

private theorem ext_on_wedges {f : A →ₐ[k] B} {n : ℕ}
    {F G : ExteriorDifferentials k A n →ₛₗ[f.toRingHom] ExteriorDifferentials k B n}
    (h : ∀ v, F (exteriorPower.ιMulti A n v) = G (exteriorPower.ιMulti A n v))
    (x : ExteriorDifferentials k A n) : F x = G x := by
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n (M := Ω[A⁄k]))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  refine Submodule.span_induction (fun _ ⟨v, hv⟩ => hv ▸ h v) (by simp) ?_ ?_ hx
  · intro a b _ _ ha hb
    simp only [map_add, ha, hb]
  · intro a w _ hw
    simp only [map_smulₛₗ, hw]

@[simp] theorem map_comp (g : B →ₐ[k] C) (f : A →ₐ[k] B) (n : ℕ)
    (x : ExteriorDifferentials k A n) :
    map (g.comp f) n x = map g n (map f n x) := by
  change map (g.comp f) n x = ((map g n).comp (map f n)) x
  apply ext_on_wedges
  intro v
  simp only [LinearMap.comp_apply, map_ιMulti, algHomKaehlerMap_comp]

private theorem kaehlerMap_id (x : Ω[A⁄k]) : algHomKaehlerMap (AlgHom.id k A) x = x := by
  have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Submodule.mem_top
  refine Submodule.span_induction ?_ (by simp) ?_ ?_ hx
  · rintro _ ⟨a, rfl⟩
    exact algHomKaehlerMap_D _ _
  · intro a b _ _ ha hb
    simp only [map_add, ha, hb]
  · intro a w _ hw
    rw [algHomKaehlerMap_smul, hw]
    rfl

@[simp] theorem map_id (n : ℕ) (x : ExteriorDifferentials k A n) :
    map (AlgHom.id k A) n x = x := by
  change map (AlgHom.id k A) n x =
    (LinearMap.id : ExteriorDifferentials k A n →ₗ[A] ExteriorDifferentials k A n) x
  apply ext_on_wedges
  intro v
  change map (AlgHom.id k A) n (exteriorPower.ιMulti A n v) = exteriorPower.ιMulti A n v
  simp only [map_ιMulti, kaehlerMap_id]

end ExteriorDifferentials

end GlobalTheory.SchemeCohomology
