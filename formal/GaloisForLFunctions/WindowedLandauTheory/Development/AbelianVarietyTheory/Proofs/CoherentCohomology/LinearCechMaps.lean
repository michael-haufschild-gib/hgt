import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CechCoefficientDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Maps of Čech data induce scalar-linear cochain maps. -/

noncomputable section

open CategoryTheory HTGeometry
open GlobalTheory.SchemeCohomology

namespace HTGeometry.FinsetCechDatum

variable {R ι : Type} [CommRing R] [DecidableEq ι] [LinearOrder ι]
  {D E : FinsetCechDatum ι} [∀ s, Module R (D.obj s)] [∀ s, Module R (E.obj s)]
  (hD : ∀ {s t : Finset ι} (h : s ⊆ t) (r : R) (x : D.obj s), D.res h (r • x) = r • D.res h x)
  (hE : ∀ {s t : Finset ι} (h : s ⊆ t) (r : R) (x : E.obj s), E.res h (r • x) = r • E.res h x)
  (φ : D.Hom E) (hφ : ∀ s (r : R) (x : D.obj s), φ.app s (r • x) = r • φ.app s x)

private def degreeLinearMap (n : ℕ) : D.degreeSubmodule (R := R) n →ₗ[R] E.degreeSubmodule (R := R) n where
  toFun x := ⟨φ.onCochain x.1, φ.onCochain_isDeg x.2⟩
  map_add' x y := Subtype.ext (funext fun s => map_add (φ.app s) (x.1 s) (y.1 s))
  map_smul' r x := Subtype.ext (funext fun s => hφ s r (x.1 s))

def linearCochainMap : D.linearComplex hD ⟶ E.linearComplex hE :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (degreeLinearMap φ hφ n)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [linearComplex, CochainComplex.of_d]
    exact Subtype.ext (φ.d_onCochain x.1))

theorem isIso_linearCochainMap (h : ∀ s : Finset ι, s.Nonempty → Function.Bijective (φ.app s)) :
    IsIso (linearCochainMap hD hE φ hφ) := by
  haveI (n : ℕ) : IsIso ((linearCochainMap hD hE φ hφ).f n) := by
    have hb : Function.Bijective (degreeLinearMap φ hφ n) := cochainMap_bijective_of_nonempty φ h n
    let e := LinearEquiv.ofBijective (degreeLinearMap φ hφ n) hb
    change IsIso e.toModuleIso.hom
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

variable {Q : FinsetCechDatum ι} [∀ s, Module R (Q.obj s)]
  (hQ : ∀ {s t : Finset ι} (h : s ⊆ t) (r : R) (x : Q.obj s), Q.res h (r • x) = r • Q.res h x)
  (ψ : E.Hom Q) (hψ : ∀ s (r : R) (x : E.obj s), ψ.app s (r • x) = r • ψ.app s x)

/-- Short exactness of the section maps implies short exactness of the linear Čech complexes. -/
theorem shortExact_linearCochainMap
    (hcomp : ∀ s (x : D.obj s), ψ.app s (φ.app s x) = 0)
    (hinj : ∀ s, s.Nonempty → Function.Injective (φ.app s))
    (hex : ∀ s, s.Nonempty → Function.Exact (φ.app s) (ψ.app s))
    (hsurj : ∀ s, s.Nonempty → Function.Surjective (ψ.app s)) :
    (ShortComplex.mk (linearCochainMap hD hE φ hφ) (linearCochainMap hE hQ ψ hψ) (by
      ext n x
      exact Subtype.ext (funext fun s => hcomp s (x.1 s)))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have h := (HomologicalComplex.shortExact_iff_degreewise_shortExact.1
    (shortExact_cochainMap φ ψ hcomp hinj hex hsurj)) n
  exact ModuleCat.shortComplex_shortExact _
    ((ShortComplex.ab_exact_iff_function_exact _).1 h.exact)
    ((AddCommGrpCat.mono_iff_injective _).1 h.mono_f)
    ((AddCommGrpCat.epi_iff_surjective _).1 h.epi_g)

end HTGeometry.FinsetCechDatum
