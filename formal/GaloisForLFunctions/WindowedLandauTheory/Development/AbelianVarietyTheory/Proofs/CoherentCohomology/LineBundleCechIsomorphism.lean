import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechMaps
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FlatLineBundleCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionIsomorphism
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ZeroTwistSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundleTrivialization

/-! Natural isomorphisms of line-bundle sections induce isomorphisms of
the Čech complexes over the base ring. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {M N : LB X} {R : Type} [CommRing R]
  (f : X ⟶ Spec (.of R)) {ι : Type} [LinearOrder ι] (U : ι → X.Opens)

private def cechIsoOfSections
    (e : ∀ V : X.Opens, Γ(toMod M, V) ≃ₗ[Γ(X, V)] Γ(toMod N, V))
    (he : ∀ {V W : X.Opens} (h : W ≤ V) (x : Γ(toMod M, V)),
      e W ((toMod M).presheaf.map (homOfLE h).op x) =
        (toMod N).presheaf.map (homOfLE h).op (e V x)) :
    cech f (toMod M) U ≅ cech f (toMod N) U := by
  letI (s : Finset ι) := sectionDatumModule f (toMod M) U s
  letI (s : Finset ι) := sectionDatumModule f (toMod N) U s
  let φ : (sectionDatum (toMod M) U).Hom (sectionDatum (toMod N) U) :=
    { app := fun s => (e (coverInter ⊤ U s)).toAddEquiv.toAddMonoidHom
      comm := fun h x => (he (coverInter_anti h) x).symm }
  have hφ (s : Finset ι) (r : R) (x : (sectionDatum (toMod M) U).obj s) :
      φ.app s (r • x) = r • φ.app s x := by
    let V := coverInter ⊤ U s
    letI := sectionAlgebra f V
    exact (e V).map_smul (algebraMap R Γ(X, V) r) (show Γ(toMod M, V) from x)
  let a : cech f (toMod M) U ⟶ cech f (toMod N) U :=
    FinsetCechDatum.linearCochainMap (res_base_smul f (toMod M) U)
      (res_base_smul f (toMod N) U) φ hφ
  letI : IsIso a := FinsetCechDatum.isIso_linearCochainMap _ _ φ hφ fun s _ =>
    (e (coverInter ⊤ U s)).bijective
  exact asIso a

/-- An isomorphism of line bundles acts invertibly on the affine Čech complex. -/
def cechIsoOfIsGen (hM : M.IsLB) (hN : N.IsLB) {w : LB.Iso M N} (hw : w.IsGen) :
    cech f (toMod M) U ≅ cech f (toMod N) U :=
  cechIsoOfSections f U (fun _ => sectionIsoEquiv hM hN hw)
    (sectionIsoEquiv_restrict hM hN hw)

private theorem twist_pull_trivial {Y : Scheme.{0}} (M : LB X) (q : X ⟶ Y) :
    twist M ((LB.trivial Y).pull q) 1 = twist M ((LB.trivial Y).pull q) 0 := by
  have hg (i j : ((LB.trivial Y).pull q).ι) : ((LB.trivial Y).pull q).g i j = 1 := by
    change (∏ k : PUnit, res _ (pullU q _ (1 : Γ(Y, (LB.trivial Y).U (i k) ⊓ (LB.trivial Y).U (j k))ˣ)) ^ (1 : ℤ)) = 1
    simp only [map_one, one_zpow, Finset.prod_const_one]
  simp only [twist, transitionPower, hg, one_zpow]

/-- The exterior product with a trivial second factor has the Čech complex
of the first pullback. -/
def cechIsoPullTrivial {Y : Scheme.{0}} (q : X ⟶ Y) (hM : M.IsLB) :
    cech f (toMod M) U ≅ cech f (toMod (twist M ((LB.trivial Y).pull q) 1)) U := by
  rw [twist_pull_trivial M q]
  let hO := (LB.isLB_trivial Y).pull q
  exact cechIsoOfSections f U (fun _ => zeroTwistEquiv hM hO) (zeroTwistEquiv_restrict hM hO)

end GlobalTheory.LineBundleSections
