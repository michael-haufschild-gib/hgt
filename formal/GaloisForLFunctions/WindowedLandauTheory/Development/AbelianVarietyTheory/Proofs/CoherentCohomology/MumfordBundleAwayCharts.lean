import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MumfordBundleSupport
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.CechRestrictScalars
import GaloisForLFunctions.HTGeometry.PointsSeparate

/-! The Čech complex on an affine base chart disjoint from the identity
is acyclic, also when viewed over the ground field. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.LineBundleSections
open scoped CategoryTheory.Obj

namespace GlobalTheory.MumfordFibre

attribute [local instance] Over.cartesianMonoidalCategory

/-- On a chart away from the identity, every maximal ideal is a rational
point where the homology vanishes. This forces its annihilator to be the unit ideal. -/
theorem cech_acyclic_away_chart {K R : Type} [Field K] [IsAlgClosed K]
    [CommRing R] [Algebra K R] {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (t : Spec (.of R) ⟶ A.left) [IsOpenImmersion t]
    (ht : t ≫ A.hom = Spec.map (CommRingCat.ofHom (algebraMap K R)))
    (haway : ∀ p : Spec (.of R), t p ≠ η[A].left (IsLocalRing.closedPoint K))
    {Y : Scheme.{0}} {π : Y ⟶ (A ⊗ A).left} {f : Y ⟶ Spec (.of R)}
    (H : IsPullback π f (fst A A).left t) {κ : Type} [LinearOrder κ] [Fintype κ]
    (U : κ → Y.Opens) (hU : ∀ i, IsAffineOpen (U i)) (cU : ⨆ i, U i = ⊤) :
    (cech (f ≫ Spec.map (CommRingCat.ofHom (algebraMap K R)))
      (toMod ((translDiff A L (𝟙 A)).pull π)) U).Acyclic := by
  let F := toMod ((translDiff A L (𝟙 A)).pull π)
  let C := cech f F U
  obtain ⟨_, _, _, hs⟩ := cohomology_finite_and_vanishes_off_origin hA hL hAmp hK t H U hU cU
  letI : Smooth A.hom := hA.smooth
  letI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K R))) :=
    ht ▸ (inferInstance : LocallyOfFiniteType (t ≫ A.hom))
  letI : Algebra.FiniteType K R := RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap K R))).mp inferInstance)
  intro n
  have han : Module.annihilator R (C.homology n) = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    letI := hm
    obtain ⟨χ, hχ⟩ := GaloisForLFunctions.HTGeometry.exists_algHom_ker_eq_of_isMaximal (C := K) m
    have hbase : (Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ t) ≫ A.hom = 𝟙 _ := by
      rw [Category.assoc, ht, ← Spec.map_comp, ← Spec.map_id]
      exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext χ.commutes))
    have hn : Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ t ≠ η[A].left := fun e =>
      haway _ (congrArg (fun g : Spec (.of K) ⟶ A.left => g (IsLocalRing.closedPoint K)) e)
    obtain ⟨r, hr, hz⟩ := hs χ.toRingHom hbase hn n
    exact hr ((hχ r).mpr (hle (Module.mem_annihilator.mpr hz)))
  letI : Subsingleton (C.homology n) := by
    have e := Module.mem_annihilator.mp ((Ideal.eq_top_iff_one _).mp han)
    exact subsingleton_of_forall_eq 0 fun x => (one_smul R x).symm.trans (e x)
  letI : Subsingleton ((ModuleCat.restrictScalars (algebraMap K R)).obj (C.homology n)) :=
    inferInstanceAs (Subsingleton (C.homology n))
  let u := homologyCechRestrictScalarsEquiv (algebraMap K R) f F U n
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (ModuleCat.isZero_iff_subsingleton.mpr u.toEquiv.subsingleton)

end GlobalTheory.MumfordFibre
