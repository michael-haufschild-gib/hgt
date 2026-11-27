import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MumfordBundleSupport
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MumfordCokernelAtOrigin
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LocalPerfectCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.SmoothRationalLocalDimension
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.CechRestrictScalars
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-! On an affine neighborhood of the identity, the universal translation
difference has one-dimensional cohomology in the relative dimension. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open HTGeometry GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology
open scoped CategoryTheory.Obj

namespace GlobalTheory.MumfordFibre

attribute [local instance] Over.cartesianMonoidalCategory

/-- The regular local calculation applies to an affine chart containing
the identity. A cover of length one more than the relative dimension gives
the required upper bound on the degrees of its Čech terms. -/
theorem finrank_cech_on_origin_chart {K R : Type} [Field K] [IsAlgClosed K]
    [CommRing R] [Algebra K R] {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    (t : Spec (.of R) ⟶ A.left) [IsOpenImmersion t]
    (ht : t ≫ A.hom = Spec.map (CommRingCat.ofHom (algebraMap K R)))
    (χ : R →ₐ[K] K) (hχ : Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ t = η[A].left)
    {Y : Scheme.{0}} {π : Y ⟶ (A ⊗ A).left} {f : Y ⟶ Spec (.of R)}
    (H : IsPullback π f (fst A A).left t) (U : Fin (d + 1) → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (cU : ⨆ i, U i = ⊤) (n : ℕ) :
    let M := (translDiff A L (𝟙 A)).pull π
    let C := cech (f ≫ Spec.map (CommRingCat.ofHom (algebraMap K R))) (toMod M) U
    Module.Finite K (C.homology n) ∧ Module.finrank K (C.homology n) = if n = d then 1 else 0 := by
  let M := translDiff A L (𝟙 A)
  let F := toMod (M.pull π)
  let C := cech f F U
  letI : SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap K R))) := by
    rw [← ht]
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + d) (t ≫ A.hom))
  letI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K R))) :=
    SmoothOfRelativeDimension.smooth d _
  letI : Algebra.Smooth K R := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap K R))).mp inferInstance)
  have hM : M.IsLB := hL.linComb _ _
  obtain ⟨hR, hflat, hfin, hs⟩ := cohomology_finite_and_vanishes_off_origin hA hL hAmp hK t H U hU cU
  letI : IsNoetherianRing R := hR
  have hsupp (ψ : R →ₐ[K] K) (hψ : ψ ≠ χ) (m : ℕ) :
      ∃ r, ψ r ≠ 0 ∧ ∀ z : C.homology m, r • z = 0 := by
    apply hs ψ.toRingHom _ _ m
    · rw [Category.assoc, ht, ← Spec.map_comp, ← Spec.map_id]
      exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext ψ.commutes))
    · intro he
      apply hψ
      have hh := Spec.map_injective ((cancel_mono t).mp (he.trans hχ.symm))
      exact AlgHom.ext fun z => congrArg (fun u : CommRingCat.of R ⟶ CommRingCat.of K => u z) hh
  let p := RingHom.ker χ.toRingHom
  letI : p.IsPrime := RingHom.ker_isPrime χ.toRingHom
  letI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ.toRingHom
  let O := Localization.AtPrime p
  letI : IsLocalization.AtPrime O (RingHom.ker χ) :=
    inferInstanceAs (IsLocalization.AtPrime (Localization.AtPrime p) p)
  obtain ⟨reg, dim⟩ := regular_local_dimension_of_rational_point d χ
  letI : IsRegularLocalRing O := reg
  obtain ⟨ρ, hρ⟩ := PointSupport.exists_residueEquiv_at_rational_point (O := O) χ
  let α := algebraMap R O
  let j := Spec.map (CommRingCat.ofHom α)
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
  let i := Spec.map (CommRingCat.ofHom ρ.symm.toRingHom)
  letI : IsIso i := inferInstanceAs (IsIso (Spec.map (ρ.symm.toCommRingCatIso.hom)))
  letI : IsPreimmersion j := IsPreimmersion.of_isLocalization p.primeCompl
  letI : Mono (j ≫ t) := inferInstance
  have hc : r ≫ (j ≫ t) = i ≫ η[A].left := by
    rw [← hχ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply congrArg Spec.map
    ext z
    exact (ρ.symm_apply_eq.mpr (hρ z).symm).symm
  let a := pullback.fst f j
  let b := pullback.snd f j
  have J : IsPullback a b f j := IsPullback.of_hasPullback f j
  have J' : IsPullback (a ≫ π) b (fst A A).left (j ≫ t) := J.paste_horiz H
  let V (k : Fin (d + 1)) := a ⁻¹ᵁ U k
  have Hprod : IsPullback (snd A A).left (fst A A).left A.hom A.hom :=
    (IsPullback.of_hasPullback A.hom A.hom).flip
  have Hbase : IsPullback (π ≫ (snd A A).left) f A.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K R))) := ht ▸ H.paste_horiz Hprod
  letI : Y.IsSeparated := (ProjectiveSections.isProjOver_baseChange (algebraMap K R) Hbase
    (ProjectiveSections.isProjOver_of_relAmple hL hAmp)).isSeparated
  have hI := affine_coverInter_of_affine U hU
  have cV : ⨆ k, V k = ⊤ := a.iSup_preimage_eq_top cU
  letI : IsAffineHom a := MorphismProperty.of_isPullback J.flip inferInstance
  have hV (s : Finset (Fin (d + 1))) (hs : s.Nonempty) : IsAffineOpen (coverInter ⊤ V s) :=
    (coverInter_pull (π := a) U s).symm ▸ (hI s hs).preimage a
  let D := cech b (toMod (M.pull (a ≫ π))) V
  obtain ⟨w, hw⟩ := exists_iso_pull_comp hM π a
  let e := cechBaseChangeIso (M.pull π) U (hM.pull π) α J hI ≪≫
    cechIsoOfIsGen b V ((hM.pull π).pull a) (hM.pull (a ≫ π)) hw
  have hzero (m : ℕ) (hm : d < m) : IsZero (C.X m) :=
    cech_isZero f F U m (by rw [Fintype.card_fin]; exact hm)
  obtain ⟨hF, hdim⟩ := FiniteLengthComplex.finrank_homology_of_local_dual_cokernel (O := O) χ d dim C
    hzero hflat hfin hsupp D e
    (fun P q hf hq => dual_cokernel_equiv_residue_at_origin hA hL hK (j ≫ t) i hc
      J' V cV hV P q hf hq) n
  letI := hF
  let u := homologyCechRestrictScalarsEquiv (algebraMap K R) f F U n
  exact ⟨Module.Finite.equiv u.symm, u.finrank_eq.trans hdim⟩

end GlobalTheory.MumfordFibre
