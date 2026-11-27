import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectSectionCyclicQuotient
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.MumfordBundleTriviality

/-! At the identity of a principal polarization, the first dual cokernel
of a perfect section model is the residue field. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open HTGeometry GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology
open scoped CategoryTheory.Obj

namespace GlobalTheory.MumfordFibre

attribute [local instance] Over.cartesianMonoidalCategory

/-- Triviality on the cyclic quotient forces the test point of the abelian
variety to be the identity, so the quotient has no infinitesimal thickening. -/
theorem dual_cokernel_equiv_residue_at_origin {K O : Type} [Field K] [CommRing O] [IsLocalRing O]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hK : KTriv A L)
    (t : Spec (.of O) ⟶ A.left) [Mono t]
    (i : Spec (.of (IsLocalRing.ResidueField O)) ⟶ Spec (.of K)) [IsIso i]
    (hi : Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ t = i ≫ η[A].left)
    {Y : Scheme.{0}} {π : Y ⟶ (A ⊗ A).left} {f : Y ⟶ Spec (.of O)}
    (H : IsPullback π f (fst A A).left t)
    {κ : Type} [LinearOrder κ] [Fintype κ] (U : κ → Y.Opens)
    (hcov : ⨆ k, U k = ⊤)
    (hU : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (coverInter ⊤ U s))
    (C : CochainComplex (ModuleCat.{0} O) ℕ)
    (φ : C ⟶ cech f (toMod ((translDiff A L (𝟙 A)).pull π)) U)
    (hfree : ∀ n, Module.Free O (C.X n) ∧ Module.Finite O (C.X n))
    (hφ : ∀ (S : Type) [CommRing S] [Algebra O S], QuasiIso
      (((ModuleCat.extendScalars (algebraMap O S)).mapHomologicalComplex (ComplexShape.up ℕ)).map φ)) :
    Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O]
      IsLocalRing.ResidueField O) := by
  let M := translDiff A L (𝟙 A)
  have hM : M.IsLB := hL.linComb _ _
  let α := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
  let a := pullback.fst f α
  let b := pullback.snd f α
  have H₀ : IsPullback a b f α := IsPullback.of_hasPullback _ _
  have Hprod : IsPullback (snd A A).left (fst A A).left A.hom A.hom :=
    (IsPullback.of_hasPullback A.hom A.hom).flip
  have Hf : IsPullback (π ≫ (snd A A).left) f A.hom (t ≫ A.hom) := H.paste_horiz Hprod
  letI : IsProper A.hom := hA.proper
  letI : IsProper f := MorphismProperty.of_isPullback Hf inferInstance
  letI : IsIso A.hom.appTop := hA.isIso_appTop
  have hi₀ : (α ≫ t) ≫ A.hom = i := by
    let e : Spec (.of K) ⟶ A.left := η[A].left
    have hbase : e ≫ A.hom = 𝟙 (Spec (.of K)) := Over.w η[A]
    calc
      _ = (i ≫ e) ≫ A.hom := congrArg (fun u => u ≫ A.hom) hi
      _ = i ≫ (e ≫ A.hom) := Category.assoc i e A.hom
      _ = i ≫ 𝟙 _ := congrArg (fun u : Spec (.of K) ⟶ Spec (.of K) => i ≫ u) hbase
      _ = i := Category.comp_id i
  let c := a ≫ π ≫ (snd A A).left
  have Hc : IsPullback c b A.hom i := by
    rw [← hi₀, Category.assoc]
    exact H₀.paste_horiz Hf
  letI : IsIso c := Hc.isIso_fst_of_isIso
  have hb : b = (c ≫ A.hom) ≫ inv i := by rw [Hc.w, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  letI : IsIso c.appTop := inferInstanceAs (IsIso (c.app ⊤))
  letI : IsIso (inv i).appTop := inferInstanceAs (IsIso ((inv i).app ⊤))
  letI : IsIso b.appTop := by rw [hb, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]; infer_instance
  have hg : ∃ s : ((M.pull π).pull a).Gen, s.IsGen := by
    have h : (a ≫ π) ≫ (fst A A).left = (b ≫ i) ≫ η[A].left := by
      rw [Category.assoc, H.w, H₀.w_assoc, hi, Category.assoc]
    obtain ⟨s, hs⟩ := exists_gen_at_identity hL (a ≫ π) (b ≫ i) h
    exact LB.exists_gen_of_pullbackSquare hM (Category.id_comp (a ≫ π)) hs
  obtain ⟨I, hI, ⟨e⟩, ⟨s, hs⟩⟩ :=
    exists_quotient_with_generator (hM.pull π) U hcov hU φ hfree hφ H₀ hg
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let j := pullback.fst f q
  let g := pullback.snd f q
  have Hq : IsPullback (j ≫ π) g (fst A A).left (q ≫ t) :=
    (IsPullback.of_hasPullback f q).paste_horiz H
  have ht : ∃ u : (M.pull (j ≫ π)).Gen, u.IsGen := by
    obtain ⟨w, hw⟩ := exists_iso_pull_comp hM π j
    exact hs.exists_gen_of_iso hw ((hM.pull π).pull j) (hM.pull (j ≫ π))
  let x : Over.mk ((q ≫ t) ≫ A.hom) ⟶ A := Over.homMk (q ≫ t) rfl
  have hx : x = 1 := eq_identity_of_exists_gen hL hK x Hq ht
  have hxt : q ≫ t = ((q ≫ t) ≫ A.hom) ≫ η[A].left := congrArg Over.Hom.left hx
  let l := ((q ≫ t) ≫ A.hom) ≫ inv i
  have hl : l ≫ α = q := (cancel_mono t).mp (by
    rw [Category.assoc, show α ≫ t = i ≫ η[A].left from hi, ← Category.assoc]
    change ((((q ≫ t) ≫ A.hom) ≫ inv i) ≫ i) ≫ η[A].left = _
    rw [Category.assoc _ (inv i) i, IsIso.inv_hom_id, Category.comp_id]
    exact hxt.symm)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective l
  have hmap : CommRingCat.ofHom (Ideal.Quotient.mk I) =
      CommRingCat.ofHom (IsLocalRing.residue O) ≫ ψ := Spec.map_injective (by
    rw [Spec.map_comp, hψ]
    exact hl.symm)
  have hmax : IsLocalRing.maximalIdeal O ≤ I := by
    intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (congrArg (fun u : CommRingCat.of O ⟶ CommRingCat.of (O ⧸ I) => u z) hmap).trans
      (by change ψ (IsLocalRing.residue O z) = 0
          rw [show IsLocalRing.residue O z = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero])
  exact ⟨e.trans (Submodule.quotEquivOfEq I _ (hI.antisymm hmax))⟩

end GlobalTheory.MumfordFibre
