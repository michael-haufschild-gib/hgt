import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELSectionValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELTensorPowerPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELPolarizations
import Mathlib.Algebra.Category.Ring.Constructions

/-! Relative ampleness pulls back over an affine open containing the base image. -/

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

private theorem isPushout_appLE_of_isPullback {X Y S T : Scheme.{0}}
    {g : Y ⟶ X} {iY : Y ⟶ T} {iX : X ⟶ S} {f : T ⟶ S} (H : IsPullback g iY iX f)
    {US : S.Opens} {UT : T.Opens} {UX : X.Opens} {UY : Y.Opens}
    (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)
    (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
    (hs : IsAffineOpen US) (hx : IsAffineOpen UX) (ht : IsAffineOpen UT) :
    IsPushout (iX.appLE US UX hUSX) (f.appLE US UT hUST)
      (g.appLE UX UY (by rw [hUY]; exact inf_le_left))
      (iY.appLE UT UY (by rw [hUY]; exact inf_le_right)) := by
  letI : IsAffine US := hs
  letI : IsAffine UX := hx
  letI : IsAffine UT := ht
  have h := Scheme.Hom.isPullback_resLE H hUST hUSX hUY
  have hp := isPushout_appTop_of_isPullback h
  refine hp.of_iso US.topIso UX.topIso UT.topIso UY.topIso ?_ ?_ ?_ ?_
  all_goals
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem eval₂Hom_surjective_of_isPushout {R R' B B' : CommRingCat}
    {g : R ⟶ B} {f : R ⟶ R'} {b : B ⟶ B'} {g' : R' ⟶ B'}
    (H : IsPushout g f b g') {ι : Type} (r : ι → B)
    (hr : Function.Surjective (MvPolynomial.eval₂Hom g.hom r)) :
    Function.Surjective (MvPolynomial.eval₂Hom g'.hom fun j => b.hom (r j)) := by
  rw [← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout H,
    Subring.closure_le]
  rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
  · obtain ⟨p, rfl⟩ := hr d
    refine ⟨MvPolynomial.map f.hom p, ?_⟩
    rw [MvPolynomial.eval₂Hom_map_hom]
    exact ((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom H.w.symm)).trans
      (MvPolynomial.map_eval₂Hom _ _ _ p).symm)
  · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

variable {Y : Scheme.{0}}

theorem mem_nonzeroLocus {M : LB Y} (s : LB.Sec M) (y : Y) :
    y ∈ nonzeroLocus s ↔ ∃ k, y ∈ M.U k ∧ IsUnit (gs (𝟙 Y) y _ (s.f k)) := by
  simp only [nonzeroLocus, TopologicalSpace.Opens.mem_iSup]
  refine exists_congr fun k => ?_
  constructor
  · intro hy
    have hk : y ∈ M.U k := Scheme.basicOpen_le _ _ hy
    refine ⟨hk, ?_⟩
    have hu := (Scheme.mem_basicOpen Y (s.f k) y hk).1 hy
    unfold gs
    rw [dif_pos (show (𝟙 Y : Y ⟶ Y) y ∈ M.U k by simpa using hk)]
    exact hu
  · rintro ⟨hk, hu⟩
    unfold gs at hu
    rw [dif_pos (show (𝟙 Y : Y ⟶ Y) y ∈ M.U k by simpa using hk)] at hu
    exact (Scheme.mem_basicOpen Y (s.f k) y hk).2 hu

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
  {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}

/-- Pull back relative ampleness when the new base maps into an affine open. -/
theorem relAmple_pull (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull φ)}
    (hw : w.IsGen) (U : S.Opens) (hU : IsAffineOpen U) (hf : ∀ y, f y ∈ U) (hA : RelAmple A L) : RelAmple A' L' := by
  intro U' hU'
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA U hU
  have le : U' ≤ f ⁻¹ᵁ U := fun y _ => hf y
  have le' : A'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y _ => (congrArg (fun q => q y ∈ U) h.w).mpr (hf _)
  let ψ := φ.resLE (A.hom ⁻¹ᵁ U) (A'.hom ⁻¹ᵁ U') le'
  have hψ : ψ ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ U').ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  have H : IsPullback ψ (A'.hom ∣_ U') (A.hom ∣_ U) (f.resLE U U' le) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict A.hom U).flip
    · rw [hψ, Scheme.Hom.resLE_comp_ι]
      exact (isPullback_morphismRestrict A'.hom U').flip.paste_horiz h
    · rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w, Category.assoc,
        Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have : IsAffine U := hU
  have : IsAffine U' := hU'
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := hL.linComb (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)
  have hP' := hL'.linComb (K := Fin N) (fun _ => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1)
  obtain ⟨W, hW⟩ := iso_linComb_pull hw
    (fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι) (fun _ => (A'.hom ⁻¹ᵁ U').ι)
    (fun _ => 1) ψ (fun _ => hψ.symm)
  choose s' hs' using fun i => sec_pull_down (pGen_of_isGen hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver A' L' U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, ← gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).trans e)).mp (u.map _))⟩
  refine ⟨N, hN, M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver A L U N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))
  · have e : nonzeroLocus (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) ⊓ (A'.hom ∣_ U') ⁻¹ᵁ ⊤ := by
      exact (loc i).trans (by rw [Scheme.Hom.preimage_top, inf_top_eq])
    have po := isPushout_appLE_of_isPullback H le_top le_top e
      (isAffineOpen_top _) haff (isAffineOpen_top _)
    exact eval₂Hom_surjective_of_isPushout po r hsurj

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
