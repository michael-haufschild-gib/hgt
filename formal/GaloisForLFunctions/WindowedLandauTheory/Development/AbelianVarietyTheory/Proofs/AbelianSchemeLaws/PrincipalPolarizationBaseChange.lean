import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.WeilTorsionCharacters
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeGeneratorRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGroupPullbacks
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELTensorPowerPullback

/-! Rigidification, symmetry, and the trivial translation kernel pass to
the pullback of a polarization. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
open GlobalTheory.LiePull
open scoped CategoryTheory.Obj

namespace GlobalTheory.PolPull

attribute [local instance] Over.cartesianMonoidalCategory

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

/-- The chosen generator at the identity pulls back to one at the new identity. -/
theorem rigid_generator_pullback (f : S' ⟶ S) (hL : L.IsLB)
    (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen) :
    ∃ t : ((L.pull (pφ f A)).pull η[(Over.pullback f).obj A].left).Gen, t.IsGen := by
  let B := (Over.pullback f).obj A
  let π := pφ f A
  obtain ⟨w, hw⟩ := (hL.pull π).gen_refl
  obtain ⟨u, hu⟩ := iso_linComb_pull hw (fun _ : PUnit => η[A].left)
    (fun _ : PUnit => η[B].left) (fun _ => 1) f (fun _ =>
      GlobalTheory.GrpTangent.one_pullback_left_fst f A)
  obtain ⟨t, ht⟩ := hrig
  obtain ⟨v, hv⟩ := (ChartPull.pull (L.pull η[A].left) f).exists_gen ht
  obtain ⟨u', hu'⟩ := hu.symm
  exact hv.exists_gen_of_iso hu' ((hL.pull η[A].left).pull f) ((hL.pull π).pull η[B].left)

/-- Inversion commutes with projection from a cartesian base change of a group scheme. -/
private theorem inv_comp_projection (f : S' ⟶ S) :
    (GrpObj.inv : (Over.pullback f).obj A ⟶ (Over.pullback f).obj A).left ≫ pφ f A =
      pφ f A ≫ (GrpObj.inv : A ⟶ A).left := by
  let B := (Over.pullback f).obj A
  let H := ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.isGrpPullback f A
  have e := congrArg Over.Hom.left (map_inv (pushHom H B) (𝟙 B))
  change ((𝟙 B : B ⟶ B)⁻¹).left ≫ pφ f A =
    ((pushHom H B (𝟙 B))⁻¹).left at e
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  exact e.trans (congrArg (fun q : B.left ⟶ A.left => q ≫ (GrpObj.inv : A ⟶ A).left)
    (Category.id_comp (pφ f A)))

/-- A system of generators comparing the bundle with its inversion pullback
restricts to the preimages of its base opens. -/
theorem symmetric_generators_pullback (f : S' ⟶ S) (hL : L.IsLB)
    (hSym : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : (LB.LinComb L (K := Fin 2)
      ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen) :
    let B := (Over.pullback f).obj A
    let L' := L.pull (pφ f A)
    ∀ s : S', ∃ V : S'.Opens, s ∈ V ∧ ∃ t : (LB.LinComb L' (K := Fin 2)
      ![(B.hom ⁻¹ᵁ V).ι ≫ (GrpObj.inv : B ⟶ B).left, (B.hom ⁻¹ᵁ V).ι] ![1, -1]).Gen, t.IsGen := by
  let B := (Over.pullback f).obj A
  let π := pφ f A
  let H : IsPullback π B.hom A.hom f := IsPullback.of_hasPullback _ _
  let L' := L.pull π
  have hL' : L'.IsLB := hL.pull π
  dsimp only
  intro s
  obtain ⟨U, hU, t, ht⟩ := hSym (f s)
  let V := f ⁻¹ᵁ U
  let W := A.hom ⁻¹ᵁ U
  let W' := B.hom ⁻¹ᵁ V
  have h : W' ≤ π ⁻¹ᵁ W := fun y hy =>
    (congrArg (fun q : B.left ⟶ S => q y ∈ U) H.w).mpr hy
  let j := π.resLE W W' h
  have hj : j ≫ W.ι = W'.ι ≫ π := Scheme.Hom.resLE_comp_ι π h
  let a : Fin 2 → (W.toScheme ⟶ A.left) := ![W.ι ≫ (GrpObj.inv : A ⟶ A).left, W.ι]
  let b : Fin 2 → (W'.toScheme ⟶ B.left) := ![W'.ι ≫ (GrpObj.inv : B ⟶ B).left, W'.ι]
  let d : Fin 2 → ℤ := ![1, -1]
  have hfac (k : Fin 2) : b k ≫ π = j ≫ a k := by
    fin_cases k
    · change (W'.ι ≫ (GrpObj.inv : B ⟶ B).left) ≫ π = j ≫ W.ι ≫ (GrpObj.inv : A ⟶ A).left
      rw [Category.assoc, inv_comp_projection, ← Category.assoc, ← hj, Category.assoc]
    · exact hj.symm
  obtain ⟨w, hw⟩ := hL'.gen_refl
  obtain ⟨u, hu⟩ := iso_linComb_pull hw a b d j hfac
  obtain ⟨v, hv⟩ := (ChartPull.pull (LB.LinComb L a d) j).exists_gen ht
  obtain ⟨u', hu'⟩ := hu.symm
  exact ⟨V, hU, hv.exists_gen_of_iso hu' ((hL.linComb a d).pull j) (hL'.linComb b d)⟩

/-- Any local trivialization of a translation difference after base change
gives one on the original group tested over the composite base morphism. -/
theorem kTriv_baseChange {A' : Over S'} [GrpObj A'] {f : S' ⟶ S}
    {π : A'.left ⟶ A.left} {L' : LB A'.left}
    (H : IsGrpPullback A' A f π) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull π)} (hw : w.IsGen) (hK : KTriv A L) : KTriv A' L' := by
  intro R _ t x hx
  let T' := Over.mk t
  let T := Over.mk (t ≫ f)
  let x₀ : T ⟶ A := pushHom H T' x
  have hx₀ : x₀.left = x.left ≫ π := rfl
  obtain ⟨e, he⟩ := exists_pushEquiv H T' (t ≫ f) rfl
  have hp : x₀ = 1 := by
    refine hK R (t ≫ f) x₀ ?_
    intro s
    obtain ⟨U, hU, c, hc⟩ := hx s
    let D := translDiff A L x₀
    let D' := translDiff A' L' x
    let W := (fst T A).left ⁻¹ᵁ U
    let W' := (fst T' A').left ⁻¹ᵁ U
    let Z := Over.mk ((fst T A).left ≫ t)
    have hs : (snd T A).left ≫ A.hom = ((fst T A).left ≫ t) ≫ f := by
      have h₁ := Over.w (fst T A)
      have h₂ := Over.w (snd T A)
      exact h₂.trans (h₁.symm.trans (Category.assoc _ _ _).symm)
    let a : Z ⟶ T' := Over.homMk (fst T A).left rfl
    let b : Z ⟶ A' := Over.homMk (H.1.lift (snd T A).left Z.hom hs) (H.1.lift_snd _ _ _)
    let l := lift a b
    have hb : b.left ≫ π = (snd T A).left := H.1.lift_fst _ _ _
    have hfst : l.left ≫ (fst T' A').left = (fst T A).left :=
      congrArg Over.Hom.left (lift_fst a b)
    have hsnd : l.left ≫ (snd T' A').left ≫ π = (snd T A).left :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q : Z ⟶ A' => q.left ≫ π) (lift_snd a b)).trans hb)
    have htr : l.left ≫ (translPt A' x).left ≫ π = (translPt A x₀).left := by
      have hl : l ≫ translPt A' x = (a ≫ x) * b := by
        change l ≫ ((fst T' A' ≫ x) * snd T' A') = _
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      let j : Over.mk (Z.hom ≫ f) ⟶ T ⊗ A :=
        Over.homMk (𝟙 _) ((Category.id_comp _).trans ((Over.w (snd T A)).symm.trans hs))
      have h := H.2 Z (a ≫ x) b (j ≫ fst T A ≫ x₀) (j ≫ snd T A)
        ((Category.id_comp _).trans (Category.assoc _ _ _).symm) ((Category.id_comp _).trans hb.symm)
      rw [← MonObj.comp_mul, ← hl] at h
      exact (Category.assoc _ _ _).symm.trans (h.symm.trans (Category.id_comp _))
    have hj : Set.range (W.ι ≫ l.left) ⊆ Set.range W'.ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q : Z.left ⟶ T.left => q y.1 ∈ U) hfst).mpr y.2
    let n := IsOpenImmersion.lift W'.ι (W.ι ≫ l.left) hj
    have hn : n ≫ W'.ι = W.ι ≫ l.left := IsOpenImmersion.lift_fac _ _ _
    let g : Fin 2 → ((T ⊗ A).left ⟶ A.left) := ![(translPt A x₀).left, (snd T A).left]
    let g' : Fin 2 → ((T' ⊗ A').left ⟶ A'.left) := ![(translPt A' x).left, (snd T' A').left]
    let d : Fin 2 → ℤ := ![1, -1]
    have hD : D.IsLB := hL.linComb g d
    have hD' : D'.IsLB := hL'.linComb g' d
    have hfac (k : Fin 2) : ((n ≫ W'.ι) ≫ g' k) ≫ π = W.ι ≫ g k := by
      calc
        _ = W.ι ≫ (l.left ≫ g' k ≫ π) := by
          rw [hn]
          simp only [Category.assoc]
        _ = _ := congrArg (W.ι ≫ ·) (by
          fin_cases k
          · exact htr
          · exact hsnd)
    obtain ⟨c₁, hc₁⟩ := (ChartPull.pull (D'.pull W'.ι) n).exists_gen hc
    obtain ⟨u, hu⟩ := LBIso.pull_comp hD' n W'.ι
    obtain ⟨c₂, hc₂⟩ := hc₁.exists_gen_of_iso hu ((hD'.pull W'.ι).pull n) (hD'.pull (n ≫ W'.ι))
    obtain ⟨c₃, hc₃⟩ := (AbLaw.Cube.trivial_pull_linComb L' hL' g' d (n ≫ W'.ι)).1 ⟨c₂, hc₂⟩
    obtain ⟨v, hv⟩ := iso_linComb_pull hw g (fun k => (n ≫ W'.ι) ≫ g' k) d W.ι hfac
    have hcomp := hL'.linComb (fun k => (n ≫ W'.ι) ≫ g' k) d
    have hgen : ∃ v : (D.pull W.ι).Gen, v.IsGen :=
      hc₃.exists_gen_of_iso hv hcomp (hD.pull W.ι)
    exact ⟨U, hU, hgen⟩
  have h : e x = x₀ := Over.OverMorphism.ext (he x)
  exact e.injective (h.trans (hp.trans (map_one e).symm))

end GlobalTheory.PolPull
