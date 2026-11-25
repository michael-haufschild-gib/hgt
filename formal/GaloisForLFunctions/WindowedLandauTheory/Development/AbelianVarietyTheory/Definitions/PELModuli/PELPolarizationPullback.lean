import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.IntegralPELObjectMaps
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundleTrivialization

/-! Pullback of the diagonal polarization and of its bounded kernel. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

/-- The two iterated pullbacks around a commuting square are isomorphic. -/
theorem LBIso.pullSquare {W X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {a : W ⟶ Y} {b : W ⟶ Z} {f : Y ⟶ X} {g : Z ⟶ X} (h : a ≫ f = b ≫ g) :
    LBIso ((L.pull f).pull a) ((L.pull g).pull b) :=
  let P := (ChartPull.pull (L.pull f) a).comp (ChartPull.pull L f)
  let Q : ChartPull ((L.pull g).pull b) L (a ≫ f) :=
    h.symm ▸ (ChartPull.pull (L.pull g) b).comp (ChartPull.pull L g)
  P.iso_of_common Q hL

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SiegelPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'}
  {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

/-- A lift into a fibre square is compatible with componentwise composition. -/
theorem lift_sq (sq : IsSquare φ φ₂) {T : Over S} {T' : Over S'} (χ : T.left ⟶ T'.left) (x' y' : T' ⟶ A')
    {Z : Over S} (ψ : T.left ⟶ Z.left) (x y : Z ⟶ A) (hx : χ ≫ x'.left ≫ φ = ψ ≫ x.left)
    (hy : χ ≫ y'.left ≫ φ = ψ ≫ y.left) : χ ≫ (lift x' y').left ≫ φ₂ = ψ ≫ (lift x y).left := by
  refine pullback.hom_ext (f := A.hom) (g := A.hom) ?_ ?_
  · show (χ ≫ (lift x' y').left ≫ φ₂) ≫ (fst A A).left = (ψ ≫ (lift x y).left) ≫ (fst A A).left
    rw [Category.assoc, Category.assoc, sq.1, ← Category.assoc (lift x' y').left, ← Over.comp_left, lift_fst, hx,
      Category.assoc, ← Over.comp_left, lift_fst]
  · show (χ ≫ (lift x' y').left ≫ φ₂) ≫ (snd A A).left = (ψ ≫ (lift x y).left) ≫ (snd A A).left
    rw [Category.assoc, Category.assoc, sq.2, ← Category.assoc (lift x' y').left, ← Over.comp_left, lift_snd, hy,
      Category.assoc, ← Over.comp_left, lift_snd]

/-- On the diagonal, the polarized bundle pulls back along the group projection. -/
theorem diag_iso (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) :
    LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  let a := (lift (𝟙 A') (𝟙 A')).left
  let b := (lift (𝟙 A) (𝟙 A)).left
  have e : a ≫ φ₂ = φ ≫ b := (Category.id_comp _).symm.trans
    (lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (𝟙 A')
      (Z := A) φ (𝟙 A) (𝟙 A)
      (by
        change 𝟙 _ ≫ 𝟙 _ ≫ φ = φ ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id])
      (by
        change 𝟙 _ ≫ 𝟙 _ ≫ φ = φ ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id]))
  exact LBIso.trans (hP'.pull a) ((hP.pull φ₂).pull a) ((hP.pull b).pull φ)
    (H.pull a) (LBIso.pullSquare hP e)

variable [GrpObj A] [GrpObj A'] {f : S' ⟶ S}

/-- A bound on the polarization kernel persists under base change. -/
theorem kernel_pullback (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂)
    {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB)
    (H : LBIso P' (P.pull φ₂)) (e : ℕ)
    (hker : ∀ (T : Over S) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1)
    (T : Over S') (x : T ⟶ A')
    (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x ^ e = 1 := by
  let T₀ := Over.mk (T.hom ≫ f)
  let x₀ : T₀ ⟶ A := LiePull.pushHom h T x
  have hbase : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ hbase
  have h₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have h₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let c : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left h₂
  have hc₁ : c ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have hc₂ : c ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  let u : (A ⊗ T₀).left ⟶ (A ⊗ A).left := (lift (snd A T₀ ≫ x₀) (fst A T₀)).left
  let u' : (A' ⊗ T).left ⟶ (A' ⊗ A').left := (lift (snd A' T ≫ x) (fst A' T)).left
  have e₁ : c ≫ u' ≫ φ₂ = u := by
    refine (lift_sq sq c (snd A' T ≫ x) (fst A' T)
      (T := A ⊗ T₀) (𝟙 _) (snd A T₀ ≫ x₀) (fst A T₀) ?_ ?_).trans (Category.id_comp u)
    · rw [Over.comp_left, Category.assoc, ← Category.assoc c, hc₂, Category.id_comp]
      rfl
    · rw [← Category.assoc, hc₁, h₁, Category.id_comp]
  obtain ⟨s, hs⟩ := hx
  obtain ⟨j, hj⟩ := H.pull u'
  obtain ⟨s', hs'⟩ := hs.exists_gen_of_iso hj (hP'.pull u') ((hP.pull φ₂).pull u')
  obtain ⟨s'', hs''⟩ := (ChartPull.pull ((P.pull φ₂).pull u') c).exists_gen hs'
  let C₁ := (ChartPull.pull ((P.pull φ₂).pull u') c).comp
    ((ChartPull.pull (P.pull φ₂) u').comp (ChartPull.pull P φ₂))
  let C₂ : ChartPull (P.pull u) P (c ≫ u' ≫ φ₂) := e₁.symm ▸ ChartPull.pull P u
  obtain ⟨j', hj'⟩ := C₁.iso_of_common C₂ hP
  have htriv := hs''.exists_gen_of_iso hj' (((hP.pull φ₂).pull u').pull c) (hP.pull u)
  have e₂ : x₀ ^ e = 1 := hker T₀ x₀ htriv
  have hinj : Function.Injective (LiePull.pushHom h T) := fun a b eq =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg Over.Hom.left eq) ((Over.w a).trans (Over.w b).symm))
  exact hinj ((map_pow _ _ _).trans (e₂.trans (map_one _).symm))

end GlobalTheory.SiegelPull

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

/-- A polarization isomorphism between two pullbacks persists for
compatible endomorphisms of the base-changed scheme. -/
theorem LBIso.pull_commuting {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (f : Y ⟶ X) {x y : X ⟶ X} {x' y' : Y ⟶ Y}
    (hx : x' ≫ f = f ≫ x) (hy : y' ≫ f = f ≫ y)
    (h : LBIso (L.pull x) (L.pull y)) :
    LBIso ((L.pull f).pull x') ((L.pull f).pull y') := by
  have e₁ := LBIso.pullSquare hL hx
  have e₂ := LBIso.pullSquare hL hy
  have hx' := (hL.pull f).pull x'
  have hy' := (hL.pull f).pull y'
  have hxf := (hL.pull x).pull f
  have hyf := (hL.pull y).pull f
  exact LBIso.trans hx' hyf hy' (LBIso.trans hx' hxf hyf e₁ (h.pull f)) e₂.symm

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SiegelPull

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S)

local notation "A₁" => Functor.obj (Over.pullback f) A

/-- A generator along a pair of sections pulls back along compatible sections. -/
theorem pull_axis_gen {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (x' y' : A₁ ⟶ A₁) (x y : A ⟶ A)
    (hx : x'.left ≫ pφ f A = pφ f A ≫ x.left)
    (hy : y'.left ≫ pφ f A = pφ f A ≫ y.left)
    (h : ∃ t : (P.pull (lift x y).left).Gen, t.IsGen) :
    ∃ t : ((P.pull (pφ₂ f A)).pull (lift x' y').left).Gen, t.IsGen := by
  have e : (lift x' y').left ≫ pφ₂ f A = pφ f A ≫ (lift x y).left :=
    (Category.id_comp _).symm.trans
      (lift_sq (isSquare f A) (T := Over.mk (pφ f A ≫ A.hom))
        (𝟙 (A₁).left) x' y' (pφ f A) x y
        ((Category.id_comp _).trans hx) ((Category.id_comp _).trans hy))
  obtain ⟨t, ht⟩ := h
  exact LB.exists_gen_of_pullbackSquare hP e.symm ht

/-- Swapping the two factors of the polarized fibre square commutes with base change. -/
theorem pull_symmetric {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (h : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) :
    LBIso (P.pull (pφ₂ f A))
      ((P.pull (pφ₂ f A)).pull (lift (snd A₁ A₁) (fst A₁ A₁)).left) := by
  let s := (lift (snd A A) (fst A A)).left
  let s' := (lift (snd A₁ A₁) (fst A₁ A₁)).left
  have e : s' ≫ pφ₂ f A = pφ₂ f A ≫ s := (Category.id_comp _).symm.trans
    (lift_sq (isSquare f A) (T := Over.mk (pφ₂ f A ≫ (A ⊗ A).hom))
      (𝟙 (A₁ ⊗ A₁).left) (snd A₁ A₁) (fst A₁ A₁) (pφ₂ f A)
      (snd A A) (fst A A)
      ((Category.id_comp _).trans (pφ₂_snd f A).symm)
      ((Category.id_comp _).trans (pφ₂_fst f A).symm))
  exact LBIso.trans (hP.pull (pφ₂ f A)) ((hP.pull s).pull (pφ₂ f A))
    ((hP.pull (pφ₂ f A)).pull s') (h.pull (pφ₂ f A)) (LBIso.pullSquare hP e.symm)

/-- Base change preserves the adjoint relation for two order elements. -/
theorem pull_adjoint {O : Type} [Ring O] [GrpObj A] (act : GlobalTheory.UPel.HT.OActN O A)
    {P : LB (A ⊗ A).left} (hP : P.IsLB) (b c : O)
    (h : LBIso (P.pull (lift (fst A A ≫ act.act b) (snd A A)).left)
      (P.pull (lift (fst A A) (snd A A ≫ act.act c)).left)) :
    LBIso ((P.pull (pφ₂ f A)).pull (lift (fst A₁ A₁ ≫ (act.pullback f).act b) (snd A₁ A₁)).left)
      ((P.pull (pφ₂ f A)).pull (lift (fst A₁ A₁) (snd A₁ A₁ ≫ (act.pullback f).act c)).left) := by
  let F := pφ₂ f A
  have hact (x : O) : ((act.pullback f).act x).left ≫ pφ f A = pφ f A ≫ (act.act x).left :=
    pullback_map_left_fst' f (act.act x)
  have hc {r' : A₁ ⊗ A₁ ⟶ A₁} {r : A ⊗ A ⟶ A}
      (hr : r'.left ≫ pφ f A = F ≫ r.left) (x : O) :
      (r' ≫ (act.pullback f).act x).left ≫ pφ f A = F ≫ (r ≫ act.act x).left := by
    calc
      _ = r'.left ≫ (((act.pullback f).act x).left ≫ pφ f A) := Category.assoc _ _ _
      _ = r'.left ≫ (pφ f A ≫ (act.act x).left) := congrArg (r'.left ≫ ·) (hact x)
      _ = (r'.left ≫ pφ f A) ≫ (act.act x).left := (Category.assoc _ _ _).symm
      _ = (F ≫ r.left) ≫ (act.act x).left := congrArg (· ≫ (act.act x).left) hr
      _ = _ := Category.assoc _ _ _
  have hl (x' y' : A₁ ⊗ A₁ ⟶ A₁) (x y : A ⊗ A ⟶ A)
      (hx : x'.left ≫ pφ f A = F ≫ x.left) (hy : y'.left ≫ pφ f A = F ≫ y.left) :
      (lift x' y').left ≫ F = F ≫ (lift x y).left :=
    (Category.id_comp _).symm.trans (lift_sq (isSquare f A) (T := Over.mk (F ≫ (A ⊗ A).hom))
      (𝟙 (A₁ ⊗ A₁).left) x' y' F x y
      ((Category.id_comp _).trans hx) ((Category.id_comp _).trans hy))
  exact LBIso.pull_commuting hP F
    (hl _ _ _ _ (hc (pφ₂_fst f A).symm b) (pφ₂_snd f A).symm)
    (hl _ _ _ _ (pφ₂_fst f A).symm (hc (pφ₂_snd f A).symm c)) h

end GlobalTheory.SiegelPull
