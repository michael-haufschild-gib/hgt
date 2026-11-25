import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.IntegralPELObjectMaps

/-! Factorization of maps through cartesian integral PEL objects. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

/-- The left square of two composable cartesian group maps is cartesian. -/
theorem IsGrpPullback.cancel {S S' T : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {P : Over T} [GrpObj P] {f : S' ⟶ S} {t : T ⟶ S'} {φ : G'.left ⟶ G.left} {ψ : P.left ⟶ G'.left}
    (h : IsGrpPullback G' G f φ) (n : IsGrpPullback P G (t ≫ f) (ψ ≫ φ))
    (w : ψ ≫ G'.hom = P.hom ≫ t) : IsGrpPullback P G' t ψ := by
  refine ⟨IsPullback.of_right n.1 w h.1, fun T₀ x y x₀ y₀ hx hy => ?_⟩
  let T₁ := Over.mk (T₀.hom ≫ t)
  let u := GlobalTheory.LiePull.pushHom h T₁
  let v := GlobalTheory.LiePull.pushHom n T₀
  let e : Over.mk (T₁.hom ≫ f) ⟶ Over.mk (T₀.hom ≫ t ≫ f) :=
    Over.homMk (𝟙 T₀.left) ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have hx₁ : u x₀ = e ≫ v x := Over.OverMorphism.ext
    ((congrArg (· ≫ φ) hx).trans ((Category.assoc _ _ _).trans (Category.id_comp _).symm))
  have hy₁ : u y₀ = e ≫ v y := Over.OverMorphism.ext
    ((congrArg (· ≫ φ) hy).trans ((Category.assoc _ _ _).trans (Category.id_comp _).symm))
  have hm : u (x₀ * y₀) = e ≫ v (x * y) :=
    (map_mul u x₀ y₀).trans ((congrArg₂ (· * ·) hx₁ hy₁).trans
      ((MonObj.comp_mul e (v x) (v y)).symm.trans (congrArg (e ≫ ·) (map_mul v x y).symm)))
  apply h.1.hom_ext
  · exact (congrArg Over.Hom.left hm).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  · calc
      _ = (T₀.hom ≫ t) := Over.w (x₀ * y₀)
      _ = (x * y).left ≫ P.hom ≫ t :=
        (congrArg (· ≫ t) (Over.w (x * y)).symm).trans (Category.assoc _ _ _)
      _ = (x * y).left ≫ ψ ≫ G'.hom := congrArg ((x * y).left ≫ ·) w.symm
      _ = _ := (Category.assoc _ _ _).symm

/-- The map on the fibre square is determined by its two projections. -/
theorem IsSquare.unique {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b :=
  pullback.hom_ext (f := G.hom) (g := G.hom) (ha.1.trans hb.1.symm) (ha.2.trans hb.2.symm)

theorem exists_isSquare {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (w : φ ≫ G.hom = G'.hom ≫ f) :
    ∃ φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, IsSquare φ φ₂ := by
  let a : (G' ⊗ G').left ⟶ G.left := (fst G' G').left ≫ φ
  let b : (G' ⊗ G').left ⟶ G.left := (snd G' G').left ≫ φ
  have e : a ≫ G.hom = b ≫ G.hom := by
    change ((fst G' G').left ≫ φ) ≫ G.hom = ((snd G' G').left ≫ φ) ≫ G.hom
    rw [Category.assoc, Category.assoc, w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]
  exact ⟨pullback.lift a b e, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

/-- A cartesian object map through a cartesian factor induces the remaining object map. -/
theorem ObjMap.factor {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : ObjMap o₁ o₃ (f ≫ g)) (m₂ : ObjMap o₂ o₃ g) : Nonempty (ObjMap o₁ o₂ f) := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := m.cart.1.w.trans (Category.assoc _ _ _).symm
  let φ : o₁.A.left ⟶ o₂.A.left := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := hφ.symm ▸ m.cart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := m.sq.unique (hφ ▸ sq.comp m₂.sq)
  have hact (c : D.O) : (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta (y : D.La) : (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    let x₁ : S₁ ⟶ o₁.A.left := (o₁.eta y).left
    let x₂ : S₂ ⟶ o₂.A.left := (o₂.eta y).left
    let x₃ : S₃ ⟶ o₃.A.left := (o₃.eta y).left
    have hx₁ : x₁ ≫ m.φ = (f ≫ g) ≫ x₃ := m.eta y
    have hx₂ : x₂ ≫ m₂.φ = g ≫ x₃ := m₂.eta y
    have hy₁ : x₁ ≫ o₁.A.hom = 𝟙 S₁ := Over.w (o₁.eta y)
    have hy₂ : x₂ ≫ o₂.A.hom = 𝟙 S₂ := Over.w (o₂.eta y)
    change x₁ ≫ φ = f ≫ x₂
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, hx₁, Category.assoc, Category.assoc, hx₂]
    · rw [Category.assoc, hφ', ← Category.assoc, hy₁, Category.assoc, hy₂, Category.id_comp, Category.comp_id]
  have hpol : LBIso (o₂.P.pull φ₂) (o₃.P.pull m.φ₂) := by
    rw [e]
    exact LBIso.trans (o₂.isLB.pull φ₂) ((o₃.isLB.pull m₂.φ₂).pull φ₂) (o₃.isLB.pull (φ₂ ≫ m₂.φ₂))
      (m₂.pol.pull φ₂) (LBIso.pull_comp o₃.isLB φ₂ m₂.φ₂)
  exact ⟨{
    φ := φ
    φ₂ := φ₂
    cart := m₂.cart.cancel n hφ'
    sq := sq
    act := hact
    pol := LBIso.trans o₁.isLB (o₃.isLB.pull m.φ₂) (o₂.isLB.pull φ₂) m.pol hpol.symm
    eta := heta }⟩

end GlobalTheory.UPel.HT
