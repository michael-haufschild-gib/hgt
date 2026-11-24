import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.IntegralPELModuli

/-! Reinterpreting integral PEL objects and their level structures over a rational base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.UPel.HT.GenCmp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R']
  {S : Scheme.{0}}

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (u : Sp B ⟶ Sp A) : ∃ β : A →+* B, u = spMap β :=
  ⟨(Spec.preimage u).hom, by simp [spMap]⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap φ = spMap (β.comp φ) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {β β' : A →+* B} (h : spMap β = spMap β') : β = β' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/-- The geometric Tate structure extends to every positive level. -/
def GeomFull {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (t : S ⟶ Sp R') : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R' →+* k), x ≫ t = spMap β →
    ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
        (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ o.eta y = I.ev N y

/-- The polarization kernel is killed by a prime-to-p integer. -/
def KerP {gb : GBase D.toG R'} {N : ℕ} {t : S ⟶ Sp R'} (o : GObj gb N t) : Prop :=
  ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A),
    (∃ u : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, u.IsGen) → x ^ e = 1

variable {b : Base D R} {gb : GBase D.toG R'} {N : ℕ} {φ : R →+* R'}

/-- Restrict the integral moduli data to a compatible rational base. -/
def rebase (hρ : gb.ρ = φ b.ρ) (ht : ∀ i, gb.t i = φ.comp (b.t i)) {t : S ⟶ Sp R'} {s : S ⟶ Sp R}
    (hs : s = t ≫ spMap φ) (o : Obj b N s) : Obj (Base.ofGeneric (D := D) gb) N t where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := o.kerP
  rosati := o.rosati
  lie R₁ _ β x hx v hv := by
    have h := o.lie R₁ (β.comp φ) x (by rw [hs, ← Category.assoc, hx, spMap_comp']) v
      (by simpa [Base.ofGeneric, hρ] using hv)
    obtain ⟨w, hw, hvw⟩ := h
    exact ⟨w, fun i c => (congrArg (fun z => IsTanScal o.act x (algebraMap (𝓞 D.F) D.O c) (β z) (w i))
      (DFunLike.congr_fun (ht i) c)).mpr (hw i c), hvw⟩
  lieRank k _ _ x β hx i :=
    (congrArg (fun z => LieMult (o.act.restrict (algebraMap (𝓞 D.F) D.O)) x (β.comp z) D.m) (ht i)).mpr
      (o.lieRank k x (β.comp φ) (by rw [hs, ← Category.assoc, hx, spMap_comp']) i)
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom k _ _ x β hx := o.geom k x (β.comp φ) (by rw [hs, ← Category.assoc, hx, spMap_comp'])

/-- Pass to the generic moduli problem with a full geometric Tate structure. -/
def toGObj {t : S ⟶ Sp R'} (o : Obj (Base.ofGeneric (D := D) gb) N t) (h : GeomFull o t) : GObj gb N t where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom := h

/-- Restrict a full Tate structure to prime-to-p levels. -/
def tateRestrict {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : GTateIso D.toG k Q act e) : TateIsoO D k Q act e where
  ζ := I.ζ
  ζ_prim n hn _ := I.ζ_prim n hn
  ζ_pow n m hn hm _ := I.ζ_pow n m hn hm
  ev := I.ev
  add := I.add
  lin := I.lin
  ker n hn _ := I.ker n hn
  onto n hn _ := I.onto n hn
  tower n m hn hm _ := I.tower n m hn hm
  isom n hn _ := I.isom n hn

/-- Forget the p-power level structure for an integral polarization. -/
def toObj (hρ : gb.ρ = φ b.ρ) (ht : ∀ i, gb.t i = φ.comp (b.t i)) {t : S ⟶ Sp R'} (o : GObj gb N t)
    (h : KerP o) : Obj b N (t ≫ spMap φ) where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := h
  rosati := o.rosati
  lie R₁ _ β x hx v hv := by
    obtain ⟨β', hβ'⟩ := exists_spMap (x ≫ t)
    obtain rfl : β = β'.comp φ := spMap_inj (by rw [← hx, ← Category.assoc, hβ', spMap_comp'])
    obtain ⟨w, hw, hvw⟩ := o.lie R₁ β' x hβ' v (by rw [hρ]; exact hv)
    exact ⟨w, fun i c => (congrArg (fun z => IsTanScal o.act x (algebraMap (𝓞 D.F) D.O c) (β' z) (w i))
      (DFunLike.congr_fun (ht i) c)).mp (hw i c), hvw⟩
  lieRank k _ _ x β hx i := by
    obtain ⟨β', hβ'⟩ := exists_spMap (x ≫ t)
    obtain rfl : β = β'.comp φ := spMap_inj (by rw [← hx, ← Category.assoc, hβ', spMap_comp'])
    exact (congrArg (fun z => LieMult (o.act.restrict (algebraMap (𝓞 D.F) D.O)) x (β'.comp z) D.m) (ht i)).mp (o.lieRank k x β' hβ' i)
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom k _ _ x β hx := by
    obtain ⟨β', hβ'⟩ := exists_spMap (x ≫ t)
    obtain ⟨I, hI⟩ := o.geom k x β' hβ'
    exact ⟨tateRestrict I, hI⟩

end GlobalTheory.UPel.HT.GenCmp
