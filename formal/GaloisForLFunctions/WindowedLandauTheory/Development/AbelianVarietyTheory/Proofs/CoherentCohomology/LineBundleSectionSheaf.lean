import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundles
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! The sheaf of sections of a cocycle-defined line bundle. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}}

abbrev resG (X : Scheme.{0}) {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

private def secOn (L : LB X) (V : X.Opens) : Set (∀ i, Γ(X, V ⊓ L.U i)) :=
  {s | ∀ i j,
    resG X (inf_le_left : V ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i) (s i) =
      resG X (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          V ⊓ L.U i ⊓ L.U j ≤ L.U i ⊓ L.U j) (L.g i j : Γ(X, L.U i ⊓ L.U j)) *
        resG X (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          V ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U j) (s j)}

@[simp] theorem resG_resG {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

@[simp] theorem resG_self {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  have : (homOfLE h).op = 𝟙 (op U) := rfl
  rw [resG, this, X.presheaf.map_id]; rfl

theorem fun_ext_of_cover {ι : Type*} {V : X.Opens} (W : ι → X.Opens) (hW : ∀ k, W k ≤ V)
    (hc : V ≤ iSup W) {a b : Γ(X, V)} (h : ∀ k, resG X (hW k) a = resG X (hW k) b) : a = b :=
  X.sheaf.eq_of_locally_eq' W V (fun k => homOfLE (hW k)) hc a b h

theorem exists_fun_of_cover {ι : Type*} {V : X.Opens} (W : ι → X.Opens) (hW : ∀ k, W k ≤ V)
    (hc : V ≤ iSup W) (a : ∀ k, Γ(X, W k))
    (h : ∀ k l, resG X (inf_le_left : W k ⊓ W l ≤ W k) (a k) =
      resG X (inf_le_right : W k ⊓ W l ≤ W l) (a l)) :
    ∃ b : Γ(X, V), ∀ k, resG X (hW k) b = a k :=
  (X.sheaf.existsUnique_gluing' W V (fun k => homOfLE (hW k)) hc a h).exists

variable (L : LB X)

def secGroup (V : X.Opens) : AddSubgroup (∀ i, Γ(X, V ⊓ L.U i)) where
  carrier := secOn L V
  add_mem' := fun {s t} hs ht i j => by
    simp only [Pi.add_apply, map_add, hs i j, ht i j, mul_add]
  zero_mem' := fun i j => by simp only [Pi.zero_apply, map_zero, mul_zero]
  neg_mem' := fun {s} hs i j => by simp only [Pi.neg_apply, map_neg, hs i j, mul_neg]

variable {L} in

theorem secOn_rel {V : X.Opens} {s : ∀ i, Γ(X, V ⊓ L.U i)} (hs : s ∈ secOn L V) (i j : L.ι)
    {W : X.Opens} (hi : W ≤ V ⊓ L.U i) (hj : W ≤ V ⊓ L.U j) (hij : W ≤ L.U i ⊓ L.U j) :
    resG X hi (s i) = resG X hij (L.g i j : Γ(X, L.U i ⊓ L.U j)) * resG X hj (s j) := by
  have := congrArg (resG X (le_inf hi (hj.trans inf_le_right) : W ≤ V ⊓ L.U i ⊓ L.U j)) (hs i j)
  simpa only [map_mul, resG_resG] using this

instance secGroupModule (V : X.Opens) : Module Γ(X, V) (secGroup L V) where
  smul a s := ⟨fun i => resG X inf_le_left a * s.1 i, fun i j => by
    rw [map_mul, map_mul, s.2 i j, resG_resG, resG_resG, mul_left_comm]⟩
  one_smul s := Subtype.ext <| funext fun i => by
    change resG X _ 1 * s.1 i = _
    rw [map_one, one_mul]
  mul_smul a b s := Subtype.ext <| funext fun i => by
    change resG X _ (a * b) * s.1 i = resG X _ a * (resG X _ b * s.1 i)
    rw [map_mul, mul_assoc]
  smul_zero a := Subtype.ext <| funext fun i => mul_zero _
  smul_add a s t := Subtype.ext <| funext fun i => mul_add _ _ _
  add_smul a b s := Subtype.ext <| funext fun i => by
    change resG X _ (a + b) * s.1 i = resG X _ a * s.1 i + resG X _ b * s.1 i
    rw [map_add, add_mul]
  zero_smul s := Subtype.ext <| funext fun i => by
    change resG X _ 0 * s.1 i = 0
    rw [map_zero, zero_mul]

def secRes {V W : X.Opens} (h : W ≤ V) : secGroup L V →+ secGroup L W where
  toFun s := ⟨fun i => resG X (inf_le_inf_right _ h) (s.1 i), fun i j => by
    rw [resG_resG, resG_resG]
    exact secOn_rel s.2 i j _ _ _⟩
  map_zero' := Subtype.ext <| funext fun i => map_zero _
  map_add' s t := Subtype.ext <| funext fun i => map_add _ _ _

theorem secRes_smul {V W : X.Opens} (h : W ≤ V) (r : Γ(X, V)) (m : secGroup L V) :
    secRes L h (r • m) = resG X h r • secRes L h m :=
  Subtype.ext <| funext fun i => by
    change resG X _ (resG X _ r * m.1 i) = resG X _ (resG X h r) * resG X _ (m.1 i)
    rw [map_mul, resG_resG, resG_resG]

def secPresheaf : TopCat.Presheaf AddCommGrpCat.{0} X where
  obj V := AddCommGrpCat.of (secGroup L V.unop)
  map f := AddCommGrpCat.ofHom (secRes L (leOfHom f.unop))
  map_id V := by
    ext s i
    exact resG_self _ _
  map_comp f g := by
    ext s i
    exact (resG_resG _ _ _).symm

private theorem isSheaf_secPresheaf : (secPresheaf L).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have hc (i : L.ι) : iSup W ⊓ L.U i ≤ ⨆ k, W k ⊓ L.U i := by rw [iSup_inf_eq]
  have hW (i : L.ι) (k : κ) : W k ⊓ L.U i ≤ iSup W ⊓ L.U i := inf_le_inf_right _ (le_iSup W k)
  have H (i : L.ι) : ∃ b : Γ(X, iSup W ⊓ L.U i), ∀ k, resG X (hW i k) b = (sf k).1 i := by
    refine exists_fun_of_cover (fun k => W k ⊓ L.U i) (hW i) (hc i) (fun k => (sf k).1 i)
      fun k l => ?_
    have e : resG X (inf_le_inf_right (L.U i) (inf_le_left : W k ⊓ W l ≤ W k)) ((sf k).1 i) =
        resG X (inf_le_inf_right (L.U i) (inf_le_right : W k ⊓ W l ≤ W l)) ((sf l).1 i) :=
      congrFun (congrArg Subtype.val (hsf k l)) i
    have := congrArg (resG X (le_inf (inf_le_inf inf_le_left inf_le_left)
      (inf_le_left.trans inf_le_right) :
        (W k ⊓ L.U i) ⊓ (W l ⊓ L.U i) ≤ W k ⊓ W l ⊓ L.U i)) e
    simpa only [resG_resG] using this
  -- Glue each coordinate, then verify compatibility on the covered overlaps.
  choose b hb using H
  refine ⟨⟨b, fun i j => ?_⟩, fun k => Subtype.ext (funext fun i => hb i k), fun t ht => ?_⟩
  · refine fun_ext_of_cover (fun k => W k ⊓ L.U i ⊓ L.U j)
      (fun k => inf_le_inf_right _ (hW i k)) (by rw [iSup_inf_eq, iSup_inf_eq]) fun k => ?_
    have := (sf k).2 i j
    rw [← hb i k, ← hb j k] at this
    simpa only [map_mul, resG_resG] using this
  · refine Subtype.ext (funext fun i => fun_ext_of_cover _ (hW i) (hc i) fun k => ?_)
    rw [hb i k]
    exact congrFun (congrArg Subtype.val (ht k)) i

/-- Glue local sections satisfying the transition identities to a scheme module. -/
def toMod : X.Modules :=
  letI : ∀ V, Module (X.ringCatSheaf.obj.obj V) ((secPresheaf L).obj V) :=
    fun V => secGroupModule L V.unop
  { val := PresheafOfModules.ofPresheaf (secPresheaf L) fun _ _ f r m =>
      secRes_smul L (leOfHom f.unop) r m
    isSheaf := isSheaf_secPresheaf L }

variable {L}

def coord {V : X.Opens} (s : Γ(toMod L, V)) (i : L.ι) : Γ(X, V ⊓ L.U i) :=
  (show secGroup L V from s).1 i

theorem coord_mem {V : X.Opens} (s : Γ(toMod L, V)) : coord s ∈ secOn L V :=
  (show secGroup L V from s).2

def mkSec {V : X.Opens} (f : ∀ i, Γ(X, V ⊓ L.U i)) (hf : f ∈ secOn L V) : Γ(toMod L, V) :=
  (⟨f, hf⟩ : secGroup L V)

@[simp] theorem coord_mkSec {V : X.Opens} (f : ∀ i, Γ(X, V ⊓ L.U i)) (hf : f ∈ secOn L V) :
    coord (mkSec f hf) = f := rfl

@[ext] theorem sec_ext {V : X.Opens} {s t : Γ(toMod L, V)} (h : ∀ i, coord s i = coord t i) :
    s = t := Subtype.ext (funext h)

variable (L) in

def secOnEquiv (V : X.Opens) : Γ(toMod L, V) ≃ secOn L V where
  toFun s := ⟨coord s, coord_mem s⟩
  invFun f := mkSec f.1 f.2
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem coord_zero {V : X.Opens} (i : L.ι) : coord (0 : Γ(toMod L, V)) i = 0 := rfl

@[simp] theorem coord_add {V : X.Opens} (s t : Γ(toMod L, V)) (i : L.ι) :
    coord (s + t) i = coord s i + coord t i := rfl

@[simp] theorem coord_neg {V : X.Opens} (s : Γ(toMod L, V)) (i : L.ι) :
    coord (-s) i = - coord s i := rfl

@[simp] theorem coord_sub {V : X.Opens} (s t : Γ(toMod L, V)) (i : L.ι) :
    coord (s - t) i = coord s i - coord t i := rfl

@[simp] theorem coord_smul {V : X.Opens} (a : Γ(X, V)) (s : Γ(toMod L, V)) (i : L.ι) :
    coord (a • s) i = resG X inf_le_left a * coord s i := rfl

@[simp] theorem coord_map {V W : X.Opens} (h : W ≤ V) (s : Γ(toMod L, V)) (i : L.ι) :
    coord ((toMod L).presheaf.map (homOfLE h).op s) i =
      resG X (inf_le_inf_right _ h) (coord s i) := rfl

theorem coord_rel {V : X.Opens} (s : Γ(toMod L, V)) (i j : L.ι)
    {W : X.Opens} (hi : W ≤ V ⊓ L.U i) (hj : W ≤ V ⊓ L.U j) (hij : W ≤ L.U i ⊓ L.U j) :
    resG X hi (coord s i) =
      resG X hij (L.g i j : Γ(X, L.U i ⊓ L.U j)) * resG X hj (coord s j) :=
  secOn_rel (coord_mem s) i j hi hj hij

end GlobalTheory.LineBundleSections
