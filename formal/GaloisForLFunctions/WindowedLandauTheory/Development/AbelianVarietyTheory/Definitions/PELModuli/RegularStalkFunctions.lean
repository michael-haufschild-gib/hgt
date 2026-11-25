import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Regular stalk families and their localization to a principal open. -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory.AmpleLocal

variable {Z : Scheme.{0}}

abbrev Fn (Z : Scheme.{0}) : Type := ∀ z : Z, Z.presheaf.stalk z

/-- Stalk families represented by a regular section on the given open. -/
def Reg (V : Z.Opens) : Subring (Fn Z) where
  carrier := {F | ∃ a : Γ(Z, V), ∀ z (hz : z ∈ V), (Z.presheaf.germ V z hz).hom a = F z}
  mul_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, fun z hz => by rw [map_mul, ha, hb]; rfl⟩
  one_mem' := ⟨1, fun z hz => by rw [map_one]; rfl⟩
  add_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, fun z hz => by rw [map_add, ha, hb]; rfl⟩
  zero_mem' := ⟨0, fun z hz => by rw [map_zero]; rfl⟩
  neg_mem' := fun ⟨a, ha⟩ => ⟨-a, fun z hz => by rw [map_neg, ha]; rfl⟩

def IsLoc (D W : Z.Opens) (F : Fn Z) : Prop := ∀ z, z ∈ D ↔ z ∈ W ∧ IsUnit (F z)

def inv (F : Fn Z) : Fn Z := fun z => Ring.inverse (F z)

def Gen (D : Z.Opens) (S : Set (Fn Z)) : Prop :=
  ∀ F ∈ Reg D, ∃ b ∈ Subring.closure S, ∀ z ∈ D, F z = b z

theorem sec_ext {V : Z.Opens} {a b : Γ(Z, V)}
    (h : ∀ z (hz : z ∈ V), (Z.presheaf.germ V z hz).hom a = (Z.presheaf.germ V z hz).hom b) : a = b :=
  TopCat.Presheaf.section_ext Z.sheaf V a b h

theorem germ_res' {V W : Z.Opens} (h : V ≤ W) (a : Γ(Z, W)) (z : Z) (hz : z ∈ V) :
    (Z.presheaf.germ V z hz).hom ((Z.presheaf.map (homOfLE h).op).hom a) = (Z.presheaf.germ W z (h hz)).hom a :=
  TopCat.Presheaf.germ_res_apply Z.presheaf _ z hz a

theorem reg_mono {V W : Z.Opens} (h : V ≤ W) {F : Fn Z} (hF : F ∈ Reg W) : F ∈ Reg V := by
  obtain ⟨a, ha⟩ := hF
  exact ⟨_, fun z hz => (germ_res' h a z hz).trans (ha z _)⟩

theorem reg_congr {V : Z.Opens} {F G : Fn Z} (hF : F ∈ Reg V) (h : ∀ z ∈ V, F z = G z) : G ∈ Reg V := by
  obtain ⟨a, ha⟩ := hF
  exact ⟨a, fun z hz => (ha z hz).trans (h z hz)⟩

theorem reg_glue {V : Z.Opens} {F : Fn Z} (h : ∀ z ∈ V, ∃ O : Z.Opens, z ∈ O ∧ F ∈ Reg O) : F ∈ Reg V := by
  choose O hO hF using h
  let W : V → Z.Opens := fun z => O z.1 z.2 ⊓ V
  choose a ha using fun z : V => reg_mono (inf_le_left : W z ≤ _) (hF z.1 z.2)
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' W V (fun i => homOfLE inf_le_right)
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hO z hz, hz⟩) a
    (fun i j => sec_ext (V := W i ⊓ W j) fun z hz =>
      ((germ_res' inf_le_left _ z hz).trans (ha i z _)).trans ((germ_res' inf_le_right _ z hz).trans (ha j z _)).symm)
  refine ⟨s, fun z hz => ?_⟩
  have hm : z ∈ W ⟨z, hz⟩ := ⟨hO z hz, hz⟩
  exact (germ_res' inf_le_right s z hm).symm.trans
    ((congrArg (Z.presheaf.germ _ z hm).hom (hs ⟨z, hz⟩)).trans (ha _ z hm))

theorem reg_inv {V : Z.Opens} {F : Fn Z} (hF : F ∈ Reg V) (hu : ∀ z ∈ V, IsUnit (F z)) : inv F ∈ Reg V := by
  obtain ⟨a, ha⟩ := hF
  have : IsUnit a := Z.toRingedSpace.isUnit_of_isUnit_germ _ _ fun z hz => by
    have := hu z hz
    rw [← ha z hz] at this
    exact this
  obtain ⟨b, hb⟩ := this.exists_right_inv
  refine ⟨b, fun z hz => ?_⟩
  have e := congrArg (Z.presheaf.germ V z hz).hom hb
  rw [map_mul, map_one, ha] at e
  exact ((Ring.eq_mul_inverse_iff_mul_eq _ _ _ (hu z hz)).2 (by rw [mul_comm, e])).trans (one_mul _)

theorem IsLoc.le {D W : Z.Opens} {F : Fn Z} (h : IsLoc D W F) : D ≤ W := fun z hz => ((h z).1 hz).1

theorem IsLoc.unit {D W : Z.Opens} {F : Fn Z} (h : IsLoc D W F) {z : Z} (hz : z ∈ D) : IsUnit (F z) := ((h z).1 hz).2

theorem IsLoc.eq_basicOpen {D W : Z.Opens} {F : Fn Z} (h : IsLoc D W F) {a : Γ(Z, W)}
    (ha : ∀ z (hz : z ∈ W), (Z.presheaf.germ W z hz).hom a = F z) : D = Z.basicOpen a := by
  ext z
  refine (h z).trans ⟨fun ⟨hz, hu⟩ => (Z.mem_basicOpen a z hz).2 (by rw [← ha z hz] at hu; exact hu), fun hz => ?_⟩
  have hw := Z.basicOpen_le a hz
  exact ⟨hw, by rw [← ha z hw]; exact (Z.mem_basicOpen a z hw).1 hz⟩

theorem exists_loc {W : Z.Opens} {F : Fn Z} (hF : F ∈ Reg W) : ∃ D, IsLoc D W F := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨Z.basicOpen a, fun z => ⟨fun hz => ?_, fun ⟨hz, hu⟩ =>
    (Z.mem_basicOpen a z hz).2 (by rw [← ha z hz] at hu; exact hu)⟩⟩
  have hw := Z.basicOpen_le a hz
  exact ⟨hw, by rw [← ha z hw]; exact (Z.mem_basicOpen a z hw).1 hz⟩

theorem IsLoc.affine {D W : Z.Opens} {F : Fn Z} (h : IsLoc D W F) (hF : F ∈ Reg W) (hW : IsAffineOpen W) :
    IsAffineOpen D := by
  obtain ⟨a, ha⟩ := hF
  rw [h.eq_basicOpen ha]
  exact hW.basicOpen a

theorem kill {D W : Z.Opens} {w F : Fn Z} (hW : IsCompact (W : Set Z)) (h : IsLoc D W w) (hw : w ∈ Reg W)
    (hF : F ∈ Reg W) (h0 : ∀ z ∈ D, F z = 0) : ∃ n : ℕ, ∀ z ∈ W, w z ^ n * F z = 0 := by
  obtain ⟨a, ha⟩ := hw
  obtain ⟨x, hx⟩ := hF
  obtain rfl := h.eq_basicOpen ha
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact Z hW x a
    (sec_ext fun z hz => (germ_res' (Z.basicOpen_le a) x z hz).trans (by rw [hx, h0 z hz, map_zero]))
  refine ⟨n, fun z hz => ?_⟩
  have e := congrArg (Z.presheaf.germ W z hz).hom hn
  rwa [map_mul, map_pow, map_zero, ha, hx] at e

theorem frac {D W : Z.Opens} {w F : Fn Z} (hW : IsAffineOpen W) (h : IsLoc D W w) (hw : w ∈ Reg W)
    (hF : F ∈ Reg D) : ∃ n : ℕ, ∃ G ∈ Reg W, ∀ z ∈ D, w z ^ n * F z = G z := by
  classical
  obtain ⟨a, ha⟩ := hw
  obtain ⟨x, hx⟩ := hF
  obtain rfl := h.eq_basicOpen ha
  obtain ⟨n, y, hn⟩ := exists_eq_pow_mul_of_isAffineOpen Z W hW a x
  refine ⟨n, fun z => if hz : z ∈ W then (Z.presheaf.germ W z hz).hom y else 0, ⟨y, fun z hz => by beta_reduce; rw [dif_pos hz]⟩,
    fun z hz => ?_⟩
  have hw := Z.basicOpen_le a hz
  have e := congrArg (Z.presheaf.germ _ z hz).hom hn
  rw [map_mul, map_pow, hx] at e
  exact ((dif_pos hw).trans ((germ_res' (Z.basicOpen_le a) y z hz).symm.trans (e.trans (congrArg (· ^ n * F z)
    ((germ_res' (Z.basicOpen_le a) a z hz).trans (ha z hw)))))).symm

theorem Gen.mono {D : Z.Opens} {S S' : Set (Fn Z)} (h : Gen D S)
    (hS : ∀ x ∈ S, ∃ b ∈ Subring.closure S', ∀ z ∈ D, x z = b z) : Gen D S' := by
  intro F hF
  obtain ⟨b, hb, e⟩ := h F hF
  suffices ∃ b' ∈ Subring.closure S', ∀ z ∈ D, b z = b' z by
    obtain ⟨b', hb', e'⟩ := this
    exact ⟨b', hb', fun z hz => (e z hz).trans (e' z hz)⟩
  clear e
  induction hb using Subring.closure_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨0, zero_mem _, fun _ _ => rfl⟩
  | one => exact ⟨1, one_mem _, fun _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, e⟩ := hx
    obtain ⟨b, hb, e'⟩ := hy
    exact ⟨a + b, add_mem ha hb, fun z hz => congrArg₂ (· + ·) (e z hz) (e' z hz)⟩
  | neg x _ hx =>
    obtain ⟨a, ha, e⟩ := hx
    exact ⟨-a, neg_mem ha, fun z hz => congrArg (- ·) (e z hz)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, e⟩ := hx
    obtain ⟨b, hb, e'⟩ := hy
    exact ⟨a * b, mul_mem ha hb, fun z hz => congrArg₂ (· * ·) (e z hz) (e' z hz)⟩

theorem Gen.loc {D W : Z.Opens} {w : Fn Z} {S : Set (Fn Z)} (hW : IsAffineOpen W) (h : IsLoc D W w) (hw : w ∈ Reg W)
    (hS : Gen W S) : Gen D (insert (inv w) S) := by
  intro F hF
  obtain ⟨n, G, hG, e⟩ := frac hW h hw hF
  obtain ⟨b, hb, e'⟩ := hS G hG
  refine ⟨inv w ^ n * b, mul_mem (pow_mem (Subring.subset_closure (Set.mem_insert _ _)) _)
    (Subring.closure_mono (Set.subset_insert _ _) hb), fun z hz => ?_⟩
  show F z = Ring.inverse (w z) ^ n * b z
  rw [← e' z (h.le hz), ← e z hz, ← mul_assoc, ← mul_pow, Ring.inverse_mul_cancel _ (h.unit hz), one_pow, one_mul]

end GlobalTheory.AmpleLocal
