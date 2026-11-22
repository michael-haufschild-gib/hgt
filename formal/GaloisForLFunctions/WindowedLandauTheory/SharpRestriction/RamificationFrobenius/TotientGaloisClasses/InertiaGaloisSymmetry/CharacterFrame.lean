import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.QuadraticArtinAction
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameCyclicGenerator

/-! The image of the dyadic projection and character quotient is a frame. -/

noncomputable section

namespace WindowedLandauTheory.HC

open WindowedLandauTheory.FrobeniusOrbits WindowedLandauTheory.TwoAdicCyclotomicDecomposition

/-- A character quotient of the units at a level containing the dyadic tower. -/
structure ModData where
  e : ℕ
  m : ℕ
  m_pos : 0 < m
  tower : 2 ^ (e + 2) ∣ m
  B : Type
  [grp : CommGroup B]
  ξ : (ZMod m)ˣ →* B

attribute [instance] ModData.grp

namespace ModData

variable (D : ModData)

instance neZero : NeZero D.m := ⟨D.m_pos.ne'⟩

def cl : (ZMod D.m)ˣ →* HGrp D.e := (QuotientGroup.mk' _).comp (ZMod.unitsMap D.tower)

theorem cl_apply (u : (ZMod D.m)ˣ) : D.cl u = hcl D.e (ZMod.unitsMap D.tower u) := rfl

def eta : (ZMod D.m)ˣ →* HGrp D.e × D.B := D.cl.prod D.ξ

theorem cl_neg_one : D.cl (-1) = 1 := by
  rw [cl_apply, D7.unitsMap_neg_one]
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)

abbrev R : Type := D.eta.range

instance : Finite D.R := Finite.of_surjective _ D.eta.rangeRestrict_surjective

instance : Fintype (Additive D.R) := Fintype.ofFinite _

def p1 : D.R →* HGrp D.e := (MonoidHom.fst _ _).comp D.eta.range.subtype

def p2 : D.R →* D.B := (MonoidHom.snd _ _).comp D.eta.range.subtype

theorem eq_one_of {x : D.R} (h1 : D.p1 x = 1) (h2 : D.p2 x = 1) : x = 1 := Subtype.ext (Prod.ext h1 h2)

theorem projection_surjective : Function.Surjective D.p1 := by
  intro h
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective h
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective D.tower u
  refine ⟨⟨D.eta v, v, rfl⟩, ?_⟩
  show D.cl v = _
  rw [cl_apply, hv]
  rfl

theorem exists_gen : ∃ a : D.R, ∀ x : D.R, D.p2 x = 1 ↔ x ∈ Subgroup.zpowers a := by
  haveI : IsCyclic (HGrp D.e) := (hostGroup D.e).2.2.2.2.2.1
  have hinj : Function.Injective (D.p1.comp D.p2.ker.subtype) :=
    (injective_iff_map_eq_one _).mpr fun x hx =>
      Subtype.ext (D.eq_one_of hx (MonoidHom.mem_ker.mp x.2))
  haveI : IsCyclic D.p2.ker := isCyclic_of_injective (D.p1.comp D.p2.ker.subtype) hinj
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D.p2.ker)
  refine ⟨g.1, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h3 := congrArg Subtype.val hk
    simpa using h3
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [map_zpow, MonoidHom.mem_ker.mp g.2, one_zpow]

def gen : D.R := D.exists_gen.choose

theorem gen_spec (x : D.R) : D.p2 x = 1 ↔ x ∈ Subgroup.zpowers D.gen := D.exists_gen.choose_spec x

def hA : Additive D.R →+ Additive (HGrp D.e) := MonoidHom.toAdditive D.p1

theorem hA_surj : Function.Surjective D.hA := D.projection_surjective

theorem hA_ker (k : ℤ) (hk : D.hA (k • Additive.ofMul D.gen) = 0) : k • Additive.ofMul D.gen = 0 := by
  rw [← ofMul_zpow] at hk ⊢
  have h2 : D.p2 (D.gen ^ k) = 1 := by
    rw [map_zpow, (D.gen_spec D.gen).mpr (Subgroup.mem_zpowers _), one_zpow]
  have h1 : D.p1 (D.gen ^ k) = 1 := by
    rw [← ofMul_eq_zero]
    exact hk
  rw [ofMul_eq_zero]
  exact D.eq_one_of h1 h2

def frame : Frame := Frame.ofGroup D.e D.hA D.hA_surj (Additive.ofMul D.gen) D.hA_ker

def isoA : D.frame.A ≃+ Additive D.R := Frame.ofGroupIso D.e D.hA D.hA_surj (Additive.ofMul D.gen) D.hA_ker

def iso : D.frame.MA ≃* D.R where
  toFun a := (D.isoA a.toAdd).toMul
  invFun x := Multiplicative.ofAdd (D.isoA.symm (Additive.ofMul x))
  left_inv a := by simp
  right_inv x := by simp
  map_mul' a b := by simp

theorem frame_e : D.frame.e = D.e := rfl

theorem hH_eq (a : D.frame.MA) : D.frame.hH a = D.p1 (D.iso a) := rfl

theorem iso_generator : D.iso (D.frame.iota D.frame.a0) = D.gen := by
  have h := Frame.ofGroup_generator D.e D.hA D.hA_surj (Additive.ofMul D.gen) D.hA_ker
  show (D.isoA D.frame.a0).toMul = D.gen
  exact congrArg Additive.toMul h

theorem ord_eq : D.frame.ord = Nat.card D.R := by
  rw [frame, Frame.ofGroup_ord, ← Nat.card_eq_fintype_card]
  rfl

def toA : (ZMod D.m)ˣ →* D.frame.MA := D.iso.symm.toMonoidHom.comp D.eta.rangeRestrict

theorem iso_toA (u : (ZMod D.m)ˣ) : D.iso (D.toA u) = D.eta.rangeRestrict u := D.iso.apply_symm_apply _

theorem toA_surj : Function.Surjective D.toA := D.iso.symm.surjective.comp (MonoidHom.rangeRestrict_surjective _)

theorem toA_eq_one_iff (u : (ZMod D.m)ˣ) : D.toA u = 1 ↔ D.eta u = 1 := by
  rw [← D.iso.injective.eq_iff, map_one, iso_toA, Subtype.ext_iff]
  rfl

theorem hH_toA (u : (ZMod D.m)ˣ) : D.frame.hH (D.toA u) = D.cl u := by
  rw [hH_eq, iso_toA]
  rfl

def xiA : D.frame.MA →* D.B := D.p2.comp D.iso.toMonoidHom

theorem xiA_toA (u : (ZMod D.m)ˣ) : D.xiA (D.toA u) = D.ξ u := by
  show D.p2 (D.iso (D.toA u)) = _
  rw [iso_toA]
  rfl

theorem mem_A0_iff_xiA_eq_one (t : D.frame.A) : t ∈ D.frame.A0 ↔ D.xiA (D.frame.iota t) = 1 := by
  have ha0 : D.isoA D.frame.a0 = Additive.ofMul D.gen :=
    Frame.ofGroup_generator D.e D.hA D.hA_surj (Additive.ofMul D.gen) D.hA_ker
  show t ∈ AddSubgroup.zmultiples D.frame.a0 ↔ D.p2 ((D.isoA t).toMul) = 1
  rw [D.gen_spec, AddSubgroup.mem_zmultiples_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [map_zsmul, ha0]; rfl⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, D.isoA.injective ?_⟩
    rw [map_zsmul, ha0, ← ofMul_zpow, hk]
    rfl

theorem range_xiA : D.xiA.range = D.ξ.range := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨u, rfl⟩ := D.toA_surj a
    exact ⟨u, (D.xiA_toA u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨D.toA u, D.xiA_toA u⟩

theorem o_eq : D.frame.o = Nat.card D.ξ.range := by
  have hker : D.p2.ker = Subgroup.zpowers D.gen := by
    ext x
    exact D.gen_spec x
  have hn0 : D.frame.n0 = Nat.card D.p2.ker := by
    rw [hker, Nat.card_zpowers, frame, Frame.ofGroup_order, addOrderOf_ofMul_eq_orderOf]
  have hs : D.p2.range = D.ξ.range := by
    ext b
    constructor
    · rintro ⟨⟨_, v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨D.eta v, v, rfl⟩, rfl⟩
  have hmul := Subgroup.card_mul_index D.p2.ker
  rw [Subgroup.index_ker, hs] at hmul
  unfold Frame.o
  rw [ord_eq, hn0, ← hmul]
  have hpos : 0 < Nat.card D.p2.ker := Nat.card_pos
  exact Nat.mul_div_cancel_left _ hpos

theorem twoGroup (h : ∃ j : ℕ, ∀ u, D.ξ u ^ 2 ^ j = 1) : D.frame.TwoGroup := by
  obtain ⟨j, hj⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : Nat.card (HGrp D.e) = 2 ^ D.e := (hostGroup D.e).2.2.2.2.2.2.1
  have hp : IsPGroup 2 D.R := by
    intro x
    refine ⟨D.e + j, ?_⟩
    obtain ⟨_, u, rfl⟩ := x
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    refine Prod.ext ?_ ?_
    · rw [Prod.pow_fst]
      show (D.cl u) ^ 2 ^ (D.e + j) = 1
      rw [show 2 ^ (D.e + j) = Nat.card (HGrp D.e) * 2 ^ j by rw [hH, pow_add], pow_mul,
        pow_card_eq_one', one_pow]
    · rw [Prod.pow_snd]
      show (D.ξ u) ^ 2 ^ (D.e + j) = 1
      rw [show 2 ^ (D.e + j) = 2 ^ j * 2 ^ D.e by rw [pow_add, mul_comm], pow_mul, hj, one_pow]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  exact ⟨k, by rw [ord_eq, hk]⟩

end ModData

end WindowedLandauTheory.HC
