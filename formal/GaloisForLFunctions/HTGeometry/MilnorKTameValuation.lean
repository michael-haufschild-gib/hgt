import GaloisForLFunctions.HTGeometry.MilnorKTameSymbol
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# The tame symbol data of an integer-valued valuation

An integer-valued valuation on a field determines the additive valuation on the units — the inverse
of the multiplicative value, so that uniformizers get positive integer valuation — and its kernel
is the group of units of valuation one, which are exactly the units of the valuation subring.

* `tameValHom` : **the additive valuation on the units.**
* `tameValHom_mem_ker_iff` : its kernel is the units of multiplicative valuation one.
* `tameValHom_pos_iff`, `tameValHom_neg_iff` : the sign of the valuation.
* `tameUnit` : **a unit of valuation zero as a unit of the valuation subring.**
-/

namespace GaloisForLFunctions.HTGeometry

open Valuation IsLocalRing

variable {K : Type*} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))

theorem tame_v_ne_zero (a : Kˣ) : v (a : K) ≠ 0 := (Valuation.ne_zero_iff v).2 a.ne_zero

/-- The multiplicative value of a unit, as an element of the value group. -/
noncomputable def tameUnzero (a : Kˣ) : Multiplicative ℤ :=
  WithZero.unzero (tame_v_ne_zero v a)

@[simp]
theorem coe_tameUnzero (a : Kˣ) : ((tameUnzero v a : Multiplicative ℤ) :
    WithZero (Multiplicative ℤ)) = v (a : K) :=
  WithZero.coe_unzero _

/-- **The additive valuation on the units**, normalized so that elements of the maximal ideal have
positive valuation. -/
noncomputable def tameValHom : Kˣ →* Multiplicative ℤ where
  toFun a := (tameUnzero v a)⁻¹
  map_one' := by
    refine inv_eq_one.2 (WithZero.coe_inj.1 ?_)
    rw [coe_tameUnzero]
    simp
  map_mul' a b := by
    have h : tameUnzero v (a * b) = tameUnzero v a * tameUnzero v b := by
      refine WithZero.coe_inj.1 ?_
      rw [coe_tameUnzero, WithZero.coe_mul, coe_tameUnzero, coe_tameUnzero]
      push_cast
      exact v.map_mul _ _
    show (tameUnzero v (a * b))⁻¹ = (tameUnzero v a)⁻¹ * (tameUnzero v b)⁻¹
    rw [h, mul_inv]

theorem tameValHom_eq (a : Kˣ) : tameValHom v a = (tameUnzero v a)⁻¹ := rfl

theorem tameValHom_toAdd (a : Kˣ) :
    Multiplicative.toAdd (tameValHom v a) = -Multiplicative.toAdd (tameUnzero v a) := rfl

/-- **The kernel of the additive valuation is the group of units of multiplicative value one.** -/
theorem tameValHom_mem_ker_iff (a : Kˣ) : a ∈ (tameValHom v).ker ↔ v (a : K) = 1 := by
  rw [MonoidHom.mem_ker, tameValHom_eq, inv_eq_one]
  constructor
  · intro h
    rw [← coe_tameUnzero v a, h]
    rfl
  · intro h
    refine WithZero.coe_inj.1 ?_
    rw [coe_tameUnzero, h]
    rfl

/-- **Positive valuation is the maximal ideal.** -/
theorem tameValHom_pos_iff (a : Kˣ) :
    0 < Multiplicative.toAdd (tameValHom v a) ↔ v (a : K) < 1 := by
  rw [tameValHom_toAdd, neg_pos]
  show Multiplicative.toAdd (tameUnzero v a) < 0 ↔ _
  constructor
  · intro h
    have hu : tameUnzero v a < 1 := h
    rw [← coe_tameUnzero]
    exact WithZero.coe_lt_one.2 hu
  · intro h
    rw [← coe_tameUnzero] at h
    exact WithZero.coe_lt_one.1 h

/-- **Negative valuation is the complement of the valuation subring.** -/
theorem tameValHom_neg_iff (a : Kˣ) :
    Multiplicative.toAdd (tameValHom v a) < 0 ↔ 1 < v (a : K) := by
  rw [tameValHom_toAdd, neg_neg_iff_pos]
  show 0 < Multiplicative.toAdd (tameUnzero v a) ↔ _
  constructor
  · intro h
    have hu : (1 : Multiplicative ℤ) < tameUnzero v a := h
    rw [← coe_tameUnzero]
    exact WithZero.one_lt_coe.2 hu
  · intro h
    rw [← coe_tameUnzero] at h
    exact WithZero.one_lt_coe.1 h

/-! ## Units of the valuation subring -/

theorem tame_mem_valuationSubring {a : Kˣ} (h : a ∈ (tameValHom v).ker) :
    (a : K) ∈ v.valuationSubring := by
  rw [Valuation.mem_valuationSubring_iff, (tameValHom_mem_ker_iff v a).1 h]

theorem tame_inv_mem_valuationSubring {a : Kˣ} (h : a ∈ (tameValHom v).ker) :
    ((a⁻¹ : Kˣ) : K) ∈ v.valuationSubring := by
  rw [Valuation.mem_valuationSubring_iff]
  have hval : v ((a⁻¹ : Kˣ) : K) = (v (a : K))⁻¹ := by
    rw [Units.val_inv_eq_inv_val, Valuation.map_inv]
  rw [hval, (tameValHom_mem_ker_iff v a).1 h, inv_one]

/-- **A unit of valuation zero, as a unit of the valuation subring.** -/
noncomputable def tameUnit {a : Kˣ} (h : a ∈ (tameValHom v).ker) : (v.valuationSubring)ˣ where
  val := ⟨(a : K), tame_mem_valuationSubring v h⟩
  inv := ⟨((a⁻¹ : Kˣ) : K), tame_inv_mem_valuationSubring v h⟩
  val_inv := by
    refine Subtype.ext ?_
    show (a : K) * ((a⁻¹ : Kˣ) : K) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  inv_val := by
    refine Subtype.ext ?_
    show ((a⁻¹ : Kˣ) : K) * (a : K) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

@[simp]
theorem tameUnit_val {a : Kˣ} (h : a ∈ (tameValHom v).ker) :
    ((tameUnit v h : (v.valuationSubring)ˣ) : v.valuationSubring)
      = ⟨(a : K), tame_mem_valuationSubring v h⟩ := rfl

/-- Every field unit of valuation zero is the image of a unit of the valuation subring.
This is the exact bridge from the valuation kernel to integral units, used when an integral
norm-surjectivity theorem is promoted to a statement about valuation-zero field units. -/
theorem tameValHom_ker_unitsMap_surjective (a : Kˣ) (h : a ∈ (tameValHom v).ker) :
    ∃ b : v.valuationSubringˣ, Units.map (algebraMap v.valuationSubring K) b = a := by
  refine ⟨tameUnit v h, ?_⟩
  apply Units.ext
  rfl

/-! ## The residue homomorphism -/

theorem tameUnit_one (h : (1 : Kˣ) ∈ (tameValHom v).ker) : tameUnit v h = 1 :=
  Units.ext (Subtype.ext rfl)

theorem tameUnit_mul {a b : Kˣ} (ha : a ∈ (tameValHom v).ker) (hb : b ∈ (tameValHom v).ker)
    (hab : a * b ∈ (tameValHom v).ker) :
    tameUnit v hab = tameUnit v ha * tameUnit v hb :=
  Units.ext (Subtype.ext rfl)

/-- **The residue homomorphism on the units of valuation zero.** -/
noncomputable def tameResHom :
    (tameValHom v).ker →* (ResidueField v.valuationSubring)ˣ where
  toFun a := Units.map (IsLocalRing.residue v.valuationSubring).toMonoidHom (tameUnit v a.2)
  map_one' := by
    show Units.map _ (tameUnit v (1 : (tameValHom v).ker).2) = 1
    rw [tameUnit_one, map_one]
  map_mul' a b := by
    show Units.map _ (tameUnit v (a * b).2) = _
    rw [tameUnit_mul v a.2 b.2, map_mul]

theorem tameResHom_val {a : Kˣ} (h : a ∈ (tameValHom v).ker) :
    ((tameResHom v ⟨a, h⟩ : (ResidueField v.valuationSubring)ˣ) :
      ResidueField v.valuationSubring)
      = IsLocalRing.residue _ ⟨(a : K), tame_mem_valuationSubring v h⟩ := rfl

/-- An element of the valuation subring of value less than one lies in the maximal ideal. -/
theorem tame_mem_maximalIdeal {x : K} (hx : x ∈ v.valuationSubring) (h : v x < 1) :
    (⟨x, hx⟩ : v.valuationSubring) ∈ maximalIdeal v.valuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  obtain ⟨u, hu⟩ := hunit
  have hxy : x * ((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) = 1 := by
    have hval := u.val_inv
    rw [hu] at hval
    exact congrArg Subtype.val hval
  have hval : v x * v ((u⁻¹ : (v.valuationSubring)ˣ) : K) = 1 := by
    rw [← v.map_mul]
    show v (x * ((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : K) = 1
    rw [hxy, v.map_one]
  have hle : v ((u⁻¹ : (v.valuationSubring)ˣ) : K) ≤ 1 :=
    (Valuation.mem_valuationSubring_iff v _).1 (u⁻¹ : (v.valuationSubring)ˣ).1.2
  have hge : (1 : WithZero (Multiplicative ℤ)) ≤ v x := by
    calc (1 : WithZero (Multiplicative ℤ))
        = v x * v ((u⁻¹ : (v.valuationSubring)ˣ) : K) := hval.symm
      _ ≤ v x * 1 := by gcongr
      _ = v x := mul_one _
  exact absurd h (not_lt.2 hge)

/-- The residue of an element of the maximal ideal vanishes. -/
theorem tame_residue_eq_zero {x : K} (hx : x ∈ v.valuationSubring) (h : v x < 1) :
    IsLocalRing.residue v.valuationSubring ⟨x, hx⟩ = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (tame_mem_maximalIdeal v hx h)

/-! ## The Steinberg clauses -/

theorem tameValHom_congr {a b : Kˣ} (h : v (a : K) = v (b : K)) :
    tameValHom v a = tameValHom v b := by
  have hu : tameUnzero v a = tameUnzero v b := by
    refine WithZero.coe_inj.1 ?_
    rw [coe_tameUnzero, coe_tameUnzero, h]
  rw [tameValHom_eq, tameValHom_eq, hu]

theorem tameResHom_neg_one (h : (-1 : Kˣ) ∈ (tameValHom v).ker) :
    tameResHom v ⟨-1, h⟩ = -1 := by
  refine Units.ext ?_
  rw [tameResHom_val,
    show (⟨(((-1 : Kˣ)) : K), tame_mem_valuationSubring v h⟩ : v.valuationSubring) = -1 from
      Subtype.ext rfl]
  simp

theorem tame_oneSub_of_pos {a : Kˣ} (ha : (a : K) ≠ 1)
    (hpos : 0 < Multiplicative.toAdd (tameValHom v a)) :
    ∃ h : oneSubUnit ha ∈ (tameValHom v).ker, tameResHom v ⟨oneSubUnit ha, h⟩ = 1 := by
  have hlt : v (a : K) < 1 := (tameValHom_pos_iff v a).1 hpos
  have hone : v (((oneSubUnit ha : Kˣ)) : K) = 1 := by
    rw [oneSubUnit_val]
    exact Valuation.map_one_sub_of_lt v hlt
  refine ⟨(tameValHom_mem_ker_iff v _).2 hone, ?_⟩
  have hamem : (a : K) ∈ v.valuationSubring := (Valuation.mem_valuationSubring_iff v _).2 hlt.le
  refine Units.ext ?_
  rw [tameResHom_val,
    show (⟨(((oneSubUnit ha : Kˣ)) : K),
        tame_mem_valuationSubring v ((tameValHom_mem_ker_iff v _).2 hone)⟩ : v.valuationSubring)
      = 1 - ⟨(a : K), hamem⟩ from Subtype.ext (oneSubUnit_val ha),
    _root_.map_sub, _root_.map_one, tame_residue_eq_zero v hamem hlt, sub_zero]
  rfl

theorem tame_oneSub_of_zero {a : Kˣ} (ha : (a : K) ≠ 1) (h : a ∈ (tameValHom v).ker) :
    0 ≤ Multiplicative.toAdd (tameValHom v (oneSubUnit ha)) ∧
      (0 < Multiplicative.toAdd (tameValHom v (oneSubUnit ha)) → tameResHom v ⟨a, h⟩ = 1) := by
  have hva : v (a : K) = 1 := (tameValHom_mem_ker_iff v a).1 h
  have hle : v (((oneSubUnit ha : Kˣ)) : K) ≤ 1 := by
    rw [oneSubUnit_val]
    refine le_trans (Valuation.map_sub v 1 (a : K)) ?_
    rw [v.map_one, hva, max_self]
  refine ⟨?_, ?_⟩
  · rw [← not_lt]
    intro hneg
    exact absurd hle (not_le.2 ((tameValHom_neg_iff v _).1 hneg))
  · intro hpos
    have hlt : v (((oneSubUnit ha : Kˣ)) : K) < 1 := (tameValHom_pos_iff v _).1 hpos
    have hmem : (((oneSubUnit ha : Kˣ)) : K) ∈ v.valuationSubring :=
      (Valuation.mem_valuationSubring_iff v _).2 hlt.le
    refine Units.ext ?_
    rw [tameResHom_val,
      show (⟨(a : K), tame_mem_valuationSubring v h⟩ : v.valuationSubring)
        = 1 - ⟨(((oneSubUnit ha : Kˣ)) : K), hmem⟩ from Subtype.ext (by
          show (a : K) = 1 - (((oneSubUnit ha : Kˣ)) : K)
          rw [oneSubUnit_val]
          ring),
      _root_.map_sub, _root_.map_one, tame_residue_eq_zero v hmem hlt, sub_zero]
    rfl

theorem tame_oneSub_of_neg {a : Kˣ} (ha : (a : K) ≠ 1)
    (hneg : Multiplicative.toAdd (tameValHom v a) < 0) :
    Multiplicative.toAdd (tameValHom v (oneSubUnit ha)) = Multiplicative.toAdd (tameValHom v a) ∧
      ∃ h : a * (oneSubUnit ha)⁻¹ ∈ (tameValHom v).ker,
        tameResHom v ⟨a * (oneSubUnit ha)⁻¹, h⟩ = -1 := by
  have hgt : 1 < v (a : K) := (tameValHom_neg_iff v a).1 hneg
  have hv1a : v (((oneSubUnit ha : Kˣ)) : K) = v (a : K) := by
    rw [oneSubUnit_val]
    have hne : v (1 : K) ≠ v (-(a : K)) := by
      rw [v.map_one, Valuation.map_neg]
      exact ne_of_lt hgt
    have hadd := Valuation.map_add_of_distinct_val v hne
    rw [show (1 : K) + -(a : K) = 1 - (a : K) from by ring, v.map_one, Valuation.map_neg] at hadd
    rw [hadd, max_eq_right hgt.le]
  refine ⟨congrArg Multiplicative.toAdd (tameValHom_congr v hv1a), ?_⟩
  have hw : v (((a * (oneSubUnit ha)⁻¹ : Kˣ)) : K) = 1 := by
    rw [Units.val_mul, v.map_mul, Units.val_inv_eq_inv_val, Valuation.map_inv, hv1a,
      mul_inv_cancel₀ (tame_v_ne_zero v a)]
  refine ⟨(tameValHom_mem_ker_iff v _).2 hw, ?_⟩
  have hsum : (((a * (oneSubUnit ha)⁻¹ : Kˣ)) : K) + 1 = (((oneSubUnit ha : Kˣ)) : K)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, oneSubUnit_val]
    have hne : (1 : K) - (a : K) ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
    field_simp
    ring
  have hsumlt : v ((((a * (oneSubUnit ha)⁻¹ : Kˣ)) : K) + 1) < 1 := by
    rw [hsum, Valuation.map_inv, hv1a]
    have hinv := (Valuation.one_lt_val_iff v a.ne_zero).1 hgt
    rwa [Valuation.map_inv] at hinv
  have hmemsum : ((((a * (oneSubUnit ha)⁻¹ : Kˣ)) : K) + 1) ∈ v.valuationSubring :=
    (Valuation.mem_valuationSubring_iff v _).2 hsumlt.le
  have hkey : IsLocalRing.residue v.valuationSubring
      ⟨(((a * (oneSubUnit ha)⁻¹ : Kˣ)) : K) + 1, hmemsum⟩ = 0 :=
    tame_residue_eq_zero v hmemsum hsumlt
  rw [show (⟨(((a * (oneSubUnit ha)⁻¹ : Kˣ)) : K) + 1, hmemsum⟩ : v.valuationSubring)
      = ⟨(((a * (oneSubUnit ha)⁻¹ : Kˣ)) : K),
          tame_mem_valuationSubring v ((tameValHom_mem_ker_iff v _).2 hw)⟩ + 1 from
      Subtype.ext rfl, _root_.map_add, _root_.map_one] at hkey
  refine Units.ext ?_
  rw [tameResHom_val]
  have hres := eq_neg_of_add_eq_zero_left hkey
  rw [hres]
  rfl

/-- **The tame symbol data of an integer-valued valuation.** -/
noncomputable def tameDataOfValuation :
    TameData K (ResidueField v.valuationSubring) where
  val := tameValHom v
  res := tameResHom v
  res_neg_one := tameResHom_neg_one v
  oneSub_of_pos ha h := tame_oneSub_of_pos v ha h
  oneSub_of_zero ha h := tame_oneSub_of_zero v ha h
  oneSub_of_neg ha h := tame_oneSub_of_neg v ha h

/-- **The tame symbol of an integer-valued valuation, as a homomorphism out of `K_2^M(K)`.** -/
noncomputable def tameHomOfValuation :
    MilnorKDeg K 2 →+ Additive (ResidueField v.valuationSubring)ˣ :=
  (tameDataOfValuation v).tameHom

theorem tameHomOfValuation_symbol (a b : Kˣ) :
    tameHomOfValuation v (milnorClassDeg K 2 ⟨[a, b], rfl⟩)
      = Additive.ofMul ((tameDataOfValuation v).tame a b) :=
  (tameDataOfValuation v).tameHom_symbol a b

end GaloisForLFunctions.HTGeometry
