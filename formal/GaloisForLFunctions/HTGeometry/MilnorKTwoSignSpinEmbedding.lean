import GaloisForLFunctions.HTGeometry.MilnorKTwoCharacteristicGate
import GaloisForLFunctions.HTGeometry.MilnorKTwoSpinWeyl
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# Faithful Spin embedding of Milnor's common sign subgroup

When `{-1,-1}` is nonzero, it has exact additive order two and the classified subgroup `H₀`
has field-independent binary coordinates. This file identifies its multiplication with the
lower-triangular three-bit cocycle, realizes those coordinates by ordered Clifford bivectors,
and proves the resulting homomorphism into the rotor-generated Spin Weyl subgroup is injective.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace MilnorDiagonalExtension

variable {F : Type*} [Field F]

private theorem zmodTwo_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem fin4MinusOneSymbol_addOrderOf
    (he : fin4MinusOneSymbol F ≠ 0) :
    addOrderOf (fin4MinusOneSymbol F) = 2 := by
  rw [addOrderOf_eq_iff (by norm_num : 0 < 2)]
  constructor
  · change fin4MinusOneSymbol F + fin4MinusOneSymbol F = 0
    exact milnorSym2_self_add_self (F := F) (-1 : Fˣ)
  · intro m hm hpos
    interval_cases m
    simpa using he

def fin4MinusOneCenterEquiv
    (he : fin4MinusOneSymbol F ≠ 0) :
    ZMod 2 ≃+ AddSubgroup.zmultiples (fin4MinusOneSymbol F) :=
  zmodAddEquivOfGenerator
    (g := ⟨fin4MinusOneSymbol F, fin4MinusOneSymbol_mem_zmultiples (F := F)⟩)
    (by
      intro x
      obtain ⟨m, hm⟩ := x.property
      refine ⟨m, ?_⟩
      apply Subtype.ext
      simpa using hm)
    (by simp [fin4MinusOneSymbol_addOrderOf he])

@[simp] theorem fin4MinusOneCenterEquiv_apply_intCast
    (he : fin4MinusOneSymbol F ≠ 0) (m : ℤ) :
    fin4MinusOneCenterEquiv he (m : ZMod 2) =
      ⟨m • fin4MinusOneSymbol F, by
        rw [AddSubgroup.mem_zmultiples_iff]
        exact ⟨m, rfl⟩⟩ := by
  apply Subtype.ext
  change ((fin4MinusOneCenterEquiv he) (m : ZMod 2)).1 =
    m • fin4MinusOneSymbol F
  rw [fin4MinusOneCenterEquiv, zmodAddEquivOfGenerator_apply_intCast]
  rfl

def signUnit (a : ZMod 2) : Fˣ :=
  if a = 0 then 1 else -1

@[simp] theorem signUnit_zero : signUnit (F := F) 0 = 1 := by simp [signUnit]

@[simp] theorem signUnit_one : signUnit (F := F) 1 = -1 := by
  simp [signUnit]

theorem signUnit_add (a b : ZMod 2) :
    signUnit (F := F) (a + b) = signUnit a * signUnit b := by
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl <;>
    rcases zmodTwo_eq_zero_or_one b with rfl | rfl
  · simp
  · simp
  · simp
  · have hz : (1 + 1 : ZMod 2) = 0 := by decide
    rw [hz]
    simp

theorem signUnit_eq_one_or_neg_one (a : ZMod 2) :
    signUnit (F := F) a = 1 ∨ signUnit a = (-1 : Fˣ) := by
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl
  · exact Or.inl signUnit_zero
  · exact Or.inr signUnit_one

theorem signUnit_injective (hminus : (-1 : Fˣ) ≠ 1) :
    Function.Injective (signUnit (F := F)) := by
  intro a b hab
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl <;>
    rcases zmodTwo_eq_zero_or_one b with rfl | rfl
  · rfl
  · exact False.elim (hminus (by simpa using hab.symm))
  · exact False.elim (hminus (by simpa using hab))
  · rfl

noncomputable def signBit (u : Fˣ) : ZMod 2 := by
  classical
  exact if u = 1 then 0 else 1

theorem signUnit_signBit {u : Fˣ} (hu : u = 1 ∨ u = -1) :
    signUnit (F := F) (signBit u) = u := by
  classical
  rcases hu with rfl | rfl
  · simp [signBit]
  · by_cases h : (-1 : Fˣ) = 1
    · simp [h, signBit]
    · simp [h, signBit]

theorem signBit_signUnit (hminus : (-1 : Fˣ) ≠ 1) (a : ZMod 2) :
    signBit (signUnit (F := F) a) = a := by
  apply signUnit_injective hminus
  rw [signUnit_signBit (signUnit_eq_one_or_neg_one a)]

end MilnorDiagonalExtension

namespace MilnorH0Coordinates

/-- Lower-triangular parity cocycle on three binary diagonal coordinates. -/
def triangularCocycle (a b : Fin 3 → ZMod 2) : ZMod 2 :=
  ∑ i : Fin 3, ∑ j : Fin 3, if j ≤ i then a i * b j else 0

@[simp] theorem triangularCocycle_zero_left (b : Fin 3 → ZMod 2) :
    triangularCocycle 0 b = 0 := by
  simp [triangularCocycle]

@[simp] theorem triangularCocycle_zero_right (a : Fin 3 → ZMod 2) :
    triangularCocycle a 0 = 0 := by
  simp [triangularCocycle]

theorem triangularCocycle_add_left (a b c : Fin 3 → ZMod 2) :
    triangularCocycle (a + b) c =
      triangularCocycle a c + triangularCocycle b c := by
  simp only [triangularCocycle, Pi.add_apply, add_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j ≤ i <;> simp [hji]

theorem triangularCocycle_add_right (a b c : Fin 3 → ZMod 2) :
    triangularCocycle a (b + c) =
      triangularCocycle a b + triangularCocycle a c := by
  simp only [triangularCocycle, Pi.add_apply, mul_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j ≤ i <;> simp [hji]

theorem triangularCocycle_cocycle (a b c : Fin 3 → ZMod 2) :
    triangularCocycle (a + b) c + triangularCocycle a b =
      triangularCocycle a (b + c) + triangularCocycle b c := by
  rw [triangularCocycle_add_left, triangularCocycle_add_right]
  abel

@[ext]
structure Coordinates where
  diag : Fin 3 → ZMod 2
  central : ZMod 2

instance : Mul Coordinates where
  mul x y := ⟨x.diag + y.diag,
    x.central + y.central + triangularCocycle x.diag y.diag⟩

instance : One Coordinates where
  one := ⟨0, 0⟩

instance : Inv Coordinates where
  inv x := ⟨-x.diag,
    -x.central - triangularCocycle (-x.diag) x.diag⟩

@[simp] theorem diag_mul (x y : Coordinates) : (x * y).diag = x.diag + y.diag := rfl
@[simp] theorem central_mul (x y : Coordinates) :
    (x * y).central = x.central + y.central + triangularCocycle x.diag y.diag := rfl
@[simp] theorem diag_one : (1 : Coordinates).diag = 0 := rfl
@[simp] theorem central_one : (1 : Coordinates).central = 0 := rfl
@[simp] theorem diag_inv (x : Coordinates) : x⁻¹.diag = -x.diag := rfl
@[simp] theorem central_inv (x : Coordinates) :
    x⁻¹.central = -x.central - triangularCocycle (-x.diag) x.diag := rfl

instance : Group Coordinates where
  mul_assoc x y z := by
    ext
    · simp [add_assoc]
    · simp only [central_mul, diag_mul]
      have hc := triangularCocycle_cocycle x.diag y.diag z.diag
      calc
        x.central + y.central + triangularCocycle x.diag y.diag + z.central
              + triangularCocycle (x.diag + y.diag) z.diag
            = x.central + y.central + z.central
              + (triangularCocycle (x.diag + y.diag) z.diag
                + triangularCocycle x.diag y.diag) := by abel
        _ = x.central + y.central + z.central
              + (triangularCocycle x.diag (y.diag + z.diag)
                + triangularCocycle y.diag z.diag) := by rw [hc]
        _ = x.central + (y.central + z.central + triangularCocycle y.diag z.diag)
              + triangularCocycle x.diag (y.diag + z.diag) := by abel
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by
    ext
    · exact neg_add_cancel _
    · simp only [central_mul, central_inv, diag_inv]
      abel

end MilnorH0Coordinates

namespace MilnorDiagonalExtension

open MilnorH0Coordinates

variable {F : Type*} [Field F]

theorem milnorSym2_signUnit_eq_center
    (he : fin4MinusOneSymbol F ≠ 0) (a b : ZMod 2) :
    milnorSym2 F (signUnit a) (signUnit b) =
      (fin4MinusOneCenterEquiv he (a * b)).1 := by
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl <;>
    rcases zmodTwo_eq_zero_or_one b with rfl | rfl
  · simp [milnorSym2_one_left]
  · simp [milnorSym2_one_left]
  · simp [milnorSym2_one_right]
  · change fin4MinusOneSymbol F = _
    rw [show (1 : ZMod 2) * 1 = (1 : ZMod 2) by simp]
    simpa using (congrArg Subtype.val
      (fin4MinusOneCenterEquiv_apply_intCast he 1)
      ).symm

def fullSignBits (u : detOneDiagonalUnits F 4) : Fin 4 → ZMod 2 :=
  fun i => signBit (u.1 i)

def fullTriangularCocycle (a b : Fin 4 → ZMod 2) : ZMod 2 :=
  ∑ i : Fin 4, ∑ j : Fin 4, if j ≤ i then a i * b j else 0

theorem fin4MinusOneCenterEquiv_fullTriangularCocycle
    (he : fin4MinusOneSymbol F ≠ 0)
    (u v : detOneDiagonalUnits F 4)
    (hu : ∀ i, u.1 i = 1 ∨ u.1 i = -1)
    (hv : ∀ i, v.1 i = 1 ∨ v.1 i = -1) :
    (fin4MinusOneCenterEquiv he
      (fullTriangularCocycle (fullSignBits u) (fullSignBits v))).1 =
      milnorDiagonalCocycle u v := by
  rw [show fullTriangularCocycle (fullSignBits u) (fullSignBits v) =
      ∑ i : Fin 4, ∑ j : Fin 4,
        if j ≤ i then fullSignBits u i * fullSignBits v j else 0 by rfl]
  rw [map_sum]
  unfold milnorDiagonalCocycle
  change (∑ i : Fin 4,
      (fin4MinusOneCenterEquiv he
        (∑ j : Fin 4, if j ≤ i then fullSignBits u i * fullSignBits v j else 0)).1) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  change (∑ j : Fin 4,
      (fin4MinusOneCenterEquiv he
        (if j ≤ i then fullSignBits u i * fullSignBits v j else 0)).1) = _
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j ≤ i
  · simp only [hji, ↓reduceIte]
    rw [← milnorSym2_signUnit_eq_center he]
    exact congrArg₂ (milnorSym2 F)
      (signUnit_signBit (hu i)) (signUnit_signBit (hv j))
  · simp [hji]

theorem fullSignBits_sum_eq_zero
    (he : fin4MinusOneSymbol F ≠ 0)
    (u : detOneDiagonalUnits F 4)
    (hu : ∀ i, u.1 i = 1 ∨ u.1 i = -1) :
    ∑ i : Fin 4, fullSignBits u i = 0 := by
  letI : CharZero F := charZero_of_fin4MinusOneSymbol_ne_zero he
  have hminus : (-1 : Fˣ) ≠ 1 := by
    intro h
    have hv : (-1 : F) = 1 := congrArg Units.val h
    norm_num at hv
  apply signUnit_injective hminus
  rw [show signUnit (F := F) (∑ i : Fin 4, fullSignBits u i) =
      ∏ i : Fin 4, signUnit (fullSignBits u i) by
    rw [Fin.sum_univ_four, Fin.prod_univ_four]
    simp only [signUnit_add]
    ]
  simp_rw [fullSignBits, signUnit_signBit (hu _)]
  rw [u.property]
  exact signUnit_zero.symm

theorem fullTriangularCocycle_eq_triangularCocycle
    (a b : Fin 4 → ZMod 2)
    (hb : ∑ i : Fin 4, b i = 0) :
    fullTriangularCocycle a b =
      triangularCocycle (fun i : Fin 3 => a i.castSucc)
        (fun i : Fin 3 => b i.castSucc) := by
  simp [fullTriangularCocycle, triangularCocycle,
    Fin.sum_univ_four, Fin.sum_univ_three] at hb ⊢
  ring_nf at hb ⊢
  linear_combination (a 3) * hb

theorem fin4MinusOneCenterEquiv_signCocycle
    (he : fin4MinusOneSymbol F ≠ 0)
    (u v : detOneDiagonalUnits F 4)
    (hu : ∀ i, u.1 i = 1 ∨ u.1 i = -1)
    (hv : ∀ i, v.1 i = 1 ∨ v.1 i = -1) :
    (fin4MinusOneCenterEquiv he
      (triangularCocycle
        (fun i : Fin 3 => fullSignBits u i.castSucc)
        (fun i : Fin 3 => fullSignBits v i.castSucc))).1 =
      milnorDiagonalCocycle u v := by
  rw [← fullTriangularCocycle_eq_triangularCocycle
    (fullSignBits u) (fullSignBits v)
    (fullSignBits_sum_eq_zero he v hv)]
  exact fin4MinusOneCenterEquiv_fullTriangularCocycle he u v hu hv

theorem fin4MilnorH0_signs
    (x : fin4MilnorH0 (F := F)) :
    ∀ i, x.1.diag.1 i = 1 ∨ x.1.diag.1 i = -1 := by
  have hx : x.1 ∈ fin4MilnorSignSubgroup (F := F) := by
    rw [← fin4MilnorH0_eq_signSubgroup]
    exact x.property
  exact hx.1

theorem fin4MilnorH0_center_mem
    (x : fin4MilnorH0 (F := F)) :
    x.1.central ∈ AddSubgroup.zmultiples (fin4MinusOneSymbol F) := by
  have hx : x.1 ∈ fin4MilnorSignSubgroup (F := F) := by
    rw [← fin4MilnorH0_eq_signSubgroup]
    exact x.property
  exact hx.2

def fin4MilnorH0Bits (x : fin4MilnorH0 (F := F)) : Fin 3 → ZMod 2 :=
  fun i => fullSignBits x.1.diag i.castSucc

def fin4MilnorH0CentralParity
    (he : fin4MinusOneSymbol F ≠ 0)
    (x : fin4MilnorH0 (F := F)) : ZMod 2 :=
  (fin4MinusOneCenterEquiv he).symm
    ⟨x.1.central, fin4MilnorH0_center_mem x⟩

@[simp] theorem fin4MinusOneCenterEquiv_h0CentralParity
    (he : fin4MinusOneSymbol F ≠ 0)
    (x : fin4MilnorH0 (F := F)) :
    fin4MinusOneCenterEquiv he (fin4MilnorH0CentralParity he x) =
      ⟨x.1.central, fin4MilnorH0_center_mem x⟩ := by
  exact (fin4MinusOneCenterEquiv he).apply_symm_apply _

def fin4MilnorH0ToCoordinates
    (he : fin4MinusOneSymbol F ≠ 0) :
    fin4MilnorH0 (F := F) →* MilnorH0Coordinates.Coordinates where
  toFun x := ⟨fin4MilnorH0Bits x, fin4MilnorH0CentralParity he x⟩
  map_one' := by
    ext i
    · simp [fin4MilnorH0Bits, fullSignBits, signBit]
    · apply (fin4MinusOneCenterEquiv he).injective
      apply Subtype.ext
      simp
  map_mul' x y := by
    letI : CharZero F := charZero_of_fin4MinusOneSymbol_ne_zero he
    have hminus : (-1 : Fˣ) ≠ 1 := by
      intro h
      have hv : (-1 : F) = 1 := congrArg Units.val h
      norm_num at hv
    ext i
    · change signBit ((x.1 * y.1).diag.1 i.castSucc) =
        signBit (x.1.diag.1 i.castSucc) + signBit (y.1.diag.1 i.castSucc)
      apply signUnit_injective hminus
      rw [signUnit_add,
        signUnit_signBit (fin4MilnorH0_signs x i.castSucc),
        signUnit_signBit (fin4MilnorH0_signs y i.castSucc)]
      rw [signUnit_signBit
        (show (x.1 * y.1).diag.1 i.castSucc = 1 ∨
            (x.1 * y.1).diag.1 i.castSucc = -1 from
          fin4MilnorH0_signs (x * y) i.castSucc)]
      rfl
    · change fin4MilnorH0CentralParity he (x * y) =
        fin4MilnorH0CentralParity he x + fin4MilnorH0CentralParity he y +
          MilnorH0Coordinates.triangularCocycle
            (fin4MilnorH0Bits x) (fin4MilnorH0Bits y)
      apply (fin4MinusOneCenterEquiv he).injective
      apply Subtype.ext
      simp only [map_add, fin4MinusOneCenterEquiv_h0CentralParity,
        AddSubgroup.coe_add]
      change (x.1 * y.1).central = x.1.central + y.1.central + _
      rw [central_mul]
      congr 1
      exact (fin4MinusOneCenterEquiv_signCocycle he x.1.diag y.1.diag
        (fin4MilnorH0_signs x) (fin4MilnorH0_signs y)).symm

theorem detOneDiagonalUnits_fin4_ext
    {u v : detOneDiagonalUnits F 4}
    (h0 : u.1 0 = v.1 0) (h1 : u.1 1 = v.1 1) (h2 : u.1 2 = v.1 2) :
    u = v := by
  apply Subtype.ext
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · have hu : u.1 0 * u.1 1 * u.1 2 * u.1 3 = 1 := by
      have h := u.property
      change (∏ i : Fin 4, u.1 i) = 1 at h
      rw [Fin.prod_univ_four] at h
      exact h
    have hv : v.1 0 * v.1 1 * v.1 2 * v.1 3 = 1 := by
      have h := v.property
      change (∏ i : Fin 4, v.1 i) = 1 at h
      rw [Fin.prod_univ_four] at h
      exact h
    rw [h0, h1, h2] at hu
    exact mul_left_cancel (hu.trans hv.symm)

theorem fin4MilnorH0ToCoordinates_injective
    (he : fin4MinusOneSymbol F ≠ 0) :
    Function.Injective (fin4MilnorH0ToCoordinates he) := by
  letI : CharZero F := charZero_of_fin4MinusOneSymbol_ne_zero he
  have hminus : (-1 : Fˣ) ≠ 1 := by
    intro h
    have hv : (-1 : F) = 1 := congrArg Units.val h
    norm_num at hv
  intro x y hxy
  apply Subtype.ext
  apply MilnorDiagonalExtension.ext
  · apply detOneDiagonalUnits_fin4_ext
    · have hb := congrArg (fun z : MilnorH0Coordinates.Coordinates => z.diag 0) hxy
      change signBit (x.1.diag.1 0) = signBit (y.1.diag.1 0) at hb
      calc
        x.1.diag.1 0 = signUnit (signBit (x.1.diag.1 0)) :=
          (signUnit_signBit (fin4MilnorH0_signs x 0)).symm
        _ = signUnit (signBit (y.1.diag.1 0)) := congrArg signUnit hb
        _ = y.1.diag.1 0 := signUnit_signBit (fin4MilnorH0_signs y 0)
    · have hb := congrArg (fun z : MilnorH0Coordinates.Coordinates => z.diag 1) hxy
      change signBit (x.1.diag.1 1) = signBit (y.1.diag.1 1) at hb
      calc
        x.1.diag.1 1 = signUnit (signBit (x.1.diag.1 1)) :=
          (signUnit_signBit (fin4MilnorH0_signs x 1)).symm
        _ = signUnit (signBit (y.1.diag.1 1)) := congrArg signUnit hb
        _ = y.1.diag.1 1 := signUnit_signBit (fin4MilnorH0_signs y 1)
    · have hb := congrArg (fun z : MilnorH0Coordinates.Coordinates => z.diag 2) hxy
      change signBit (x.1.diag.1 2) = signBit (y.1.diag.1 2) at hb
      calc
        x.1.diag.1 2 = signUnit (signBit (x.1.diag.1 2)) :=
          (signUnit_signBit (fin4MilnorH0_signs x 2)).symm
        _ = signUnit (signBit (y.1.diag.1 2)) := congrArg signUnit hb
        _ = y.1.diag.1 2 := signUnit_signBit (fin4MilnorH0_signs y 2)
  · have hc := congrArg
      (fun z : MilnorH0Coordinates.Coordinates => z.central) hxy
    change fin4MilnorH0CentralParity he x = fin4MilnorH0CentralParity he y at hc
    have hm := congrArg (fin4MinusOneCenterEquiv he) hc
    simpa using congrArg Subtype.val hm

def coordinatesDiagonal (a : Fin 3 → ZMod 2) : detOneDiagonalUnits F 4 :=
  ⟨![signUnit (a 0), signUnit (a 1), signUnit (a 2),
      signUnit (a 0 + a 1 + a 2)], by
    change ∏ i : Fin 4,
      (![signUnit (a 0), signUnit (a 1), signUnit (a 2),
        signUnit (a 0 + a 1 + a 2)] : Fin 4 → Fˣ) i = 1
    rw [Fin.prod_univ_four]
    change signUnit (a 0) * signUnit (a 1) * signUnit (a 2) *
      signUnit (a 0 + a 1 + a 2) = 1
    rw [← signUnit_add (a 0) (a 1),
      ← signUnit_add (a 0 + a 1) (a 2),
      ← signUnit_add (a 0 + a 1 + a 2) (a 0 + a 1 + a 2)]
    have hz : a 0 + a 1 + a 2 + (a 0 + a 1 + a 2) = 0 := by
      calc
        a 0 + a 1 + a 2 + (a 0 + a 1 + a 2) =
            2 * (a 0 + a 1 + a 2) := by ring
        _ = 0 := by
          have htwo : (2 : ZMod 2) = 0 := by decide
          rw [htwo, zero_mul]
    rw [hz]
    exact signUnit_zero⟩

@[simp] theorem coordinatesDiagonal_apply_zero (a : Fin 3 → ZMod 2) :
    (coordinatesDiagonal (F := F) a).1 0 = signUnit (a 0) := rfl
@[simp] theorem coordinatesDiagonal_apply_one (a : Fin 3 → ZMod 2) :
    (coordinatesDiagonal (F := F) a).1 1 = signUnit (a 1) := rfl
@[simp] theorem coordinatesDiagonal_apply_two (a : Fin 3 → ZMod 2) :
    (coordinatesDiagonal (F := F) a).1 2 = signUnit (a 2) := rfl

theorem fin4MilnorH0ToCoordinates_surjective
    (he : fin4MinusOneSymbol F ≠ 0) :
    Function.Surjective (fin4MilnorH0ToCoordinates he) := by
  letI : CharZero F := charZero_of_fin4MinusOneSymbol_ne_zero he
  have hminus : (-1 : Fˣ) ≠ 1 := by
    intro h
    have hv : (-1 : F) = 1 := congrArg Units.val h
    norm_num at hv
  intro c
  let raw : MilnorDiagonalExtension F 4 :=
    ⟨coordinatesDiagonal c.diag,
      (fin4MinusOneCenterEquiv he c.central).1⟩
  have hrawSign : raw ∈ fin4MilnorSignSubgroup (F := F) := by
    constructor
    · intro i
      fin_cases i <;> apply signUnit_eq_one_or_neg_one
    · exact (fin4MinusOneCenterEquiv he c.central).property
  have hrawH0 : raw ∈ fin4MilnorH0 (F := F) := by
    rw [fin4MilnorH0_eq_signSubgroup]
    exact hrawSign
  refine ⟨⟨raw, hrawH0⟩, ?_⟩
  apply MilnorH0Coordinates.Coordinates.ext
  · funext i
    fin_cases i <;>
      simp [fin4MilnorH0ToCoordinates, fin4MilnorH0Bits, fullSignBits,
        raw, signBit_signUnit hminus]
  · change (fin4MinusOneCenterEquiv he).symm
      ⟨(fin4MinusOneCenterEquiv he c.central).1, _⟩ = c.central
    exact (fin4MinusOneCenterEquiv he).symm_apply_apply c.central

def fin4MilnorH0EquivCoordinates
    (he : fin4MinusOneSymbol F ≠ 0) :
    fin4MilnorH0 (F := F) ≃* MilnorH0Coordinates.Coordinates :=
  MulEquiv.ofBijective (fin4MilnorH0ToCoordinates he)
    ⟨fin4MilnorH0ToCoordinates_injective he,
      fin4MilnorH0ToCoordinates_surjective he⟩

end MilnorDiagonalExtension

namespace MilnorSpinWeyl

open MilnorH0Coordinates

private theorem zmodTwo_eq_zero_or_one' (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp] private theorem zmodTwo_one_add_one : (1 + 1 : ZMod 2) = 0 := by
  decide

/-- Bivector lift corresponding to the canonical sign diagonal `h_{i,3}(-1)`. -/
def h0Generator (i : Fin 3) : spinGroup spinQ :=
  (weylLift i.castSucc 3 (Fin.castSucc_ne_last i))⁻¹ ^ 2

@[simp] theorem h0Generator_val (i : Fin 3) :
    ((h0Generator i : spinGroup spinQ) : Clifford) = bivector i.castSucc 3 := by
  simpa [h0Generator] using
    weylLift_inv_sq_val i.castSucc 3 (Fin.castSucc_ne_last i)

theorem bivector_same_terminal_anti (i j : Fin 3) (hij : i ≠ j) :
    bivector j.castSucc 3 * bivector i.castSucc 3 =
      -(bivector i.castSucc 3 * bivector j.castSucc 3) := by
  calc
    bivector j.castSucc 3 * bivector i.castSucc 3 =
        basisClifford j.castSucc *
          (basisClifford 3 * basisClifford i.castSucc) * basisClifford 3 := by
      simp [bivector, mul_assoc]
    _ = basisClifford j.castSucc *
          (-(basisClifford i.castSucc * basisClifford 3)) * basisClifford 3 := by
      rw [basisClifford_anti 3 i.castSucc (Ne.symm (Fin.castSucc_ne_last i))]
    _ = basisClifford j.castSucc * basisClifford i.castSucc := by
      rw [show basisClifford j.castSucc *
          (-(basisClifford i.castSucc * basisClifford 3)) * basisClifford 3 =
          -(basisClifford j.castSucc * basisClifford i.castSucc) *
            (basisClifford 3 * basisClifford 3) by noncomm_ring,
        basisClifford_sq]
      simp
    _ = -(basisClifford i.castSucc * basisClifford j.castSucc) :=
      basisClifford_anti j.castSucc i.castSucc (by simpa using Ne.symm hij)
    _ = -(bivector i.castSucc 3 * bivector j.castSucc 3) := by
      rw [show bivector i.castSucc 3 * bivector j.castSucc 3 =
          basisClifford i.castSucc * basisClifford j.castSucc by
        calc
          bivector i.castSucc 3 * bivector j.castSucc 3 =
              basisClifford i.castSucc *
                (basisClifford 3 * basisClifford j.castSucc) * basisClifford 3 := by
            simp [bivector, mul_assoc]
          _ = basisClifford i.castSucc *
                (-(basisClifford j.castSucc * basisClifford 3)) * basisClifford 3 := by
            rw [basisClifford_anti 3 j.castSucc (Ne.symm (Fin.castSucc_ne_last j))]
          _ = basisClifford i.castSucc * basisClifford j.castSucc := by
            rw [show basisClifford i.castSucc *
                (-(basisClifford j.castSucc * basisClifford 3)) * basisClifford 3 =
                -(basisClifford i.castSucc * basisClifford j.castSucc) *
                  (basisClifford 3 * basisClifford 3) by noncomm_ring,
              basisClifford_sq]
            simp]

@[simp] theorem h0Generator_sq (i : Fin 3) :
  h0Generator i * h0Generator i = centralNegOne := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul]
  rw [h0Generator_val, centralNegOne_val]
  change bivector i.castSucc 3 * bivector i.castSucc 3 = (-1 : Clifford)
  exact bivector_sq i.castSucc 3 (Fin.castSucc_ne_last i)

theorem h0Generator_reverse_order (i j : Fin 3) (hij : i ≠ j) :
    h0Generator j * h0Generator i =
      centralNegOne * (h0Generator i * h0Generator j) := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul]
  rw [h0Generator_val, h0Generator_val, centralNegOne_val]
  change bivector j.castSucc 3 * bivector i.castSucc 3 =
    (-1 : Clifford) * (bivector i.castSucc 3 * bivector j.castSucc 3)
  rw [bivector_same_terminal_anti i j hij]
  simp

@[simp] theorem centralNegOne_sq : centralNegOne * centralNegOne = 1 := by
  apply Subtype.ext
  simp

theorem centralNegOne_comm (x : spinGroup spinQ) :
    centralNegOne * x = x * centralNegOne := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul]
  rw [centralNegOne_val]
  change (-1 : Clifford) * (x : Clifford) = (x : Clifford) * (-1 : Clifford)
  simp

abbrev h0GeneratorZero : spinGroup spinQ := h0Generator 0
abbrev h0GeneratorOne : spinGroup spinQ := h0Generator 1
abbrev h0GeneratorTwo : spinGroup spinQ := h0Generator 2

theorem h0GeneratorOne_zero :
    h0GeneratorOne * h0GeneratorZero =
      centralNegOne * (h0GeneratorZero * h0GeneratorOne) :=
  h0Generator_reverse_order 0 1 (by decide)

theorem h0GeneratorTwo_zero :
    h0GeneratorTwo * h0GeneratorZero =
      centralNegOne * (h0GeneratorZero * h0GeneratorTwo) :=
  h0Generator_reverse_order 0 2 (by decide)

theorem h0GeneratorTwo_one :
    h0GeneratorTwo * h0GeneratorOne =
      centralNegOne * (h0GeneratorOne * h0GeneratorTwo) :=
  h0Generator_reverse_order 1 2 (by decide)

/-- Select identity or a group element according to a binary coordinate. -/
def bitElement {G : Type*} [One G] (a : ZMod 2) (x : G) : G :=
  if a = 0 then 1 else x

@[simp] theorem bitElement_zero {G : Type*} [One G] (x : G) : bitElement 0 x = 1 := by
  simp [bitElement]

@[simp] theorem bitElement_one {G : Type*} [One G] (x : G) : bitElement 1 x = x := by
  simp [bitElement]

/-- Canonical ordered Spin representative of a binary `H₀` coordinate. -/
def coordinatesSpin (c : Coordinates) : spinGroup spinQ :=
  bitElement c.central centralNegOne *
    bitElement (c.diag 0) h0GeneratorZero *
    bitElement (c.diag 1) h0GeneratorOne *
    bitElement (c.diag 2) h0GeneratorTwo

theorem centralNegOne_self_tail (r : spinGroup spinQ) :
    centralNegOne * (centralNegOne * r) = r := by
  rw [← mul_assoc, centralNegOne_sq, one_mul]

theorem h0GeneratorZero_central_tail (r : spinGroup spinQ) :
    h0GeneratorZero * (centralNegOne * r) =
      centralNegOne * (h0GeneratorZero * r) := by
  calc
    h0GeneratorZero * (centralNegOne * r) =
        (h0GeneratorZero * centralNegOne) * r := by rw [mul_assoc]
    _ = (centralNegOne * h0GeneratorZero) * r := by
      rw [centralNegOne_comm]
    _ = centralNegOne * (h0GeneratorZero * r) := by rw [mul_assoc]

theorem h0GeneratorOne_central_tail (r : spinGroup spinQ) :
    h0GeneratorOne * (centralNegOne * r) =
      centralNegOne * (h0GeneratorOne * r) := by
  calc
    h0GeneratorOne * (centralNegOne * r) =
        (h0GeneratorOne * centralNegOne) * r := by rw [mul_assoc]
    _ = (centralNegOne * h0GeneratorOne) * r := by
      rw [centralNegOne_comm]
    _ = centralNegOne * (h0GeneratorOne * r) := by rw [mul_assoc]

theorem h0GeneratorTwo_central_tail (r : spinGroup spinQ) :
    h0GeneratorTwo * (centralNegOne * r) =
      centralNegOne * (h0GeneratorTwo * r) := by
  calc
    h0GeneratorTwo * (centralNegOne * r) =
        (h0GeneratorTwo * centralNegOne) * r := by rw [mul_assoc]
    _ = (centralNegOne * h0GeneratorTwo) * r := by
      rw [centralNegOne_comm]
    _ = centralNegOne * (h0GeneratorTwo * r) := by rw [mul_assoc]

theorem h0GeneratorZero_self_tail (r : spinGroup spinQ) :
    h0GeneratorZero * (h0GeneratorZero * r) = centralNegOne * r := by
  rw [← mul_assoc, h0Generator_sq]

theorem h0GeneratorOne_self_tail (r : spinGroup spinQ) :
    h0GeneratorOne * (h0GeneratorOne * r) = centralNegOne * r := by
  rw [← mul_assoc, h0Generator_sq]

theorem h0GeneratorTwo_self_tail (r : spinGroup spinQ) :
    h0GeneratorTwo * (h0GeneratorTwo * r) = centralNegOne * r := by
  rw [← mul_assoc, h0Generator_sq]

theorem h0GeneratorOne_zero_tail (r : spinGroup spinQ) :
    h0GeneratorOne * (h0GeneratorZero * r) =
      centralNegOne * (h0GeneratorZero * (h0GeneratorOne * r)) := by
  rw [← mul_assoc, h0GeneratorOne_zero]
  simp [mul_assoc]

theorem h0GeneratorTwo_zero_tail (r : spinGroup spinQ) :
    h0GeneratorTwo * (h0GeneratorZero * r) =
      centralNegOne * (h0GeneratorZero * (h0GeneratorTwo * r)) := by
  rw [← mul_assoc, h0GeneratorTwo_zero]
  simp [mul_assoc]

theorem h0GeneratorTwo_one_tail (r : spinGroup spinQ) :
    h0GeneratorTwo * (h0GeneratorOne * r) =
      centralNegOne * (h0GeneratorOne * (h0GeneratorTwo * r)) := by
  rw [← mul_assoc, h0GeneratorTwo_one]
  simp [mul_assoc]

theorem bitElement_central_add (a b : ZMod 2) :
    bitElement (a + b) centralNegOne =
      bitElement a centralNegOne * bitElement b centralNegOne := by
  rcases zmodTwo_eq_zero_or_one' a with rfl | rfl <;>
    rcases zmodTwo_eq_zero_or_one' b with rfl | rfl
  · simp
  · simp
  · simp
  · have hz : (1 + 1 : ZMod 2) = 0 := by decide
    rw [hz]
    simp

theorem bitElement_central_comm (a : ZMod 2) (x : spinGroup spinQ) :
    bitElement a centralNegOne * x = x * bitElement a centralNegOne := by
  rcases zmodTwo_eq_zero_or_one' a with rfl | rfl
  · simp
  · exact centralNegOne_comm x

def diagonalSpin (a : Fin 3 → ZMod 2) : spinGroup spinQ :=
  bitElement (a 0) h0GeneratorZero *
    bitElement (a 1) h0GeneratorOne *
    bitElement (a 2) h0GeneratorTwo

theorem coordinatesSpin_eq (c : Coordinates) :
    coordinatesSpin c =
      bitElement c.central centralNegOne * diagonalSpin c.diag := by
  simp [coordinatesSpin, diagonalSpin, mul_assoc]

set_option maxHeartbeats 400000 in
theorem diagonalSpin_mul (a b : Fin 3 → ZMod 2) :
    diagonalSpin a * diagonalSpin b =
      bitElement (triangularCocycle a b) centralNegOne * diagonalSpin (a + b) := by
  rcases zmodTwo_eq_zero_or_one' (a 0) with ha0 | ha0 <;>
    rcases zmodTwo_eq_zero_or_one' (a 1) with ha1 | ha1 <;>
    rcases zmodTwo_eq_zero_or_one' (a 2) with ha2 | ha2 <;>
    rcases zmodTwo_eq_zero_or_one' (b 0) with hb0 | hb0 <;>
    rcases zmodTwo_eq_zero_or_one' (b 1) with hb1 | hb1 <;>
    rcases zmodTwo_eq_zero_or_one' (b 2) with hb2 | hb2 <;>
    simp [diagonalSpin, bitElement, triangularCocycle, Fin.sum_univ_three,
      ha0, ha1, ha2, hb0, hb1, hb2, mul_assoc,
      h0GeneratorOne_zero, h0GeneratorTwo_zero, h0GeneratorTwo_one,
      centralNegOne_comm,
      
      h0GeneratorZero_self_tail, h0GeneratorOne_self_tail,
      h0GeneratorOne_zero_tail,
      h0GeneratorTwo_zero_tail, h0GeneratorTwo_one_tail]

theorem coordinatesSpin_mul (c d : Coordinates) :
    coordinatesSpin (c * d) = coordinatesSpin c * coordinatesSpin d := by
  let zc := bitElement c.central centralNegOne
  let zd := bitElement d.central centralNegOne
  let zk := bitElement (triangularCocycle c.diag d.diag) centralNegOne
  let Dc := diagonalSpin c.diag
  let Dd := diagonalSpin d.diag
  let Dcd := diagonalSpin (c.diag + d.diag)
  have hdiag : Dc * Dd = zk * Dcd := diagonalSpin_mul c.diag d.diag
  have hcomm : Dc * zd = zd * Dc := (bitElement_central_comm d.central Dc).symm
  rw [coordinatesSpin_eq (c * d), coordinatesSpin_eq c, coordinatesSpin_eq d]
  change bitElement (c.central + d.central + triangularCocycle c.diag d.diag)
      centralNegOne * Dcd = (zc * Dc) * (zd * Dd)
  calc
    bitElement (c.central + d.central + triangularCocycle c.diag d.diag)
          centralNegOne * Dcd = ((zc * zd) * zk) * Dcd := by
      rw [bitElement_central_add (c.central + d.central)
          (triangularCocycle c.diag d.diag),
        bitElement_central_add c.central d.central]
    _ = (zc * zd) * (zk * Dcd) := by rw [mul_assoc]
    _ = (zc * zd) * (Dc * Dd) := by rw [hdiag]
    _ = zc * (zd * (Dc * Dd)) := by rw [mul_assoc]
    _ = zc * ((zd * Dc) * Dd) := by rw [mul_assoc]
    _ = zc * ((Dc * zd) * Dd) := by rw [hcomm]
    _ = (zc * Dc) * (zd * Dd) := by simp [mul_assoc]

def coordinatesSpinHom : Coordinates →* spinGroup spinQ where
  toFun := coordinatesSpin
  map_one' := by simp [coordinatesSpin]
  map_mul' := coordinatesSpin_mul

@[simp] theorem coordinatesSpinHom_apply (c : Coordinates) :
    coordinatesSpinHom c = coordinatesSpin c := rfl

def cliffordBitSign (a : ZMod 2) : Clifford :=
  if a = 0 then 1 else -1

theorem bivector_terminal_mul_basis_same (i : Fin 4) (hi : i ≠ 3) :
    bivector i 3 * basisClifford i =
      -(basisClifford i * bivector i 3) := by
  calc
    bivector i 3 * basisClifford i =
        basisClifford i *
          (basisClifford 3 * basisClifford i) := by
      simp [bivector, mul_assoc]
    _ = basisClifford i *
          (-(basisClifford i * basisClifford 3)) := by
      rw [basisClifford_anti 3 i (Ne.symm hi)]
    _ = -(basisClifford i * bivector i 3) := by
      rw [show basisClifford i *
          (-(basisClifford i * basisClifford 3)) =
          -(basisClifford i * basisClifford i) *
            basisClifford 3 by noncomm_ring,
        basisClifford_sq]
      simp only [bivector]
      rw [← mul_assoc, basisClifford_sq]
      simp

theorem bivector_terminal_mul_basis_ne (i k : Fin 4)
    (hk : k ≠ 3) (hik : i ≠ k) :
    bivector i 3 * basisClifford k =
      basisClifford k * bivector i 3 := by
  calc
    bivector i 3 * basisClifford k =
        basisClifford i *
          (basisClifford 3 * basisClifford k) := by
      simp [bivector, mul_assoc]
    _ = basisClifford i *
          (-(basisClifford k * basisClifford 3)) := by
      rw [basisClifford_anti 3 k (Ne.symm hk)]
    _ = -(basisClifford i * basisClifford k) *
          basisClifford 3 := by noncomm_ring
    _ = basisClifford k * basisClifford i *
          basisClifford 3 := by
      rw [basisClifford_anti i k hik]
      noncomm_ring
    _ = basisClifford k * bivector i 3 := by
      simp [bivector, mul_assoc]

theorem bivector_terminal_basis_same_tail (i : Fin 4) (hi : i ≠ 3) (r : Clifford) :
    bivector i 3 * (basisClifford i * r) =
      -(basisClifford i * (bivector i 3 * r)) := by
  rw [← mul_assoc, bivector_terminal_mul_basis_same i hi]
  noncomm_ring

theorem bivector_terminal_basis_ne_tail (i k : Fin 4)
    (hk : k ≠ 3) (hik : i ≠ k) (r : Clifford) :
    bivector i 3 * (basisClifford k * r) =
      basisClifford k * (bivector i 3 * r) := by
  rw [← mul_assoc, bivector_terminal_mul_basis_ne i k hk hik, mul_assoc]

theorem coordinatesSpin_mul_basis (c : Coordinates) (k : Fin 3) :
    ((coordinatesSpin c : spinGroup spinQ) : Clifford) * basisClifford k.castSucc =
      cliffordBitSign (c.diag k) * basisClifford k.castSucc *
        ((coordinatesSpin c : spinGroup spinQ) : Clifford) := by
  rcases zmodTwo_eq_zero_or_one' c.central with hc | hc <;>
    rcases zmodTwo_eq_zero_or_one' (c.diag 0) with h0 | h0 <;>
    rcases zmodTwo_eq_zero_or_one' (c.diag 1) with h1 | h1 <;>
    rcases zmodTwo_eq_zero_or_one' (c.diag 2) with h2 | h2 <;>
    fin_cases k <;>
    simp [coordinatesSpin, bitElement, cliffordBitSign, hc, h0, h1, h2,
      Submonoid.coe_mul, h0Generator_val, centralNegOne_val, mul_assoc,
      bivector_terminal_mul_basis_same, bivector_terminal_mul_basis_ne,
      bivector_terminal_basis_same_tail, bivector_terminal_basis_ne_tail]

theorem basisClifford_ne_neg (k : Fin 3) :
    basisClifford k.castSucc ≠ -basisClifford k.castSucc := by
  intro h
  apply clifford_neg_one_ne_one
  have hm := congrArg (fun q : Clifford => q * basisClifford k.castSucc) h
  rw [basisClifford_sq] at hm
  simpa using hm

theorem cliffordBitSign_mul_basis_injective (k : Fin 3) :
    Function.Injective
      (fun a : ZMod 2 => cliffordBitSign a * basisClifford k.castSucc) := by
  intro a b hab
  rcases zmodTwo_eq_zero_or_one' a with rfl | rfl <;>
    rcases zmodTwo_eq_zero_or_one' b with rfl | rfl
  · rfl
  · exact False.elim (basisClifford_ne_neg k (by simpa [cliffordBitSign] using hab))
  · exact False.elim (basisClifford_ne_neg k (by simpa [cliffordBitSign] using hab.symm))
  · rfl

theorem bitElement_injective_of_ne_one {G : Type*} [Group G]
    {x : G} (hx : x ≠ 1) : Function.Injective (fun a : ZMod 2 => bitElement a x) := by
  intro a b hab
  rcases zmodTwo_eq_zero_or_one' a with rfl | rfl <;>
    rcases zmodTwo_eq_zero_or_one' b with rfl | rfl
  · rfl
  · exact False.elim (hx hab.symm)
  · exact False.elim (hx hab)
  · rfl

theorem coordinatesSpinHom_injective : Function.Injective coordinatesSpinHom := by
  intro c d hcd
  change coordinatesSpin c = coordinatesSpin d at hcd
  have hdiag : c.diag = d.diag := by
    funext k
    apply cliffordBitSign_mul_basis_injective k
    have hm := congrArg
      (fun x : spinGroup spinQ => (x : Clifford) * basisClifford k.castSucc) hcd
    rw [coordinatesSpin_mul_basis c k, coordinatesSpin_mul_basis d k] at hm
    rw [← hcd] at hm
    have hm' := congrArg
      (fun q : Clifford => q * (((coordinatesSpin c)⁻¹ : spinGroup spinQ) : Clifford)) hm
    have hinv : ((coordinatesSpin c : spinGroup spinQ) : Clifford) *
        (((coordinatesSpin c)⁻¹ : spinGroup spinQ) : Clifford) = 1 := by
      rw [← Submonoid.coe_mul]
      simp
    simpa [mul_assoc, hinv] using hm'
  apply Coordinates.ext
  · exact hdiag
  · have h := hcd
    rw [coordinatesSpin_eq c, coordinatesSpin_eq d, hdiag] at h
    exact bitElement_injective_of_ne_one centralNegOne_ne_one (mul_right_cancel h)

/-- Spin subgroup generated by all canonical rank-four Weyl rotors. -/
def spinWeylSubgroup : Subgroup (spinGroup spinQ) :=
  Subgroup.closure {x | ∃ (i j : Fin 4) (hij : i ≠ j), x = weylLift i j hij}

theorem weylLift_mem_spinWeylSubgroup (i j : Fin 4) (hij : i ≠ j) :
    weylLift i j hij ∈ spinWeylSubgroup := by
  apply Subgroup.subset_closure
  exact ⟨i, j, hij, rfl⟩

theorem h0Generator_mem_spinWeylSubgroup (i : Fin 3) :
    h0Generator i ∈ spinWeylSubgroup := by
  exact spinWeylSubgroup.pow_mem (spinWeylSubgroup.inv_mem
    (weylLift_mem_spinWeylSubgroup i.castSucc 3 (Fin.castSucc_ne_last i))) 2

theorem centralNegOne_mem_spinWeylSubgroup : centralNegOne ∈ spinWeylSubgroup := by
  exact (spinWeylSubgroup.pow_mem
    (weylLift_mem_spinWeylSubgroup 0 1 (by decide)) 4)

theorem coordinatesSpin_mem_spinWeylSubgroup (c : Coordinates) :
    coordinatesSpin c ∈ spinWeylSubgroup := by
  have hz : bitElement c.central centralNegOne ∈ spinWeylSubgroup := by
    rcases zmodTwo_eq_zero_or_one' c.central with hc | hc
    · simp [hc]
    · simpa [hc] using centralNegOne_mem_spinWeylSubgroup
  have h0 : bitElement (c.diag 0) h0GeneratorZero ∈ spinWeylSubgroup := by
    rcases zmodTwo_eq_zero_or_one' (c.diag 0) with h | h
    · simp [h]
    · simpa [h] using h0Generator_mem_spinWeylSubgroup 0
  have h1 : bitElement (c.diag 1) h0GeneratorOne ∈ spinWeylSubgroup := by
    rcases zmodTwo_eq_zero_or_one' (c.diag 1) with h | h
    · simp [h]
    · simpa [h] using h0Generator_mem_spinWeylSubgroup 1
  have h2 : bitElement (c.diag 2) h0GeneratorTwo ∈ spinWeylSubgroup := by
    rcases zmodTwo_eq_zero_or_one' (c.diag 2) with h | h
    · simp [h]
    · simpa [h] using h0Generator_mem_spinWeylSubgroup 2
  exact spinWeylSubgroup.mul_mem
    (spinWeylSubgroup.mul_mem (spinWeylSubgroup.mul_mem hz h0) h1) h2

def coordinatesSpinWeylHom : Coordinates →* spinWeylSubgroup :=
  coordinatesSpinHom.codRestrict spinWeylSubgroup coordinatesSpin_mem_spinWeylSubgroup

theorem coordinatesSpinWeylHom_injective :
    Function.Injective coordinatesSpinWeylHom := by
  intro c d h
  apply coordinatesSpinHom_injective
  exact congrArg Subtype.val h

end MilnorSpinWeyl

namespace MilnorDiagonalExtension

open MilnorH0Coordinates MilnorSpinWeyl

variable {F : Type*} [Field F]

/-- Faithful common-subgroup map from Milnor's `H₀` into the rotor-generated Spin Weyl group. -/
def fin4MilnorH0ToSpinWeyl
    (he : fin4MinusOneSymbol F ≠ 0) :
    fin4MilnorH0 (F := F) →* spinWeylSubgroup :=
  coordinatesSpinWeylHom.comp (fin4MilnorH0ToCoordinates he)

theorem fin4MilnorH0ToSpinWeyl_injective
    (he : fin4MinusOneSymbol F ≠ 0) :
    Function.Injective (fin4MilnorH0ToSpinWeyl he) :=
  coordinatesSpinWeylHom_injective.comp
    (fin4MilnorH0ToCoordinates_injective he)

end MilnorDiagonalExtension
end GaloisForLFunctions.HTGeometry

end
