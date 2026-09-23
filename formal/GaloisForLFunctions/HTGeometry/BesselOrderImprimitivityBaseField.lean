import GaloisForLFunctions.HTGeometry.BesselOrderIsomonodromyBaseField
import GaloisForLFunctions.HTGeometry.RatFuncShiftSquareOrbit

/-!
# Bessel order imprimitivity obstruction after constant-field extension

The global discriminant argument excluding an imprimitive order module uses only algebraic
closedness and characteristic zero. This version works over every such constant field, including
the differential closure used by the parameterized Galois endgame.
-/

namespace GaloisForLFunctions.HTGeometry.FieldShift

noncomputable section

open Polynomial

variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]

/-- The order module remains non-imprimitive after every algebraically closed characteristic-zero
extension of its constant field. -/
theorem orderBessel_no_imprimitive_pair {c : F} (hc : c ≠ 0) {e p : RatFunc F} (hp : p ≠ 0)
    (hE : ratShift e = e / p + 2 * orderShiftCoeff c)
    (hP : p * ratShift p =
      1 + orderShiftCoeff c * e + orderShiftCoeff c ^ (2 : ℕ) * p) : False := by
  set b : RatFunc F := orderShiftCoeff c with hbdef
  have hb0 : b ≠ 0 := orderShiftCoeff_ne_zero hc
  have hbdeg : b.intDegree = 1 := intDegree_orderShiftCoeff hc
  have h2 : (2 : RatFunc F) ≠ 0 := by norm_num
  have htwoDeg : ((2 : RatFunc F)).intDegree = 0 := by
    have htwo : (2 : RatFunc F) = algebraMap F (RatFunc F) 2 :=
      (map_ofNat (algebraMap F (RatFunc F)) 2).symm
    rw [htwo, intDegree_algebraMap_const]
  have hriccati : ∀ r : RatFunc F, r ≠ 0 → ratShift r = b + 1 / r → False := by
    intro r hr hrs
    refine orderBesselRiccati_no_ratFunc_solution hc ⟨r, ?_⟩
    have hbb : algebraMap (Polynomial F) (RatFunc F) (C c * (X + C 1)) = b := by
      rw [hbdef, orderShiftCoeff]
    rw [hrs, hbb]
    field_simp
    ring
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_div, zero_add] at hE
    rcases mul_eq_zero.mp hE.symm with h | h
    · exact h2 h
    · exact hb0 h
  have hsp : ratShift p = (1 + b * e + b ^ (2 : ℕ) * p) / p := by
    field_simp
    linear_combination hP
  have h4s : ratShift (4 : RatFunc F) = 4 := by simpa using map_ofNat ratShift 4
  have h2s : ratShift (2 : RatFunc F) = 2 := by simpa using map_ofNat ratShift 2
  have hkey : ratShift (e ^ (2 : ℕ) - 4 * p) * p ^ (2 : ℕ) = e ^ (2 : ℕ) - 4 * p := by
    rw [map_sub, map_pow, map_mul, hE, hsp, h4s]
    field_simp
    ring
  have hD0 : e ^ (2 : ℕ) - 4 * p ≠ 0 := by
    intro h0
    have hep : e ^ (2 : ℕ) = 4 * p := by linear_combination h0
    have he2 : e / 2 ≠ 0 := div_ne_zero he0 h2
    refine hriccati (e / 2) he2 ?_
    rw [map_div₀, hE, h2s]
    field_simp
    linear_combination hep
  have hsq : IsSquare (e ^ (2 : ℕ) - 4 * p) :=
    isSquare_of_ratShift_mul_sq hD0 hp hkey
  obtain ⟨k, hk⟩ := hsq
  have hkk : e ^ (2 : ℕ) - k * k = 4 * p := by linear_combination hk
  set r₁ : RatFunc F := (e + k) / 2 with hr₁def
  set r₂ : RatFunc F := (e - k) / 2 with hr₂def
  have hsum : r₁ + r₂ = e := by rw [hr₁def, hr₂def]; field_simp; ring
  have hprod : r₁ * r₂ = p := by
    rw [hr₁def, hr₂def]
    field_simp
    linear_combination hkk
  have hr₁0 : r₁ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    exact hp hprod.symm
  have hr₂0 : r₂ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact hp hprod.symm
  have hsD : ratShift (e ^ (2 : ℕ) - 4 * p) ≠ 0 := fun h0 =>
    hD0 (ratShift_injective (by rw [h0, map_zero]))
  have hsp0 : ratShift p ≠ 0 := fun h0 =>
    hp (ratShift_injective (by rw [h0, map_zero]))
  have hpdeg : p.intDegree = 0 := by
    have h1 := congrArg RatFunc.intDegree hkey
    rw [RatFunc.intDegree_mul hsD (pow_ne_zero 2 hp), intDegree_ratShift,
      show p ^ (2 : ℕ) = p * p from sq p, RatFunc.intDegree_mul hp hp] at h1
    omega
  have h2bdeg : ((2 : RatFunc F) * b).intDegree = 1 := by
    rw [RatFunc.intDegree_mul h2 hb0, htwoDeg, hbdeg, zero_add]
  have hedeg : e.intDegree = 1 := by
    have hepdiv : (e / p).intDegree = e.intDegree := by
      rw [RatFunc.intDegree_div he0 hp, hpdeg, sub_zero]
    have hge : 1 ≤ e.intDegree := by
      by_contra hlt
      push Not at hlt
      obtain ⟨hne, hdeg⟩ := intDegree_add_eq_left (u := 2 * b) (v := e / p)
        (mul_ne_zero h2 hb0) (Or.inr (by rw [hepdiv, h2bdeg]; omega))
      have hh := congrArg RatFunc.intDegree hE
      rw [intDegree_ratShift, add_comm (e / p), hdeg, h2bdeg] at hh
      omega
    by_contra hne1
    have hgt : 1 < e.intDegree := by omega
    have hb2p : (b ^ (2 : ℕ) * p).intDegree = 2 := by
      rw [RatFunc.intDegree_mul (pow_ne_zero 2 hb0) hp, show b ^ (2 : ℕ) = b * b from sq b,
        RatFunc.intDegree_mul hb0 hb0, hbdeg, hpdeg]
      norm_num
    have hone : ((1 : RatFunc F)).intDegree = 0 := by simp
    obtain ⟨hne1', hdeg1⟩ :=
      intDegree_add_eq_left (u := b ^ (2 : ℕ) * p) (v := 1) (mul_ne_zero (pow_ne_zero 2 hb0) hp)
        (Or.inr (by rw [hone, hb2p]; norm_num))
    have hbe : (b * e).intDegree = 1 + e.intDegree := by
      rw [RatFunc.intDegree_mul hb0 he0, hbdeg]
    obtain ⟨hne2, hdeg2⟩ :=
      intDegree_add_eq_left (u := b * e) (v := b ^ (2 : ℕ) * p + 1) (mul_ne_zero hb0 he0)
        (Or.inr (by rw [hdeg1, hb2p, hbe]; omega))
    have hPP : (1 : RatFunc F) + b * e + b ^ (2 : ℕ) * p = b * e + (b ^ (2 : ℕ) * p + 1) := by ring
    have hlhs : (p * ratShift p).intDegree = 0 := by
      rw [RatFunc.intDegree_mul hp hsp0, intDegree_ratShift, hpdeg]
      norm_num
    have hh := congrArg RatFunc.intDegree hP
    rw [hlhs, hPP, hdeg2, hbe] at hh
    omega
  have hrsum : r₁.intDegree + r₂.intDegree = 0 := by
    have h1 := congrArg RatFunc.intDegree hprod
    rw [RatFunc.intDegree_mul hr₁0 hr₂0, hpdeg] at h1
    omega
  have hrcase : (r₁.intDegree = 1 ∧ r₂.intDegree = -1)
      ∨ (r₂.intDegree = 1 ∧ r₁.intDegree = -1) := by
    rcases lt_trichotomy r₁.intDegree r₂.intDegree with h | h | h
    · obtain ⟨_, hd⟩ := intDegree_add_eq_left hr₂0 (Or.inr h)
      have hde : e.intDegree = r₂.intDegree := by rw [← hsum, add_comm]; exact hd
      right
      constructor <;> omega
    · exfalso
      have hle := RatFunc.intDegree_add_le hr₂0 (by rw [hsum]; exact he0)
      rw [hsum] at hle
      omega
    · obtain ⟨_, hd⟩ := intDegree_add_eq_left hr₁0 (Or.inr h)
      have hde : e.intDegree = r₁.intDegree := by rw [← hsum]; exact hd
      left
      constructor <;> omega
  have hsum' : (b + 1 / r₁) + (b + 1 / r₂) = ratShift r₁ + ratShift r₂ := by
    have hh : ratShift r₁ + ratShift r₂ = ratShift e := by rw [← map_add, hsum]
    rw [hh, hE, ← hprod, ← hsum]
    field_simp
    ring
  have hprod' : (b + 1 / r₁) * (b + 1 / r₂) = ratShift r₁ * ratShift r₂ := by
    have hh : ratShift r₁ * ratShift r₂ = ratShift p := by rw [← map_mul, hprod]
    rw [hh, hsp, ← hprod, ← hsum]
    field_simp
    ring
  have hroot : (ratShift r₁ - (b + 1 / r₁)) * (ratShift r₁ - (b + 1 / r₂)) = 0 := by
    linear_combination (-(ratShift r₁)) * hsum' + hprod'
  rcases mul_eq_zero.mp hroot with h | h
  · exact hriccati r₁ hr₁0 (by linear_combination h)
  · have hswap1 : ratShift r₁ = b + 1 / r₂ := by linear_combination h
    have hswap2 : ratShift r₂ = b + 1 / r₁ := by linear_combination -hsum' - h
    rcases hrcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hinv : (1 / r₁).intDegree = -1 := by
        rw [one_div, RatFunc.intDegree_inv, h1]
      obtain ⟨_, hd⟩ := intDegree_add_eq_left hb0
        (Or.inr (by rw [hinv, hbdeg]; norm_num))
      have hh := congrArg RatFunc.intDegree hswap2
      rw [intDegree_ratShift, hd, hbdeg] at hh
      omega
    · have hinv : (1 / r₂).intDegree = -1 := by
        rw [one_div, RatFunc.intDegree_inv, h1]
      obtain ⟨_, hd⟩ := intDegree_add_eq_left hb0
        (Or.inr (by rw [hinv, hbdeg]; norm_num))
      have hh := congrArg RatFunc.intDegree hswap1
      rw [intDegree_ratShift, hd, hbdeg] at hh
      omega

end

end GaloisForLFunctions.HTGeometry.FieldShift
