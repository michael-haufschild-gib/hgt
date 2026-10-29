import GaloisForLFunctions.HTGeometry.MilnorKDegTwoSymbol
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The rank-one Kubota cocycle in Milnor K₂

For a determinant-one matrix, `kubotaX` is its nonzero lower-left entry, or its
lower-right entry when the former vanishes. The symbol
`{x(gh)/x(g), x(gh)/x(h)}` is a normalized cocycle. Its defect is one Steinberg
symbol; a two-by-two determinant identity handles the open Bruhat cell, and
the triangular cases give the unit or opposite-argument relations.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

open Matrix

noncomputable section

variable {K : Type*} [Field K]

/-- The ordinary special linear group over the coefficient field. -/
abbrev SL2 (K : Type*) [Field K] := SpecialLinearGroup (Fin 2) K

private theorem det_relation (g : SL2 K) :
    g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using g.det_coe

private theorem entry_mul (g h : SL2 K) (i j : Fin 2) :
    (g * h) i j = g i 0 * h 0 j + g i 1 * h 1 j := by
  change ((g : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K)) i j = _
  simp only [Matrix.mul_apply, Fin.sum_univ_two]

/-- The nonzero Bruhat coordinate used in the rank-one symbol. -/
def kubotaX (g : SL2 K) : K := by
  classical
  exact if g 1 0 = 0 then g 1 1 else g 1 0

theorem kubotaX_ne_zero (g : SL2 K) : kubotaX g ≠ 0 := by
  classical
  unfold kubotaX
  split_ifs with h
  · intro hz
    have hd := det_relation g
    rw [h, hz, mul_zero, mul_zero, sub_zero] at hd
    exact zero_ne_one hd
  · exact h

/-- The Bruhat coordinate as a unit, so every Milnor symbol is defined. -/
def kubotaUnit (g : SL2 K) : Kˣ := Units.mk0 (kubotaX g) (kubotaX_ne_zero g)

@[simp] theorem coe_kubotaUnit (g : SL2 K) : (kubotaUnit g : K) = kubotaX g := rfl

private theorem kubotaX_of_zero {g : SL2 K} (h : g 1 0 = 0) :
    kubotaX g = g 1 1 := by classical exact if_pos h

private theorem kubotaX_of_ne_zero {g : SL2 K} (h : g 1 0 ≠ 0) :
    kubotaX g = g 1 0 := by classical exact if_neg h

@[simp] theorem kubotaX_one : kubotaX (1 : SL2 K) = 1 := by
  simp [kubotaX]

@[simp] theorem kubotaUnit_one : kubotaUnit (1 : SL2 K) = 1 := by
  apply Units.ext
  exact kubotaX_one

private theorem kubotaX_mul_left_zero (g h : SL2 K) (hg : g 1 0 = 0) :
    kubotaX (g * h) = kubotaX g * kubotaX h := by
  have hgd : g 1 1 ≠ 0 := by
    simpa only [kubotaX_of_zero hg] using kubotaX_ne_zero g
  rw [kubotaX_of_zero hg]
  by_cases hh : h 1 0 = 0
  · have hgh : (g * h) 1 0 = 0 := by rw [entry_mul, hg, hh]; ring
    rw [kubotaX_of_zero hgh, kubotaX_of_zero hh, entry_mul, hg, zero_mul, zero_add]
  · have hgh : (g * h) 1 0 ≠ 0 := by
      rw [entry_mul, hg, zero_mul, zero_add]
      exact mul_ne_zero hgd hh
    rw [kubotaX_of_ne_zero hgh, kubotaX_of_ne_zero hh, entry_mul, hg,
      zero_mul, zero_add]

private theorem kubotaX_mul_right_zero (g h : SL2 K)
    (hg : g 1 0 ≠ 0) (hh : h 1 0 = 0) :
    kubotaX (g * h) = kubotaX g / kubotaX h := by
  have hd : h 0 0 * h 1 1 = 1 := by
    simpa only [hh, mul_zero, sub_zero] using det_relation h
  have hha : h 0 0 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hd
    exact zero_ne_one hd
  have hhd : h 1 1 ≠ 0 := by
    simpa only [kubotaX_of_zero hh] using kubotaX_ne_zero h
  have hgh : (g * h) 1 0 ≠ 0 := by
    rw [entry_mul, hh, mul_zero, add_zero]
    exact mul_ne_zero hg hha
  rw [kubotaX_of_ne_zero hgh, kubotaX_of_ne_zero hg, kubotaX_of_zero hh,
    eq_div_iff hhd, entry_mul, hh, mul_zero, add_zero, mul_assoc, hd, mul_one]

private theorem kubotaX_mul_eq_neg_div (g h : SL2 K)
    (hg : g 1 0 ≠ 0) (hh : h 1 0 ≠ 0) (hgh : (g * h) 1 0 = 0) :
    kubotaX (g * h) = -kubotaX g / kubotaX h := by
  have hc : g 1 0 * h 0 0 + g 1 1 * h 1 0 = 0 := by
    rw [← entry_mul, hgh]
  rw [kubotaX_of_zero hgh, kubotaX_of_ne_zero hg, kubotaX_of_ne_zero hh,
    eq_div_iff hh, entry_mul]
  linear_combination h 1 1 * hc - g 1 0 * det_relation h

/-- The determinant-one identity governing the six Bruhat coordinates. -/
private theorem lower_left_plucker (g h k : SL2 K) :
    (g * h) 1 0 * (h * k) 1 0 =
      g 1 0 * k 1 0 + h 1 0 * ((g * h) * k) 1 0 := by
  simp only [entry_mul]
  linear_combination (g 1 0 * k 1 0) * det_relation h

/-- Bruhat boundary cases give a unit or opposite pair; the open cell gives
the Steinberg relation. -/
private theorem kubota_cross_relations (g h k : SL2 K) :
    kubotaX (g * h) * kubotaX (h * k) = kubotaX g * kubotaX k ∨
    kubotaX (g * h) * kubotaX (h * k) = kubotaX h * kubotaX ((g * h) * k) ∨
    kubotaX g * kubotaX k = -(kubotaX h * kubotaX ((g * h) * k)) ∨
    kubotaX (g * h) * kubotaX (h * k) =
      kubotaX g * kubotaX k + kubotaX h * kubotaX ((g * h) * k) := by
  by_cases hg : g 1 0 = 0
  · refine Or.inr (Or.inl ?_)
    rw [kubotaX_mul_left_zero g h hg, mul_assoc g h k,
      kubotaX_mul_left_zero g (h * k) hg]
    ring
  by_cases hh : h 1 0 = 0
  · refine Or.inl ?_
    rw [kubotaX_mul_right_zero g h hg hh, kubotaX_mul_left_zero h k hh]
    field_simp [kubotaX_ne_zero h]
  by_cases hgh : (g * h) 1 0 = 0
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [kubotaX_mul_left_zero (g * h) k hgh, kubotaX_mul_eq_neg_div g h hg hh hgh]
    field_simp [kubotaX_ne_zero h]
  by_cases hk : k 1 0 = 0
  · refine Or.inr (Or.inl ?_)
    rw [kubotaX_mul_right_zero h k hh hk, kubotaX_mul_right_zero (g * h) k hgh hk]
    ring
  by_cases hhk : (h * k) 1 0 = 0
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [mul_assoc g h k, kubotaX_mul_right_zero g (h * k) hg hhk,
      kubotaX_mul_eq_neg_div h k hh hk hhk]
    field_simp [kubotaX_ne_zero h, kubotaX_ne_zero k]
  have hp := lower_left_plucker g h k
  by_cases hghk : ((g * h) * k) 1 0 = 0
  · refine Or.inl ?_
    simpa only [kubotaX_of_ne_zero hg, kubotaX_of_ne_zero hk,
      kubotaX_of_ne_zero hgh, kubotaX_of_ne_zero hhk, hghk, mul_zero, add_zero] using hp
  · refine Or.inr (Or.inr (Or.inr ?_))
    simpa only [kubotaX_of_ne_zero hg, kubotaX_of_ne_zero hh,
      kubotaX_of_ne_zero hk, kubotaX_of_ne_zero hgh,
      kubotaX_of_ne_zero hhk, kubotaX_of_ne_zero hghk] using hp

private theorem symbol_div_left (a b c : Kˣ) :
    milnorSym2 K (a / b) c = milnorSym2 K a c - milnorSym2 K b c := by
  rw [div_eq_mul_inv, milnorSym2_mul_left, milnorSym2_inv_left, sub_eq_add_neg]

private theorem symbol_div_right (a b c : Kˣ) :
    milnorSym2 K a (b / c) = milnorSym2 K a b - milnorSym2 K a c := by
  rw [div_eq_mul_inv, milnorSym2_mul_right, milnorSym2_inv_right, sub_eq_add_neg]

/-- The six-coordinate cocycle defect is a single symbol of two cross ratios. -/
theorem kubota_symbol_defect (a b c d e f : Kˣ) :
    milnorSym2 K (d / a) (d / b) + milnorSym2 K (f / d) (f / c) -
      milnorSym2 K (f / a) (f / e) - milnorSym2 K (e / b) (e / c) =
      milnorSym2 K (a * c / (d * e)) (b * f / (d * e)) := by
  simp only [symbol_div_left, symbol_div_right, milnorSym2_mul_left,
    milnorSym2_mul_right]
  rw [milnorSym2_antisymm c b, milnorSym2_antisymm c f,
    milnorSym2_antisymm c d, milnorSym2_antisymm c e,
    milnorSym2_antisymm e b, milnorSym2_antisymm e f,
    milnorSym2_antisymm e d]
  have he : milnorSym2 K e e + milnorSym2 K e e = 0 :=
    eq_neg_iff_add_eq_zero.mp (milnorSym2_antisymm e e)
  apply sub_eq_zero.mp
  calc
    _ = -(milnorSym2 K e e + milnorSym2 K e e) := by abel
    _ = 0 := by rw [he, neg_zero]

private theorem cross_symbol_zero (a b c d e f : Kˣ)
    (h : (d : K) * e = (a : K) * c ∨
      (d : K) * e = (b : K) * f ∨
      (a : K) * c = -((b : K) * f) ∨
      (d : K) * e = (a : K) * c + (b : K) * f) :
    milnorSym2 K (a * c / (d * e)) (b * f / (d * e)) = 0 := by
  rcases h with h | h | h | h
  · have hr : a * c / (d * e) = 1 := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_one]
      rw [← h]
      exact div_self (mul_ne_zero d.ne_zero e.ne_zero)
    rw [hr, milnorSym2_one_left]
  · have hs : b * f / (d * e) = 1 := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_one]
      rw [← h]
      exact div_self (mul_ne_zero d.ne_zero e.ne_zero)
    rw [hs, milnorSym2_one_right]
  · have hs : b * f / (d * e) = -(a * c / (d * e)) := by
      apply Units.ext
      simp only [Units.val_neg, Units.val_div_eq_div_val, Units.val_mul]
      rw [h]
      ring
    rw [hs, milnorSym2_neg_self]
  · let r := a * c / (d * e)
    let s := b * f / (d * e)
    have hsum : (r : K) + (s : K) = 1 := by
      dsimp only [r, s]
      simp only [Units.val_div_eq_div_val, Units.val_mul]
      rw [← add_div, ← h]
      exact div_self (mul_ne_zero d.ne_zero e.ne_zero)
    have hr : (r : K) ≠ 1 := by
      intro hr
      apply s.ne_zero
      linear_combination hsum - hr
    have hs : s = oneSubUnit hr := by
      apply Units.ext
      change (s : K) = 1 - (r : K)
      linear_combination hsum
    change milnorSym2 K r s = 0
    rw [hs, milnorSym2_steinberg]

/-- The additive Kubota symbol with values in the actual degree-two Milnor group. -/
def kubotaCocycle (g h : SL2 K) : MilnorKDeg K 2 :=
  milnorSym2 K (kubotaUnit (g * h) / kubotaUnit g)
    (kubotaUnit (g * h) / kubotaUnit h)

@[simp] theorem kubotaCocycle_one_left (g : SL2 K) : kubotaCocycle 1 g = 0 := by
  simp only [kubotaCocycle, one_mul, kubotaUnit_one, div_eq_mul_inv, inv_one,
    mul_one, mul_inv_cancel,
    milnorSym2_one_right]

@[simp] theorem kubotaCocycle_one_right (g : SL2 K) : kubotaCocycle g 1 = 0 := by
  simp only [kubotaCocycle, mul_one, kubotaUnit_one, div_eq_mul_inv, inv_one,
    mul_one, mul_inv_cancel,
    milnorSym2_one_left]

/-- The rank-one symbol is a cocycle, with no assumed central extension. -/
theorem kubotaCocycle_identity (g h k : SL2 K) :
    kubotaCocycle g h + kubotaCocycle (g * h) k =
      kubotaCocycle g (h * k) + kubotaCocycle h k := by
  have hz := cross_symbol_zero (kubotaUnit g) (kubotaUnit h) (kubotaUnit k)
    (kubotaUnit (g * h)) (kubotaUnit (h * k)) (kubotaUnit ((g * h) * k))
    (kubota_cross_relations g h k)
  rw [← kubota_symbol_defect] at hz
  simp only [kubotaCocycle, ← mul_assoc]
  exact sub_eq_zero.mp (by simpa only [sub_sub] using hz)

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
