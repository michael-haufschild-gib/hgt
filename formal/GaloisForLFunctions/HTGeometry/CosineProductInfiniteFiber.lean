import GaloisForLFunctions.HTGeometry.CosineProductAperiodic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Infinitely many regular marked points of the reflected product repair

A congruence separates one arithmetic subfamily of source labels from every
reflected source return. All points in this family are genuine holomorphic
1-points, with nonzero displayed denominator.
-/

namespace GaloisForLFunctions.HTGeometry.CosineProductInfiniteFiber

open Complex LabeledCosineDescent CosineProductRepair
open CosineBasepointRepair (divided divided_mul)

noncomputable section

def point (n : ℤ) : ℂ := fiberPoint 1 (7 * n + 1)

theorem point_injective : Function.Injective point := by
  intro n m h
  have hh := first_fiber_injective h
  omega

theorem source_point (n : ℤ) : source (point n) = source 0 := by
  have hf0 : fiberPoint 1 0 = 0 := by norm_num [fiberPoint]
  rw [point, source_fiberPoint]
  simpa [hf0] using (source_fiberPoint 1 0).symm

theorem source_neg_point (n : ℤ) : source (-point n) ≠ source 0 := by
  intro h
  obtain ⟨m, hm, _⟩ := CosineProductAperiodic.source_return_jet h
  have hc : (18 * (m : ℂ) + 1) ^ 2 + (18 * (7 * (n : ℂ) + 1) + 1) ^ 2 = 2 := by
    dsimp [point, fiberPoint] at hm
    push_cast at hm
    linear_combination -12 * hm
  have hi : (18 * m + 1) ^ 2 + (18 * (7 * n + 1) + 1) ^ 2 = (2 : ℤ) := by
    exact_mod_cast hc
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let a : ZMod 7 := (18 * m + 1 : ℤ)
  have hh := congrArg (fun z : ℤ ↦ (z : ZMod 7)) hi
  have h7 : (7 : ZMod 7) = 0 := (ZMod.natCast_eq_zero_iff 7 7).mpr (by norm_num)
  have ha : a ^ 2 = (5 : ZMod 7) := by
    push_cast at hh
    rw [h7] at hh
    norm_num at hh
    dsimp [a]
    push_cast
    linear_combination hh - 52 * h7
  have h125 : (5 : ZMod 7) ^ 3 = 6 := by
    calc
      _ = ((125 : ℕ) : ZMod 7) := by norm_num
      _ = _ := (ZMod.natCast_eq_natCast_iff' 125 6 7).mpr (by norm_num)
  have h5 : (5 : ZMod 7) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 5 7).not.mpr (by norm_num)
  have hf := ZMod.pow_card a
  have hg : a ^ 7 = 6 * a := by
    calc
      _ = a * (a ^ 2) ^ 3 := by ring
      _ = _ := by rw [ha, h125]; ring
  have hz : (5 : ZMod 7) * a = 0 := by linear_combination hf - hg
  have ha0 : a = 0 := (mul_eq_zero.mp hz).resolve_left h5
  exact h5 (by simpa only [ha0, zero_pow (by norm_num : 2 ≠ 0)] using ha.symm)

theorem point_ne_zero (n : ℤ) : point n ≠ 0 := by
  intro h
  exact source_neg_point n (by simp [h])

theorem divided_point (n : ℤ) : divided (point n) = 0 := by
  have h := divided_mul (point n)
  rw [source_point, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_left (point_ne_zero n)

theorem divided_neg_point_ne (n : ℤ) : divided (-point n) ≠ 0 := by
  intro h
  have hh := divided_mul (-point n)
  rw [h, mul_zero] at hh
  exact source_neg_point n (sub_eq_zero.mp hh.symm)

theorem point_denominator_ne (n : ℤ) : denominator (point n) ≠ 0 := by
  simpa [denominator, divided_point] using divided_neg_point_ne n

theorem repair_point (n : ℤ) : repair (point n) = 1 := by
  apply (div_eq_one_iff_eq (point_denominator_ne n)).mpr
  simp [numerator, denominator, divided_point]

theorem infinite_regular_one_fiber :
    Set.Infinite {w : ℂ | denominator w ≠ 0 ∧ AnalyticAt ℂ repair w ∧ repair w = 1} := by
  apply (Set.infinite_range_of_injective point_injective).mono
  rintro w ⟨n, rfl⟩
  exact ⟨point_denominator_ne n, (numerator_entire.analyticAt _).div
    (denominator_entire.analyticAt _) (point_denominator_ne n), repair_point n⟩

theorem no_polynomial_coordinates (P Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ¬ ∀ w : ℂ, numerator w * Q.eval w = denominator w * P.eval w := by
  intro h
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective point_injective).mono
    rintro w ⟨n, rfl⟩
    have hn : numerator (point n) = denominator (point n) :=
      (div_eq_one_iff_eq (point_denominator_ne n)).mp (repair_point n)
    have hh := h (point n)
    rw [hn] at hh
    exact (mul_left_cancel₀ (point_denominator_ne n) hh).symm
  subst P
  have hf : ∀ w : ℂ, w.im ≠ 0 → Q.eval w = 0 := by
    intro w hw
    have hz : (numerator w - denominator w) * Q.eval w = 0 := by
      linear_combination h w
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (off_real_coordinates_distinct hw))
  apply hQ
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective CosineInfiniteDiagonal.point_injective).mono
  rintro w ⟨n, rfl⟩
  simpa using hf _ (CosineInfiniteDiagonal.point_nonreal n)

end

end GaloisForLFunctions.HTGeometry.CosineProductInfiniteFiber
