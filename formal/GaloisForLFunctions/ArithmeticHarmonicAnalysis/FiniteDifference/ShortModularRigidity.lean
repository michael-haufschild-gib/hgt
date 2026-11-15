import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.ShortResidueProgressions
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic.Linarith

/-!
# Short modular sequences of arbitrary degree

An integer sequence in an interval of width `D` has its positive order
`n+1` difference in `[-2^n D,2^n D]`. If that difference vanishes modulo
a larger modulus, it vanishes over the integers. Bounded integer
sequences with a vanishing positive order difference are constant.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Function

/-- An interval bound controls every positive order finite difference. -/
theorem iterated_difference_interval_bound (f : ℕ → ℤ) (L D : ℤ)
    (hb : ∀ j, L ≤ f j ∧ f j ≤ L + D) (n j : ℕ) :
    -(2 ^ n * D) ≤ (fwdDiff 1)^[n + 1] f j ∧
      (fwdDiff 1)^[n + 1] f j ≤ 2 ^ n * D := by
  induction n generalizing j with
  | zero =>
    simp only [Nat.zero_add, pow_zero, one_mul, iterate_one, fwdDiff]
    have := hb j
    have := hb (j + 1)
    omega
  | succ n ih =>
    rw [iterate_succ_apply']
    change -(2 ^ (n + 1) * D) ≤
        (fwdDiff 1)^[n + 1] f (j + 1) - (fwdDiff 1)^[n + 1] f j ∧
      (fwdDiff 1)^[n + 1] f (j + 1) - (fwdDiff 1)^[n + 1] f j ≤ 2 ^ (n + 1) * D
    have h0 := ih j
    have h1 := ih (j + 1)
    rw [pow_succ]
    constructor <;> nlinarith only [h0.1, h0.2, h1.1, h1.2]

private theorem constant_of_difference_zero (f : ℕ → ℤ)
    (h : fwdDiff 1 f = 0) : ∀ j, f j = f 0 := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    have hs := congrFun h j
    change f (j + 1) - f j = 0 at hs
    omega

private theorem difference_zero_of_second_zero (f : ℕ → ℤ) (L D : ℤ)
    (hb : ∀ j, L ≤ f j ∧ f j ≤ L + D)
    (h : fwdDiff 1 (fwdDiff 1 f) = 0) : fwdDiff 1 f = 0 := by
  have hD : 0 ≤ D := by have := hb 0; omega
  have hd := constant_of_difference_zero (fwdDiff 1 f) h
  have hp := short_modular_progression (fun j => f j - L)
    (D := D) (k := 2 * D + 1) (h := D.toNat + 1) (by omega)
    (fun j _ => by have := hb j; omega)
    (fun j _ => by
      have hj := hd j
      change f (j + 1) - f j = f 1 - f 0 at hj
      have he : (f (j + 1) - L) - (f j - L) = (f 1 - L) - (f 0 - L) := by omega
      rw [he])
  have hlast := hp (D.toNat + 1) le_rfl
  have hbound := hb (D.toNat + 1)
  have hzero := hb 0
  have hcast : ((D.toNat + 1 : ℕ) : ℤ) = D + 1 := by
    rw [Nat.cast_add, Int.toNat_of_nonneg hD, Nat.cast_one]
  rw [hcast] at hlast
  have hz : f 1 - f 0 = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have hm := mul_le_mul_of_nonneg_left (show f 1 - f 0 ≤ -1 by omega)
        (show 0 ≤ D + 1 by omega)
      nlinarith only [hlast, hm, hbound.1, hzero.2]
    · have hm := mul_le_mul_of_nonneg_left (show 1 ≤ f 1 - f 0 by omega)
        (show 0 ≤ D + 1 by omega)
      nlinarith only [hlast, hm, hbound.2, hzero.1]
  funext j
  have hj := hd j
  change f (j + 1) - f j = 0
  change f (j + 1) - f j = f 1 - f 0 at hj
  exact hj.trans hz

/-- A bounded integer sequence with any vanishing positive order difference is constant. -/
theorem bounded_iterated_difference_zero_iff (f : ℕ → ℤ) (L D : ℤ)
    (hb : ∀ j, L ≤ f j ∧ f j ≤ L + D) (n : ℕ) :
    (fwdDiff 1)^[n + 1] f = 0 ↔ ∀ j, f j = f 0 := by
  constructor
  · intro hz
    suffices h : fwdDiff 1 f = 0 from constant_of_difference_zero f h
    induction n generalizing f L D with
    | zero => exact hz
    | succ n ih =>
      have hbg : ∀ j, -D ≤ fwdDiff 1 f j ∧ fwdDiff 1 f j ≤ -D + 2 * D := by
        intro j
        have := iterated_difference_interval_bound f L D hb 0 j
        simp only [Nat.zero_add, pow_zero, one_mul, iterate_one] at this
        omega
      have hg : fwdDiff 1 (fwdDiff 1 f) = 0 :=
        ih (fwdDiff 1 f) (-D) (2 * D) hbg (by
          simpa only [iterate_succ_apply] using hz)
      exact difference_zero_of_second_zero f L D hb hg
  · intro hc
    have he : f = fun _ => f 0 := funext hc
    rw [he, iterate_succ_apply, fwdDiff_const]
    have hz : (fwdDiff (1 : ℕ))^[n] (fun _ => (0 : ℤ)) = fun _ => 0 := by
      induction n with
      | zero => rfl
      | succ n ih => rw [iterate_succ_apply', ih, fwdDiff_const]
    exact hz

/-- Below the difference-size threshold, modular polynomiality forces constancy. -/
theorem short_modular_iterated_difference_iff (f : ℕ → ℤ) (L D k : ℤ)
    (hb : ∀ j, L ≤ f j ∧ f j ≤ L + D) (n : ℕ) (hk : 2 ^ n * D < k) :
    (∀ j, (fwdDiff 1)^[n + 1] f j ≡ 0 [ZMOD k]) ↔ ∀ j, f j = f 0 := by
  rw [← bounded_iterated_difference_zero_iff f L D hb n]
  constructor
  · intro hm
    funext j
    have hd := iterated_difference_interval_bound f L D hb n j
    have hD : 0 ≤ D := by have := hb 0; omega
    have hpow : 0 ≤ (2 : ℤ) ^ n * D := mul_nonneg (pow_nonneg (by omega) _) hD
    have hdiv : k ∣ (fwdDiff 1)^[n + 1] f j := by
      have he := Int.modEq_iff_dvd.mp (hm j).symm
      simpa only [sub_zero] using he
    obtain ⟨a, ha⟩ := hdiv
    have ha0 : a = 0 := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hn | hn
      · have hh := mul_le_mul_of_nonneg_left (show a ≤ -1 by omega)
          (show 0 ≤ k by omega)
        nlinarith only [ha, hh, hd.1, hk]
      · have hh := mul_le_mul_of_nonneg_left (show 1 ≤ a by omega)
          (show 0 ≤ k by omega)
        nlinarith only [ha, hh, hd.2, hk]
    change (fwdDiff 1)^[n + 1] f j = 0
    simpa only [ha0, mul_zero] using ha
  · intro he j
    rw [he]
    exact Int.ModEq.refl 0

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.iterated_difference_interval_bound
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.bounded_iterated_difference_zero_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.short_modular_iterated_difference_iff
