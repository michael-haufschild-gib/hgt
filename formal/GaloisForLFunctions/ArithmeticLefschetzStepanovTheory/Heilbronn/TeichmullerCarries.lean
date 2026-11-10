import Mathlib.FieldTheory.Finite.Basic
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheArithmeticSquareIsCofree
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.TruncatedLogarithmJets
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheWittCarryIsTheDigitCarryUpToTheFermatQuotient

/-!
# Teichmüller pair collisions and the first Witt carry

The pth-power lift from F_p to Z/p² is multiplicative and injective.
For odd p, its pair sums of residue one have first carry −L_p(x).
Consequently, after scaling any nonzero residue sum, pair collisions
are exactly the fibres of the truncated logarithm.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn

variable {p : ℕ} [Fact p.Prime]

theorem prime_square_pow_congr (a b : ℤ) (hab : (a : ZMod p) = (b : ZMod p)) :
    (a : ZMod (p ^ 2)) ^ p = (b : ZMod (p ^ 2)) ^ p := by
  have hd : (p : ℤ) ∣ a - b := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, hab, sub_self]
  have hbig : (p : ℤ) ^ 2 ∣ a ^ p - b ^ p :=
    AbsoluteGeometryOfSpecZ.prime_pow_succ_dvd_pow_sub_pow (Fact.out : p.Prime)
      one_ne_zero (by simpa only [pow_one] using hd)
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ p - b ^ p) (p ^ 2)).mpr
    (by exact_mod_cast hbig)
  exact sub_eq_zero.mp (by simpa only [Int.cast_sub, Int.cast_pow] using hz)

/-- The multiplicative pth-power section of reduction modulo p. -/
def teichLift (p : ℕ) [Fact p.Prime] (x : ZMod p) : ZMod (p ^ 2) := (x.val : ZMod (p ^ 2)) ^ p

theorem teichLift_intCast (a : ℤ) : teichLift p (a : ZMod p) = (a : ZMod (p ^ 2)) ^ p := by
  have h := prime_square_pow_congr (p := p) (((a : ZMod p).val : ℕ) : ℤ) a (by simp)
  simpa only [teichLift, Int.cast_natCast] using h

theorem teichLift_zero : teichLift p 0 = 0 := by
  simpa only [Int.cast_zero, zero_pow (Fact.out : p.Prime).ne_zero] using
    (teichLift_intCast (p := p) 0)

theorem teichLift_one : teichLift p 1 = 1 := by
  simpa only [Int.cast_one, one_pow] using (teichLift_intCast (p := p) 1)

theorem teichLift_mul (x y : ZMod p) : teichLift p (x * y) = teichLift p x * teichLift p y := by
  have h := prime_square_pow_congr (p := p) (((x * y).val : ℕ) : ℤ)
    ((x.val : ℤ) * (y.val : ℤ)) (by simp)
  simpa only [teichLift, Int.cast_natCast, Int.cast_mul, mul_pow] using h

def teichLiftHom (p : ℕ) [Fact p.Prime] : ZMod p →* ZMod (p ^ 2) where
  toFun := teichLift p
  map_one' := teichLift_one
  map_mul' := teichLift_mul

def primeSquareReduction (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)

theorem primeSquareReduction_teichLift (x : ZMod p) :
    primeSquareReduction p (teichLift p x) = x := by
  simp only [teichLift, map_pow, map_natCast]
  simpa only [ZMod.card, ZMod.natCast_zmod_val] using FiniteField.pow_card x

theorem teichLift_injective : Function.Injective (teichLift p) := by
  intro x y h
  have := congrArg (primeSquareReduction p) h
  simpa only [primeSquareReduction_teichLift] using this

theorem isUnit_teichLift {x : ZMod p} (hx : x ≠ 0) : IsUnit (teichLift p x) :=
  (isUnit_iff_ne_zero.mpr hx).map (teichLiftHom p)

open Polynomial


theorem choose_pred_cast {k : ℕ} (hk : k < p) :
    ((p - 1).choose k : ZMod p) = (-1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hzero : (p.choose (k + 1) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p _).mpr
        ((Fact.out : p.Prime).dvd_choose_self (by omega) hk)
    have hpas := congrArg (fun n : ℕ => (n : ZMod p))
      (Nat.choose_succ_right p k (Fact.out : p.Prime).pos)
    simp only [Nat.cast_add] at hpas
    rw [hzero, ih (by omega)] at hpas
    rw [pow_succ]
    linear_combination -hpas

theorem choose_div_prime_mul {k : ℕ} (hk : k + 1 < p) :
    p.choose (k + 1) / p * (k + 1) = (p - 1).choose k := by
  have hp := (Fact.out : p.Prime)
  have hq : p * (p.choose (k + 1) / p) = p.choose (k + 1) :=
    Nat.mul_div_cancel' (hp.dvd_choose_self (by omega) hk)
  have hpas := Nat.add_one_mul_choose_eq (p - 1) k
  rw [Nat.sub_add_cancel hp.one_le] at hpas
  apply mul_left_cancel₀ hp.ne_zero
  rw [← mul_assoc, hq]
  exact hpas.symm

theorem signed_choose_div_prime_cast {k : ℕ} (hk : k + 1 < p) :
    ((p.choose (k + 1) / p : ℕ) : ZMod p) * (-1) ^ (k + 1) = -(((k + 1 : ℕ) : ZMod p)⁻¹) := by
  have hk0 : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff (ZMod p) p]
    exact Nat.not_dvd_of_pos_of_lt (by omega) hk
  have hm := congrArg (fun n : ℕ => (n : ZMod p)) (choose_div_prime_mul hk)
  simp only [Nat.cast_mul, choose_pred_cast (by omega : k < p)] at hm
  apply mul_right_cancel₀ hk0
  rw [neg_mul, inv_mul_cancel₀ hk0]
  calc
    ((p.choose (k + 1) / p : ℕ) : ZMod p) * (-1) ^ (k + 1) * ((k + 1 : ℕ) : ZMod p)
        = -((((p.choose (k + 1) / p : ℕ) : ZMod p) * ((k + 1 : ℕ) : ZMod p)) * (-1) ^ k) := by
          rw [pow_succ]
          ring
    _ = -((-1 : ZMod p) ^ k * (-1) ^ k) := by rw [hm]
    _ = -1 := by rw [← mul_pow]; simp

open AbsoluteGeometryOfSpecZ

/-- The divided binomial expansion of the carry at a pair summing to one. -/
theorem wittCarry_one_sub_eq_sum (hp2 : p ≠ 2) (a : ℤ) :
    wittCarry p a (1 - a) =
      ∑ i ∈ range (p - 1), ((p.choose (i + 1) / p : ℕ) : ℤ) * (-a) ^ (i + 1) := by
  have hp := (Fact.out : p.Prime)
  have hstart := sum_range_succ' (fun k => (-a) ^ k * (p.choose k : ℤ)) (p - 1)
  simp only [Nat.sub_add_cancel hp.one_le, pow_zero, Nat.choose_zero_right,
    Nat.cast_one, mul_one] at hstart
  have hpow := add_pow (-a) (1 : ℤ) p
  simp only [one_pow, mul_one] at hpow
  rw [sum_range_succ, hstart, Nat.choose_self, Nat.cast_one, mul_one] at hpow
  have hneg : (-a) ^ p = -(a ^ p) := by
    rw [neg_pow, (hp.odd_of_ne_two hp2).neg_one_pow, neg_one_mul]
  rw [hneg, show -a + 1 = 1 - a by ring] at hpow
  have hF : a ^ p + (1 - a) ^ p - 1 =
      ∑ i ∈ range (p - 1), (-a) ^ (i + 1) * (p.choose (i + 1) : ℤ) := by
    linear_combination hpow
  have hqsum : (p : ℤ) *
      (∑ i ∈ range (p - 1), ((p.choose (i + 1) / p : ℕ) : ℤ) * (-a) ^ (i + 1)) =
      ∑ i ∈ range (p - 1), (-a) ^ (i + 1) * (p.choose (i + 1) : ℤ) := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i + 1 < p := by have := mem_range.mp hi; omega
    have hq : (p : ℤ) * ((p.choose (i + 1) / p : ℕ) : ℤ) = (p.choose (i + 1) : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' (hp.dvd_choose_self (by omega : i + 1 ≠ 0) hi')
    rw [← mul_assoc, hq, mul_comm]
  have hcarry : (p : ℤ) * wittCarry p a (1 - a) = a ^ p + (1 - a) ^ p - 1 := by
    simpa only [show a + (1 - a) = 1 by ring, one_pow] using natCast_mul_wittCarry hp a (1 - a)
  apply mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)
  rw [hcarry, hqsum, hF]

/-- Modulo p, the first Witt carry is the negative truncated logarithm. -/
theorem wittCarry_one_sub_cast (hp2 : p ≠ 2) (a : ℤ) :
    (wittCarry p a (1 - a) : ZMod p) = -(truncatedLog (ZMod p) p).eval (a : ZMod p) := by
  rw [wittCarry_one_sub_eq_sum hp2]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_neg]
  rw [truncatedLog, Polynomial.eval_finsetSum, ← Finset.sum_neg_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i + 1 < p := by have := mem_range.mp hi; omega
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [neg_pow, ← mul_assoc, signed_choose_div_prime_cast hi']
  ring


theorem teichLift_pair_int (a : ℤ) :
    teichLift p (a : ZMod p) + teichLift p (1 - (a : ZMod p)) =
      1 + (p : ZMod (p ^ 2)) * (wittCarry p a (1 - a) : ZMod (p ^ 2)) := by
  have h := congrArg (fun z : ℤ => (z : ZMod (p ^ 2)))
    (natCast_mul_wittCarry (Fact.out : p.Prime) a (1 - a))
  simp only [show a + (1 - a) = 1 by ring, one_pow, Int.cast_mul,
    Int.cast_natCast, Int.cast_sub, Int.cast_pow, Int.cast_one, Int.cast_add] at h
  rw [show 1 - (a : ZMod p) = ((1 - a : ℤ) : ZMod p) by simp only [Int.cast_sub, Int.cast_one],
    teichLift_intCast, teichLift_intCast]
  push_cast
  linear_combination -h

/-- Multiplication by `p` identifies the first carry with a residue modulo `p`. -/
theorem prime_mul_cast_eq_iff (a b : ℤ) :
    (p : ZMod (p ^ 2)) * (a : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) * (b : ZMod (p ^ 2)) ↔
      (a : ZMod p) = (b : ZMod p) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  constructor
  · intro h
    have hz : (((p : ℤ) * (a - b) : ℤ) : ZMod (p ^ 2)) = 0 := by
      push_cast
      rw [mul_sub, h, sub_self]
    have hd : (p : ℤ) ^ 2 ∣ (p : ℤ) * (a - b) := by
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).mp hz
    obtain ⟨c, hc⟩ := hd
    have hs : (p : ℤ) ∣ a - b := by
      refine ⟨c, ?_⟩
      apply mul_left_cancel₀ hp0
      calc (p : ℤ) * (a - b) = (p : ℤ) ^ 2 * c := hc
        _ = (p : ℤ) * ((p : ℤ) * c) := by ring
    have hz' := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) p).mpr hs
    exact sub_eq_zero.mp (by simpa only [Int.cast_sub] using hz')
  · intro h
    have hs : (p : ℤ) ∣ a - b := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [Int.cast_sub, h, sub_self]
    obtain ⟨c, hc⟩ := hs
    have hd : (p : ℤ) ^ 2 ∣ (p : ℤ) * (a - b) := by
      refine ⟨c, ?_⟩
      rw [hc]
      ring
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd ((p : ℤ) * (a - b)) (p ^ 2)).mpr
      (by exact_mod_cast hd)
    have hz' : (p : ZMod (p ^ 2)) * (a : ZMod (p ^ 2)) -
        (p : ZMod (p ^ 2)) * (b : ZMod (p ^ 2)) = 0 := by
      simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_sub, mul_sub] using hz
    exact sub_eq_zero.mp hz'

/-- Equal pair sums in the prime-square Teichmüller image are truncated-logarithm collisions. -/
theorem teichLift_pair_eq_iff (hp2 : p ≠ 2) (x y : ZMod p) :
    teichLift p x + teichLift p (1 - x) = teichLift p y + teichLift p (1 - y) ↔
      (truncatedLog (ZMod p) p).eval x = (truncatedLog (ZMod p) p).eval y := by
  have hx := teichLift_pair_int (p := p) (x.val : ℤ)
  have hy := teichLift_pair_int (p := p) (y.val : ℤ)
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at hx hy
  rw [hx, hy, add_right_inj, prime_mul_cast_eq_iff,
    wittCarry_one_sub_cast hp2, wittCarry_one_sub_cast hp2, neg_inj]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- A nonzero residue normalizes pair collisions by a unit Teichmüller lift. -/
theorem teichLift_scaled_pair_eq_iff (hp2 : p ≠ 2) {s : ZMod p} (hs : s ≠ 0) (x y : ZMod p) :
    teichLift p x + teichLift p (s - x) = teichLift p y + teichLift p (s - y) ↔
      (truncatedLog (ZMod p) p).eval (x / s) = (truncatedLog (ZMod p) p).eval (y / s) := by
  have hn (x : ZMod p) : teichLift p x + teichLift p (s - x) =
      teichLift p s * (teichLift p (x / s) + teichLift p (1 - x / s)) := by
    rw [mul_add, ← teichLift_mul, ← teichLift_mul]
    congr 1 <;> congr 1 <;> field_simp [hs]
  rw [hn x, hn y]
  obtain ⟨u, hu⟩ := isUnit_teichLift hs
  rw [← hu]
  constructor
  · intro h
    apply (teichLift_pair_eq_iff hp2 (x / s) (y / s)).mp
    have := congrArg (fun z : ZMod (p ^ 2) => (↑u⁻¹ : ZMod (p ^ 2)) * z) h
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using this
  · intro h
    rw [(teichLift_pair_eq_iff hp2 (x / s) (y / s)).mpr h]

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn

#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.wittCarry_one_sub_cast
#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.teichLift_pair_eq_iff
#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.teichLift_scaled_pair_eq_iff
