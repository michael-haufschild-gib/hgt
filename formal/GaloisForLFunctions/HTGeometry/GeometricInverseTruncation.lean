import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The truncated geometric inverse

Multiplying an element with an invertible part by the alternating geometric sum of the remaining
part telescopes: everything cancels except the first term and a remainder carrying the next power.

In a power series ring this says that the alternating geometric sum in the non-constant part is the
inverse up to that order, which is what expands the inverse of a truncated Taylor jet.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [CommRing A]

/-- **The telescoping identity.**  With `b` inverse to `a`, the alternating geometric sum in `r`
inverts `a + r` up to the remainder carrying `r ^ (n+1)`. -/
theorem add_mul_geomSum {a b : A} (hab : a * b = 1) (r : A) (n : ℕ) :
    (a + r) * (∑ k ∈ Finset.range (n + 1), (-1 : A) ^ k * b ^ (k + 1) * r ^ k) =
      1 + (-1 : A) ^ n * b ^ (n + 1) * r ^ (n + 1) := by
  induction n with
  | zero =>
      rw [Finset.sum_range_one]
      simp only [pow_zero, pow_one, mul_one, one_mul, Nat.zero_add]
      linear_combination hab
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have hcancel : (a + r) * ((-1 : A) ^ (n + 1) * b ^ (n + 2) * r ^ (n + 1)) =
          (-1 : A) ^ (n + 1) * b ^ (n + 1) * r ^ (n + 1) +
            (-1 : A) ^ (n + 1) * b ^ (n + 2) * r ^ (n + 2) := by
        have hstep : a * b ^ (n + 2) = b ^ (n + 1) := by
          rw [show n + 2 = (n + 1) + 1 from rfl, pow_succ, ← mul_assoc, mul_comm a (b ^ (n + 1)),
            mul_assoc, hab, mul_one]
        calc (a + r) * ((-1 : A) ^ (n + 1) * b ^ (n + 2) * r ^ (n + 1))
            = (-1 : A) ^ (n + 1) * (a * b ^ (n + 2)) * r ^ (n + 1) +
              (-1 : A) ^ (n + 1) * b ^ (n + 2) * (r * r ^ (n + 1)) := by ring
          _ = (-1 : A) ^ (n + 1) * b ^ (n + 1) * r ^ (n + 1) +
              (-1 : A) ^ (n + 1) * b ^ (n + 2) * r ^ (n + 2) := by
              rw [hstep, ← pow_succ']
      rw [hcancel]
      have hsign : (-1 : A) ^ (n + 1) = -((-1 : A) ^ n) := by ring
      rw [hsign]
      ring

/-! ## The power series form -/

open PowerSeries

/-- The alternating geometric sum of the non-constant part, truncated at order `n`. -/
noncomputable def geomInverseSum (b : A) (r : PowerSeries A) (n : ℕ) : PowerSeries A :=
  ∑ k ∈ Finset.range (n + 1), (-1 : PowerSeries A) ^ k * (PowerSeries.C b : PowerSeries A) ^ (k + 1) * r ^ k

/-- **The truncated geometric inverse of a power series.**  If the constant term `a` has inverse
`b`, then the alternating geometric sum in the non-constant part inverts the series up to a
remainder of order at least `n+1`. -/
theorem mul_geomInverseSum {a b : A} (hab : a * b = 1) (R : PowerSeries A) (n : ℕ) :
    ((PowerSeries.C a : PowerSeries A) + PowerSeries.X * R) * geomInverseSum b (PowerSeries.X * R) n =
      1 + (-1 : PowerSeries A) ^ n * (PowerSeries.C b : PowerSeries A) ^ (n + 1) *
        (PowerSeries.X * R) ^ (n + 1) := by
  have hCab : ((PowerSeries.C a : PowerSeries A)) * (PowerSeries.C b : PowerSeries A) = 1 := by
    rw [← map_mul, hab, map_one]
  rw [geomInverseSum]
  exact add_mul_geomSum hCab (PowerSeries.X * R) n

/-! ## Reading the coefficients of the inverse -/

/-- **The truncated geometric sum computes the coefficients of the inverse up to its order.** -/
theorem coeff_eq_geomInverseSum_of_mul_eq_one {a b : A} (hab : a * b = 1)
    (R Y : PowerSeries A)
    (hY : ((PowerSeries.C a : PowerSeries A) + PowerSeries.X * R) * Y = 1)
    {n m : ℕ} (hm : m ≤ n) :
    PowerSeries.coeff m Y =
      PowerSeries.coeff m (geomInverseSum b (PowerSeries.X * R) n) := by
  set rem : PowerSeries A := (-1 : PowerSeries A) ^ n * (PowerSeries.C b : PowerSeries A) ^ (n + 1) *
    (PowerSeries.X * R) ^ (n + 1) with hrem
  have hdiff : Y - geomInverseSum b (PowerSeries.X * R) n = -(Y * rem) := by
    have hmul : ((PowerSeries.C a : PowerSeries A) + PowerSeries.X * R) *
        (Y - geomInverseSum b (PowerSeries.X * R) n) = -rem := by
      rw [mul_sub, hY, mul_geomInverseSum hab R n, hrem]
      ring
    have hY' : Y * ((PowerSeries.C a : PowerSeries A) + PowerSeries.X * R) = 1 := by
      rw [mul_comm]
      exact hY
    calc Y - geomInverseSum b (PowerSeries.X * R) n
        = (Y * ((PowerSeries.C a : PowerSeries A) + PowerSeries.X * R)) *
            (Y - geomInverseSum b (PowerSeries.X * R) n) := by rw [hY', one_mul]
      _ = Y * (((PowerSeries.C a : PowerSeries A) + PowerSeries.X * R) *
            (Y - geomInverseSum b (PowerSeries.X * R) n)) := by ring
      _ = -(Y * rem) := by rw [hmul, mul_neg]
  have hdvd : (PowerSeries.X : PowerSeries A) ^ (n + 1) ∣ Y * rem := by
    refine Dvd.dvd.mul_left ?_ Y
    rw [hrem, mul_pow]
    exact ⟨(-1 : PowerSeries A) ^ n * (PowerSeries.C b : PowerSeries A) ^ (n + 1) * R ^ (n + 1),
      by ring⟩
  have hzero : PowerSeries.coeff m (Y * rem) = 0 :=
    (PowerSeries.X_pow_dvd_iff.1 hdvd) m (by omega)
  have h := congrArg (PowerSeries.coeff m) hdiff
  rw [map_sub, map_neg, hzero, neg_zero, sub_eq_zero] at h
  exact h

/-- **The coefficients of the truncated geometric sum.** -/
theorem coeff_geomInverseSum_top (b : A) (R : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (geomInverseSum b (PowerSeries.X * R) n) =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : A) ^ k * b ^ (k + 1) * PowerSeries.coeff (n - k) (R ^ k) := by
  rw [geomInverseSum, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hk' : k ≤ n := by omega
  have hterm : (-1 : PowerSeries A) ^ k * (PowerSeries.C b : PowerSeries A) ^ (k + 1) *
      (PowerSeries.X * R) ^ k =
      (PowerSeries.C ((-1 : A) ^ k * b ^ (k + 1)) : PowerSeries A) *
        ((PowerSeries.X : PowerSeries A) ^ k * R ^ k) := by
    rw [map_mul, map_pow, map_pow, mul_pow]
    simp only [map_neg, map_one]
  have hcoeff : PowerSeries.coeff n ((PowerSeries.X : PowerSeries A) ^ k * R ^ k) =
      PowerSeries.coeff (n - k) (R ^ k) := by
    conv_lhs => rw [show n = (n - k) + k from by omega]
    exact PowerSeries.coeff_X_pow_mul _ _ _
  rw [hterm, PowerSeries.coeff_C_mul, hcoeff]

end GaloisForLFunctions.HTGeometry
