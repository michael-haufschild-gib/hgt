import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite root-modulus energy

Bounded weights may depend on both the modulus and the cofactor.
Divisor incidence and two applications of Cauchy--Schwarz bound
their root sums by the unweighted and divisor-weighted energies.
-/

namespace TwinPrime

open Finset

noncomputable section

/-- Complex weights of modulus at most one, including cutoff weights. -/
abbrev UnitWeight := {z : ℂ // ‖z‖ ≤ 1}

/-- The weighted sum on multiples of a positive root modulus. -/
def rootModulusSum (H q : ℕ) (c : ℕ → ℕ → UnitWeight) (a : ℕ → ℂ) : ℂ :=
  ∑ k ∈ (Icc 1 H).filter (q ∣ ·), (c q k).val * a k

/-- Sum of the absolute root-modulus sums. -/
def rootModulusMass (H : ℕ) (c : ℕ → ℕ → UnitWeight) (a : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Icc 1 H, ‖rootModulusSum H q c a‖

/-- Number of incidences between positive moduli and their multiples up to `H`. -/
def divisorIncidenceMass (H : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 H, (k.divisors.card : ℝ)

/-- Cofactor energy weighted by the `j`th power of the divisor count. -/
def cofactorEnergy (H j : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ k ∈ Icc 1 H, (k.divisors.card : ℝ) ^ j * ‖a k‖ ^ 2

/-- Exchanging divisor incidence counts each cofactor once per divisor. -/
theorem sum_rootMultiples_eq (H : ℕ) (f : ℕ → ℝ) :
    (∑ q ∈ Icc 1 H, ∑ k ∈ (Icc 1 H).filter (q ∣ ·), f k) =
      ∑ k ∈ Icc 1 H, (k.divisors.card : ℝ) * f k := by
  classical
  simp only [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hkpos : 0 < k := (mem_Icc.mp hk).1
  have hsets : (Icc 1 H).filter (· ∣ k) = k.divisors := by
    ext q
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨h.2, Nat.ne_of_gt hkpos⟩
    · intro h
      exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hkpos,
        (Nat.le_of_dvd hkpos h.1).trans (mem_Icc.mp hk).2⟩, h.1⟩
  rw [← sum_filter, hsets, sum_const, nsmul_eq_mul]

/-- The triangle bound retains divisor multiplicity, even for modulus-dependent weights. -/
theorem rootModulusMass_le (H : ℕ) (c : ℕ → ℕ → UnitWeight) (a : ℕ → ℂ) :
    rootModulusMass H c a ≤ ∑ k ∈ Icc 1 H, (k.divisors.card : ℝ) * ‖a k‖ := by
  unfold rootModulusMass
  calc
    (∑ q ∈ Icc 1 H, ‖rootModulusSum H q c a‖) ≤
        ∑ q ∈ Icc 1 H, ∑ k ∈ (Icc 1 H).filter (q ∣ ·), ‖a k‖ := by
      refine sum_le_sum fun q _ => (norm_sum_le _ _).trans ?_
      refine sum_le_sum fun k _ => ?_
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (c q k).property (norm_nonneg _)).trans_eq
        (one_mul _)
    _ = _ := sum_rootMultiples_eq H (fun k => ‖a k‖)

/-- A root-modulus average is bounded by the first divisor-weighted energy. -/
theorem rootModulusMass_sq_le (H : ℕ) (c : ℕ → ℕ → UnitWeight) (a : ℕ → ℂ) :
    rootModulusMass H c a ^ 2 ≤ divisorIncidenceMass H * cofactorEnergy H 1 a := by
  have hnonneg : 0 ≤ rootModulusMass H c a := sum_nonneg fun _ _ => norm_nonneg _
  have htriangle := pow_le_pow_left₀ hnonneg (rootModulusMass_le H c a) 2
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul (Icc 1 H)
    (r := fun k => (k.divisors.card : ℝ) * ‖a k‖)
    (f := fun k => (k.divisors.card : ℝ))
    (g := fun k => (k.divisors.card : ℝ) * ‖a k‖ ^ 2)
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => by positivity)
    (fun _ _ => le_of_eq (by ring))
  simpa only [divisorIncidenceMass, cofactorEnergy, pow_one] using htriangle.trans hc

/-- Interpolation between the unweighted and squared-divisor cofactor energies. -/
theorem cofactorEnergy_one_sq_le (H : ℕ) (a : ℕ → ℂ) :
    cofactorEnergy H 1 a ^ 2 ≤ cofactorEnergy H 0 a * cofactorEnergy H 2 a := by
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul (Icc 1 H)
    (r := fun k => (k.divisors.card : ℝ) * ‖a k‖ ^ 2)
    (f := fun k => ‖a k‖ ^ 2)
    (g := fun k => (k.divisors.card : ℝ) ^ 2 * ‖a k‖ ^ 2)
    (fun _ _ => sq_nonneg _) (fun _ _ => by positivity)
    (fun _ _ => le_of_eq (by ring))
  simpa only [cofactorEnergy, pow_one, pow_zero, one_mul] using hc

/-- Fourth-power transfer: a small unweighted energy survives the modulus average. -/
theorem rootModulusMass_pow_four_le (H : ℕ) (c : ℕ → ℕ → UnitWeight) (a : ℕ → ℂ) :
    rootModulusMass H c a ^ 4 ≤
      divisorIncidenceMass H ^ 2 * cofactorEnergy H 0 a * cofactorEnergy H 2 a := by
  have hsq := pow_le_pow_left₀ (sq_nonneg (rootModulusMass H c a))
    (rootModulusMass_sq_le H c a) 2
  calc
    rootModulusMass H c a ^ 4 = (rootModulusMass H c a ^ 2) ^ 2 := by ring
    _ ≤ (divisorIncidenceMass H * cofactorEnergy H 1 a) ^ 2 := hsq
    _ = divisorIncidenceMass H ^ 2 * cofactorEnergy H 1 a ^ 2 := mul_pow _ _ _
    _ ≤ divisorIncidenceMass H ^ 2 * (cofactorEnergy H 0 a * cofactorEnergy H 2 a) :=
      mul_le_mul_of_nonneg_left (cofactorEnergy_one_sq_le H a) (sq_nonneg _)
    _ = _ := by ring

end

end TwinPrime
