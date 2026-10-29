import GaloisForLFunctions.ArithmeticEffectivityTheory.TheFourierCoefficientsOfTheTorsionMeasure

/-!
# Primitive-root prefix energy and quadratic residue remainders

Finite root orthogonality gives the total prefix energy at each modulus.
Möbius inversion then isolates the primitive order. The resulting signed
quadratic residue sum is exactly a sum of squared absolute values.
-/

noncomputable section

open Polynomial Finset Complex
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticEffectivityTheory

/-- The actual finite prefix energy on primitive roots of the stated order. -/
def primitiveRootPrefixEnergy (m k : ℕ) : ℝ :=
  ∑ ζ ∈ primitiveRoots m ℂ, Complex.normSq (∑ j ∈ range k, ζ ^ j)

theorem primitiveRootPrefixEnergy_nonneg (m k : ℕ) : 0 ≤ primitiveRootPrefixEnergy m k :=
  sum_nonneg fun ζ _ => Complex.normSq_nonneg _

private theorem conj_pow_eq_complement {d : ℕ} (hd : 0 < d) {ζ : ℂ}
    (hζ : ζ ^ d = 1) {i : ℕ} (hi : i ≤ d) : conj (ζ ^ i) = ζ ^ (d - i) := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne'] at hζ
    exact zero_ne_one hζ
  have hnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ hd.ne'
  have hsq : Complex.normSq (ζ ^ i) = 1 := by
    rw [← Complex.sq_norm, norm_pow, hnorm, one_pow, one_pow]
  apply mul_right_cancel₀ (pow_ne_zero i hζ0)
  rw [← Complex.normSq_eq_conj_mul_self, hsq, Complex.ofReal_one,
    ← pow_add, Nat.sub_add_cancel hi, hζ]

private theorem sum_nthRoots_conj_pow_mul_pow {d i j : ℕ} (hd : 0 < d)
    (hi : i < d) (hj : j < d) :
    (∑ ζ ∈ nthRootsFinset d (1 : ℂ), conj (ζ ^ i) * ζ ^ j) =
      if i = j then (d : ℂ) else 0 := by
  have hterm : ∀ ζ ∈ nthRootsFinset d (1 : ℂ),
      conj (ζ ^ i) * ζ ^ j = ζ ^ (d - i + j) := by
    intro ζ hζ
    rw [conj_pow_eq_complement hd ((mem_nthRootsFinset hd).mp hζ) hi.le, pow_add]
  rw [sum_congr rfl hterm, sum_nthRoots_pow hd]
  have he : d ∣ d - i + j ↔ i = j := by
    constructor
    · rintro ⟨a, ha⟩
      have hpos : 0 < d - i + j := by omega
      have hlt : d - i + j < 2 * d := by omega
      have ha1 : a = 1 := by
        have ha0 : a ≠ 0 := by
          intro h
          rw [h, mul_zero] at ha
          omega
        have ha2 : a < 2 := by
          by_contra h
          have hmul := Nat.mul_le_mul_left d (not_lt.mp h)
          nlinarith only [ha, hlt, hmul]
        omega
      rw [ha1, mul_one] at ha
      omega
    · rintro rfl
      rw [Nat.sub_add_cancel hi.le]
  rw [he]

private theorem nthRoots_prefix_energy_of_le {d r : ℕ} (hd : 0 < d) (hr : r ≤ d) :
    (∑ ζ ∈ nthRootsFinset d (1 : ℂ), Complex.normSq (∑ j ∈ range r, ζ ^ j)) =
      (d : ℝ) * r := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, sum_mul, mul_sum]
  calc
    _ = ∑ i ∈ range r, ∑ ζ ∈ nthRootsFinset d (1 : ℂ),
        ∑ j ∈ range r, conj (ζ ^ i) * ζ ^ j := sum_comm
    _ = ∑ i ∈ range r, ∑ j ∈ range r,
        ∑ ζ ∈ nthRootsFinset d (1 : ℂ), conj (ζ ^ i) * ζ ^ j :=
      sum_congr rfl fun i _ => sum_comm
    _ = ∑ i ∈ range r, ∑ j ∈ range r, if i = j then (d : ℂ) else 0 := by
      refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
      exact sum_nthRoots_conj_pow_mul_pow hd ((mem_range.mp hi).trans_le hr)
        ((mem_range.mp hj).trans_le hr)
    _ = _ := by
      simp only [sum_ite_eq, mem_range, if_true]
      rw [sum_const, card_range, nsmul_eq_mul]
      ring

private theorem root_geometric_prefix_mod {d : ℕ} (hd : 0 < d) {ζ : ℂ}
    (hζ : ζ ^ d = 1) (hζ1 : ζ ≠ 1) (k : ℕ) :
    (∑ j ∈ range k, ζ ^ j) = ∑ j ∈ range (k % d), ζ ^ j := by
  have hpow : ζ ^ k = ζ ^ (k % d) := by
    conv_lhs => rw [← Nat.mod_add_div k d]
    rw [pow_add, pow_mul, hζ, one_pow, mul_one]
  apply mul_right_cancel₀ (sub_ne_zero.mpr hζ1)
  rw [geom_sum_mul, geom_sum_mul, hpow]

/-- The full root family has exactly the constant mode plus the quadratic
remainder of the prefix length modulo its order. -/
theorem nthRoots_prefix_energy {d : ℕ} (hd : 0 < d) (k : ℕ) :
    (∑ ζ ∈ nthRootsFinset d (1 : ℂ), Complex.normSq (∑ j ∈ range k, ζ ^ j)) =
      (k : ℝ) ^ 2 + (k % d : ℕ) * ((d : ℝ) - (k % d : ℕ)) := by
  have h1 : (1 : ℂ) ∈ nthRootsFinset d 1 := (mem_nthRootsFinset hd).mpr (one_pow d)
  have he : ∀ ζ ∈ nthRootsFinset d (1 : ℂ),
      Complex.normSq (∑ j ∈ range k, ζ ^ j) =
        Complex.normSq (∑ j ∈ range (k % d), ζ ^ j) +
          if ζ = 1 then (k : ℝ) ^ 2 - (k % d : ℕ) ^ 2 else 0 := by
    intro ζ hζ
    by_cases hζ1 : ζ = 1
    · subst ζ
      simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, if_true,
        Complex.normSq_natCast]
      ring
    · rw [root_geometric_prefix_mod hd ((mem_nthRootsFinset hd).mp hζ) hζ1,
        if_neg hζ1, add_zero]
  rw [sum_congr rfl he, sum_add_distrib,
    nthRoots_prefix_energy_of_le hd (Nat.mod_lt k hd).le, sum_ite_eq', if_pos h1]
  ring

private theorem nthRoots_prefix_energy_eq_sum_orders (d k : ℕ) :
    (∑ ζ ∈ nthRootsFinset d (1 : ℂ), Complex.normSq (∑ j ∈ range k, ζ ^ j)) =
      ∑ m ∈ d.divisors, primitiveRootPrefixEnergy m k := by
  have h := congrArg Complex.re
    (sum_nthRoots_eq_sum_divisors d (fun ζ =>
      ((Complex.normSq (∑ j ∈ range k, ζ ^ j) : ℝ) : ℂ)))
  simpa only [Complex.re_sum, Complex.ofReal_re, primitiveRootPrefixEnergy] using h

/-- Möbius inversion extracts the actual primitive-root energy from the
quadratic residue remainders, including the constant-order convention. -/
theorem primitiveRootPrefixEnergy_eq_moebius_antidiagonal {m : ℕ} (hm : 0 < m) (k : ℕ) :
    primitiveRootPrefixEnergy m k = ∑ p ∈ m.divisorsAntidiagonal,
      (ArithmeticFunction.moebius p.1 : ℝ) *
        ((k : ℝ) ^ 2 + (k % p.2 : ℕ) * ((p.2 : ℝ) - (k % p.2 : ℕ))) := by
  exact (((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => primitiveRootPrefixEnergy d k)
    (g := fun d => (k : ℝ) ^ 2 + (k % d : ℕ) * ((d : ℝ) - (k % d : ℕ)))).mp
      fun d hd => by
        rw [← nthRoots_prefix_energy_eq_sum_orders, nthRoots_prefix_energy hd]) m hm).symm

/-- At every positive order, the signed complete Möbius remainder is
nonnegative because it is the literal primitive-root square energy. -/
theorem moebius_quadratic_remainder_nonneg {m : ℕ} (hm : 0 < m) (k : ℕ) :
    0 ≤ ∑ p ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1 : ℝ) *
      ((k : ℝ) ^ 2 + (k % p.2 : ℕ) * ((p.2 : ℝ) - (k % p.2 : ℕ))) := by
  rw [← primitiveRootPrefixEnergy_eq_moebius_antidiagonal hm k]
  exact primitiveRootPrefixEnergy_nonneg m k

/-- A primitive prefix has positive energy whenever its length is not a
multiple of the conductor. One actual primitive root already detects it. -/
theorem primitiveRootPrefixEnergy_pos {m k : ℕ} (hm : 1 < m) (hkm : ¬ m ∣ k) :
    0 < primitiveRootPrefixEnergy m k := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)
  have hm0 : 0 < m := zero_lt_one.trans hm
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm0.ne'
  have hmem : ζ ∈ primitiveRoots m ℂ := (mem_primitiveRoots hm0).mpr hζ
  have hprefix : (∑ j ∈ range k, ζ ^ j) ≠ 0 := by
    intro hz
    have h := geom_sum_mul ζ k
    rw [hz, zero_mul] at h
    exact hkm (hζ.dvd_of_pow_eq_one k (sub_eq_zero.mp h.symm))
  have hpos : 0 < Complex.normSq (∑ j ∈ range k, ζ ^ j) :=
    (Complex.normSq_pos).mpr hprefix
  exact hpos.trans_le (single_le_sum (fun ξ _ => Complex.normSq_nonneg _) hmem)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.nthRoots_prefix_energy
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.primitiveRootPrefixEnergy_eq_moebius_antidiagonal
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.moebius_quadratic_remainder_nonneg
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.primitiveRootPrefixEnergy_pos
