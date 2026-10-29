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

open ArithmeticEffectivityTheory ArithmeticFunction

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
      simpa only [Nat.sub_add_cancel hi.le] using (dvd_refl d)
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
    _ = ∑ _i ∈ range r, (d : ℂ) := by
      exact sum_congr rfl fun i hi => by rw [sum_ite_eq, if_pos hi]
    _ = _ := by
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
          if ζ = 1 then (k : ℝ) ^ 2 - ((k % d : ℕ) : ℝ) ^ 2 else 0 := by
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

private theorem sum_antidiagonal_moebius (m : ℕ) :
    (∑ p ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1 : ℝ)) =
      if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f m)
    (coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [mul_apply, one_apply] at h
  rw [← h]
  refine sum_congr rfl fun p hp => ?_
  rw [intCoe_apply, natCoe_apply, zeta_apply_ne (Nat.pos_of_mem_divisors
    (Nat.snd_mem_divisors_of_mem_antidiagonal hp)).ne', Nat.cast_one, mul_one]

/-- At nontrivial conductor the constant mode cancels exactly. The remaining
signed quadratic residue sum is the actual primitive-root energy. -/
theorem primitiveRootPrefixEnergy_eq_moebius_remainder {m : ℕ} (hm : 1 < m) (k : ℕ) :
    primitiveRootPrefixEnergy m k = ∑ d ∈ m.divisors,
      (ArithmeticFunction.moebius (m / d) : ℝ) * (k % d : ℕ) *
        ((d : ℝ) - (k % d : ℕ)) := by
  have hzero : (∑ p ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1 : ℝ)) = 0 := by
    rw [sum_antidiagonal_moebius, if_neg (by omega)]
  calc
    _ = ∑ p ∈ m.divisorsAntidiagonal,
        (ArithmeticFunction.moebius p.1 : ℝ) * (k : ℝ) ^ 2 +
          (ArithmeticFunction.moebius p.1 : ℝ) *
            ((k % p.2 : ℕ) * ((p.2 : ℝ) - (k % p.2 : ℕ))) := by
      rw [primitiveRootPrefixEnergy_eq_moebius_antidiagonal (zero_lt_one.trans hm)]
      exact sum_congr rfl fun p _ => by ring
    _ = ∑ p ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1 : ℝ) *
        ((k % p.2 : ℕ) * ((p.2 : ℝ) - (k % p.2 : ℕ))) := by
      rw [sum_add_distrib, ← sum_mul, hzero, zero_mul, zero_add]
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal' (fun a b => (ArithmeticFunction.moebius a : ℝ) *
        ((k % b : ℕ) * ((b : ℝ) - (k % b : ℕ))))]
      exact sum_congr rfl fun d _ => by ring

/-- Möbius extraction preserves positivity for the actual quadratic
remainder, although its divisor coefficients have both signs. -/
theorem moebius_residue_quadratic_nonneg {m : ℕ} (hm : 1 < m) (k : ℕ) :
    0 ≤ ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) *
      (k % d : ℕ) * ((d : ℝ) - (k % d : ℕ)) := by
  rw [← primitiveRootPrefixEnergy_eq_moebius_remainder hm]
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

/-- The nonzero energy has an arithmetic quantum: its exact Möbius formula
is an integer, so positivity already gives a lower bound of one. -/
theorem one_le_primitiveRootPrefixEnergy {m k : ℕ} (hm : 1 < m) (hkm : ¬ m ∣ k) :
    1 ≤ primitiveRootPrefixEnergy m k := by
  let z : ℤ := ∑ d ∈ m.divisors, ArithmeticFunction.moebius (m / d) *
    (k % d : ℕ) * ((d : ℤ) - (k % d : ℕ))
  have he : primitiveRootPrefixEnergy m k = (z : ℝ) := by
    rw [primitiveRootPrefixEnergy_eq_moebius_remainder hm]
    simp only [z, Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_natCast]
  have hz : 0 < z := by
    have hp := primitiveRootPrefixEnergy_pos hm hkm
    rw [he] at hp
    exact_mod_cast hp
  rw [he]
  exact_mod_cast (show (1 : ℤ) ≤ z by omega)

/-- Conductor multiples are exactly the vanishing prefix lengths. -/
theorem primitiveRootPrefixEnergy_eq_zero_iff {m : ℕ} (hm : 1 < m) (k : ℕ) :
    primitiveRootPrefixEnergy m k = 0 ↔ m ∣ k := by
  constructor
  · intro hz
    by_contra hkm
    exact (primitiveRootPrefixEnergy_pos hm hkm).ne' hz
  · intro hkm
    rw [primitiveRootPrefixEnergy_eq_moebius_remainder hm]
    exact sum_eq_zero fun d hd => by
      rw [Nat.mod_eq_zero_of_dvd ((Nat.dvd_of_mem_divisors hd).trans hkm),
        Nat.cast_zero, mul_zero, zero_mul]

/-- The signed quadratic remainder on a real cell of the integer lattice. -/
def primitiveQuadraticCell (m k : ℕ) (u : ℝ) : ℝ :=
  ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) *
    ((k % d : ℕ) + u) * ((d : ℝ) - (k % d : ℕ) - u)

private theorem primitiveQuadraticCell_zero {m : ℕ} (hm : 1 < m) (k : ℕ) :
    primitiveQuadraticCell m k 0 = primitiveRootPrefixEnergy m k := by
  rw [primitiveQuadraticCell, primitiveRootPrefixEnergy_eq_moebius_remainder hm]
  simp only [add_zero, sub_zero]

private theorem quadratic_residue_succ {d : ℕ} (hd : 0 < d) (k : ℕ) :
    (((k % d : ℕ) : ℝ) + 1) * ((d : ℝ) - (k % d : ℕ) - 1) =
      ((k + 1) % d : ℕ) * ((d : ℝ) - ((k + 1) % d : ℕ)) := by
  have hstep : k + 1 = (k % d + 1) + d * (k / d) := by
    have h := Nat.mod_add_div k d
    omega
  rw [hstep, Nat.add_mul_mod_self_left]
  have hr := Nat.mod_lt k hd
  by_cases hlt : k % d + 1 < d
  · rw [Nat.mod_eq_of_lt hlt]
    push_cast
    ring
  · have heq : k % d + 1 = d := by omega
    have heqR : ((k % d : ℕ) : ℝ) + 1 = d := by exact_mod_cast heq
    rw [heq, Nat.mod_self, Nat.cast_zero, zero_mul, ← heqR]
    ring

private theorem primitiveQuadraticCell_one {m : ℕ} (hm : 1 < m) (k : ℕ) :
    primitiveQuadraticCell m k 1 = primitiveRootPrefixEnergy m (k + 1) := by
  rw [primitiveQuadraticCell, primitiveRootPrefixEnergy_eq_moebius_remainder hm]
  refine sum_congr rfl fun d hd => ?_
  have h := quadratic_residue_succ (Nat.pos_of_mem_divisors hd) k
  linear_combination (ArithmeticFunction.moebius (m / d) : ℝ) * h

/-- Möbius cancellation removes the curvature within each lattice cell:
the signed quadratic expression is a convex interpolation of actual energies. -/
theorem primitiveQuadraticCell_eq_interpolation {m : ℕ} (hm : 1 < m) (k : ℕ) (u : ℝ) :
    primitiveQuadraticCell m k u =
      (1 - u) * primitiveRootPrefixEnergy m k + u * primitiveRootPrefixEnergy m (k + 1) := by
  have hzero : (∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ)) = 0 := by
    calc
      _ = ∑ p ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1 : ℝ) :=
        (Nat.sum_divisorsAntidiagonal' (fun a _b => (ArithmeticFunction.moebius a : ℝ))).symm
      _ = 0 := by rw [sum_antidiagonal_moebius, if_neg (by omega)]
  have hid : primitiveQuadraticCell m k u =
      (1 - u) * primitiveQuadraticCell m k 0 + u * primitiveQuadraticCell m k 1 +
        u * (1 - u) * ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) := by
    simp only [primitiveQuadraticCell, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun d _ => by ring
  rw [hzero, mul_zero, add_zero, primitiveQuadraticCell_zero hm,
    primitiveQuadraticCell_one hm] at hid
  exact hid

/-- Every real lattice cell has nonnegative primitive arithmetic curvature. -/
theorem primitiveQuadraticCell_nonneg {m : ℕ} (hm : 1 < m) (k : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ primitiveQuadraticCell m k u := by
  rw [primitiveQuadraticCell_eq_interpolation hm]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hu1) (primitiveRootPrefixEnergy_nonneg _ _))
    (mul_nonneg hu0 (primitiveRootPrefixEnergy_nonneg _ _))

/-- A nonvanishing primitive prefix gives strict curvature throughout the
cell up to its right endpoint. -/
theorem primitiveQuadraticCell_pos {m k : ℕ} (hm : 1 < m) (hkm : ¬ m ∣ k)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : 0 < primitiveQuadraticCell m k u := by
  rw [primitiveQuadraticCell_eq_interpolation hm]
  exact add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr hu1) (primitiveRootPrefixEnergy_pos hm hkm))
    (mul_nonneg hu0 (primitiveRootPrefixEnergy_nonneg _ _))

/-- The signed divisor curvature of the arithmetic overlap symbol. -/
def arithmeticOverlapCurvature (m : ℕ) (t : ℝ) : ℝ :=
  ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * (d : ℝ) ^ 2 *
    Int.fract (t / d) * (1 - Int.fract (t / d))

private theorem fract_div_on_nat_cell {d : ℕ} (hd : 0 < d) (k : ℕ)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Int.fract (((k : ℝ) + u) / d) = (((k % d : ℕ) : ℝ) + u) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmod : ((k % d : ℕ) : ℝ) + (d : ℝ) * (k / d : ℕ) = k := by
    exact_mod_cast Nat.mod_add_div k d
  have he : ((k : ℝ) + u) / d =
      (((k % d : ℕ) : ℝ) + u) / d + (k / d : ℕ) := by
    apply (div_eq_iff hdR.ne').mpr
    rw [add_mul, div_mul_cancel₀ _ hdR.ne']
    linarith only [hmod]
  rw [he, Int.fract_add_natCast]
  apply Int.fract_eq_self.mpr
  refine ⟨div_nonneg (add_nonneg (Nat.cast_nonneg _) hu0) hdR.le, ?_⟩
  rw [div_lt_one hdR]
  have hr : ((k % d : ℕ) : ℝ) + 1 ≤ d := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mod_lt k hd)
  linarith only [hr, hu1]

/-- On every nonnegative unit cell, the fractional-part formula is exactly
the finite Möbius remainder; there is no asymptotic substitution. -/
theorem arithmeticOverlapCurvature_eq_cell (m k : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    arithmeticOverlapCurvature m ((k : ℝ) + u) = primitiveQuadraticCell m k u := by
  unfold arithmeticOverlapCurvature primitiveQuadraticCell
  refine sum_congr rfl fun d hd => ?_
  have hd0 := Nat.pos_of_mem_divisors hd
  rw [fract_div_on_nat_cell hd0 k hu0 hu1]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  field_simp [hdR]
  <;> ring

/-- The actual signed fractional-part curvature is a convex interpolation
of primitive-root square energies at every nontrivial conductor. -/
theorem arithmeticOverlapCurvature_eq_interpolation {m : ℕ} (hm : 1 < m)
    (k : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    arithmeticOverlapCurvature m ((k : ℝ) + u) =
      (1 - u) * primitiveRootPrefixEnergy m k + u * primitiveRootPrefixEnergy m (k + 1) := by
  rw [arithmeticOverlapCurvature_eq_cell m k hu0 hu1,
    primitiveQuadraticCell_eq_interpolation hm]

/-- Signed arithmetic curvature is nonnegative on every real unit cell. -/
theorem arithmeticOverlapCurvature_cell_nonneg {m : ℕ} (hm : 1 < m) (k : ℕ)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    0 ≤ arithmeticOverlapCurvature m ((k : ℝ) + u) := by
  rw [arithmeticOverlapCurvature_eq_cell m k hu0 hu1]
  exact primitiveQuadraticCell_nonneg hm k hu0 hu1.le

/-- Integer quantization gives a positive common cell bound for every
nontrivial conductor, before division by its totient. -/
theorem arithmeticOverlapCurvature_cell_lower {m : ℕ} (hm : 1 < m) (k : ℕ)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u * (1 - u) ≤ arithmeticOverlapCurvature m ((k : ℝ) + u) := by
  rw [arithmeticOverlapCurvature_eq_interpolation hm k hu0 hu1]
  by_cases hkm : m ∣ k
  · have hnext : ¬ m ∣ k + 1 := by
      intro h
      have hm1 : m ∣ 1 := (Nat.dvd_add_iff_right hkm).mp h
      exact (by omega : m ≠ 1) (Nat.dvd_one.mp hm1)
    have hE := one_le_primitiveRootPrefixEnergy hm hnext
    have hmul := mul_le_mul_of_nonneg_left hE hu0
    have hn := mul_nonneg (sub_nonneg.mpr hu1.le) (primitiveRootPrefixEnergy_nonneg m k)
    nlinarith only [hmul, hn, sq_nonneg u]
  · have hE := one_le_primitiveRootPrefixEnergy hm hkm
    have hmul := mul_le_mul_of_nonneg_left hE (sub_nonneg.mpr hu1.le)
    have hn := mul_nonneg hu0 (primitiveRootPrefixEnergy_nonneg m (k + 1))
    nlinarith only [hmul, hn, sq_nonneg (1 - u)]

/-- Every nontrivial conductor dominates the same positive fractional-part
curvature on the whole nonnegative real axis. -/
theorem fract_mul_one_sub_fract_le_arithmeticOverlapCurvature {m : ℕ} (hm : 1 < m)
    {t : ℝ} (ht : 0 ≤ t) :
    Int.fract t * (1 - Int.fract t) ≤ arithmeticOverlapCurvature m t := by
  let k : ℕ := ⌊t⌋₊
  let u : ℝ := t - k
  have hu0 : 0 ≤ u := sub_nonneg.mpr (Nat.floor_le ht)
  have hu1 : u < 1 := by
    have h := Nat.lt_floor_add_one t
    dsimp only [u, k]
    linarith only [h]
  have he : t = (k : ℝ) + u := by dsimp only [u]; ring
  have hf : Int.fract t = u := by
    rw [he, add_comm, Int.fract_add_natCast]
    exact Int.fract_eq_self.mpr ⟨hu0, hu1⟩
  rw [hf, he]
  exact arithmeticOverlapCurvature_cell_lower hm k hu0 hu1

/-- The original signed fractional-part divisor expression is nonnegative,
with no assumption about zeros or about the spectrum of an operator. -/
theorem arithmeticOverlapCurvature_nonneg {m : ℕ} (hm : 1 < m)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ arithmeticOverlapCurvature m t := by
  exact (mul_nonneg (Int.fract_nonneg t) (sub_nonneg.mpr (Int.fract_lt_one t).le)).trans
    (fract_mul_one_sub_fract_le_arithmeticOverlapCurvature hm ht)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.primitiveRootPrefixEnergy_eq_moebius_remainder
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.moebius_residue_quadratic_nonneg
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.primitiveRootPrefixEnergy_pos
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.primitiveQuadraticCell_eq_interpolation
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.primitiveQuadraticCell_pos
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.arithmeticOverlapCurvature_eq_interpolation
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.fract_mul_one_sub_fract_le_arithmeticOverlapCurvature
