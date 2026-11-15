import GaloisForLFunctions.RHTower.CausalMobiusThetaUniformCycle
import Mathlib.Algebra.BigOperators.Intervals


/-!
# Floor sums from reduced residues

Uniform residue cycles determine the sum of `Ri mod N`. If `1+mR`
is invertible modulo `N`, the remainders of `i+m(Ri mod N)` permute
the complete residue system. Summing Euclidean division then evaluates
the associated floor sum exactly.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Finset

/-- Reducing the branch multiplicity preserves the corresponding linear residue. -/
theorem reducedResidue_mod (N m R i : ℕ) :
    (i + m * (i * R % N)) % N = ((1 + m * R) * i) % N := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  conv_rhs => rw [add_mul, one_mul, mul_assoc m R i, Nat.mul_comm R i,
    Nat.add_mod, Nat.mul_mod]

/-- The sum of all multiplication residues is determined by the common divisor. -/
theorem two_mul_sum_mul_mod (N R : ℕ) (hN : 0 < N) :
    2 * (∑ i ∈ range N, R * i % N) = N * (N - Nat.gcd N R) := by
  by_cases hR : R = 0
  · subst R
    simp only [zero_mul, Nat.zero_mod, sum_const_zero, Nat.gcd_zero_right,
      Nat.sub_self, mul_zero]
  have hRpos : 0 < R := Nat.pos_of_ne_zero hR
  let g := Nat.gcd R N
  let T := N / g
  have hNT : N = g * T := (Nat.mul_div_cancel' (Nat.gcd_dvd_right R N)).symm
  have hRfactor : R = g * (R / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left R N)).symm
  have hRT : R * T = (R / g) * N := by
    conv_lhs => rw [hRfactor]
    rw [hNT]
    ring
  have hperiod (i : ℕ) : R * (i + T) % N = R * i % N := by
    rw [mul_add, hRT, Nat.mul_comm (R / g) N, Nat.add_mul_mod_self_left]
  have hrepeat : (∑ i ∈ range N, R * i % N) = g * ∑ i ∈ range T, R * i % N := by
    have h := RHTower.sum_range_mul_period_eq
      (F := fun i => ((R * i % N : ℕ) : ℝ)) (n := T)
      (fun i => by rw [hperiod]) g
    rw [show T * g = N by rw [hNT, mul_comm]] at h
    exact_mod_cast h
  have hcycle : (∑ i ∈ range T, R * i % N) = g * ∑ i ∈ range T, i := by
    simpa only [Nat.zero_mod, zero_add, mul_zero] using
      (RHTower.sum_range_add_mul_mod_eq_gcd (c := 0) hN hRpos)
  rw [hrepeat, hcycle, Nat.gcd_comm N R]
  change 2 * (g * (g * ∑ i ∈ range T, i)) = N * (N - g)
  calc
    2 * (g * (g * ∑ i ∈ range T, i)) =
        g * g * ((∑ i ∈ range T, i) * 2) := by ring
    _ = g * g * (T * (T - 1)) := by rw [sum_range_id_mul_two]
    _ = N * (N - g) := by
      have hsub : g * (T - 1) = N - g := by
        rw [Nat.mul_sub_left_distrib, mul_one, ← hNT]
      calc
        g * g * (T * (T - 1)) = (g * T) * (g * (T - 1)) := by ring
        _ = N * (N - g) := by rw [← hNT, hsub]

/-- Complete residue permutation evaluates the reduced-divisor floor sum. -/
theorem two_mul_sum_reducedResidue_floor (N m R : ℕ) (hN : 0 < N)
    (hcop : Nat.Coprime (1 + m * R) N) :
    2 * (∑ i ∈ range N, (i + m * (i * R % N)) / N) =
      m * (N - Nat.gcd N R) := by
  let D : ℕ → ℕ := fun i => i + m * (i * R % N)
  have hmod (i : ℕ) : D i % N = ((1 + m * R) * i) % N := reducedResidue_mod N m R i
  have hremainder : (∑ i ∈ range N, D i % N) = ∑ i ∈ range N, i := by
    simp_rw [hmod]
    simpa only [zero_add] using RHTower.sum_range_add_mul_mod_eq hN hcop 0
  have hdivision : N * (∑ i ∈ range N, D i / N) + (∑ i ∈ range N, i) =
      (∑ i ∈ range N, i) + m * (∑ i ∈ range N, R * i % N) := by
    conv_lhs => rw [← hremainder]
    rw [mul_sum, ← sum_add_distrib]
    have hterm : ∀ i, N * (D i / N) + D i % N = D i := fun i => Nat.div_add_mod (D i) N
    simp_rw [hterm]
    dsimp only [D]
    rw [sum_add_distrib, mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [Nat.mul_comm i R]
  have hcancel : N * (∑ i ∈ range N, D i / N) =
      m * (∑ i ∈ range N, R * i % N) := by omega
  apply Nat.eq_of_mul_eq_mul_left hN
  change N * (2 * ∑ i ∈ range N, D i / N) = N * (m * (N - Nat.gcd N R))
  calc
    N * (2 * ∑ i ∈ range N, D i / N) = 2 * (N * ∑ i ∈ range N, D i / N) := by ring
    _ = m * (2 * ∑ i ∈ range N, R * i % N) := by rw [hcancel]; ring
    _ = N * (m * (N - Nat.gcd N R)) := by rw [two_mul_sum_mul_mod N R hN]; ring

/-- The nonzero character residues turn the pole-order inequality into an exact degree cutoff. -/
theorem reducedResidue_cutoff_iff (N m R : ℕ) (hN : 0 < N)
    (hcop : Nat.Coprime (1 + m * R) N) (i : Fin N) (k : ℕ) :
    N * (k + 1) + 1 ≤ i.val + m * (i.val * R % N) ↔
      k < (i.val + m * (i.val * R % N)) / N := by
  let D := i.val + m * (i.val * R % N)
  change N * (k + 1) + 1 ≤ D ↔ k < D / N
  constructor
  · intro h
    apply Nat.lt_of_succ_le
    apply (Nat.le_div_iff_mul_le hN).mpr
    have hle : N * (k + 1) ≤ D := by omega
    simpa only [Nat.mul_comm] using hle
  · intro h
    have hle : N * (k + 1) ≤ D := by
      have h' := (Nat.le_div_iff_mul_le hN).mp (Nat.succ_le_of_lt h)
      simpa only [Nat.mul_comm] using h'
    by_contra hbad
    have heq : D = N * (k + 1) := by omega
    have hmod : D % N = 0 := Nat.mod_eq_zero_of_dvd ⟨k + 1, heq⟩
    change (i.val + m * (i.val * R % N)) % N = 0 at hmod
    rw [reducedResidue_mod] at hmod
    have hdiv : N ∣ i.val := hcop.symm.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero hmod)
    have hi0 : i.val = 0 := by
      by_contra hi
      exact (not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hi) hdiv)) i.isLt
    have hD0 : D = 0 := by simp only [D, hi0, zero_mul, Nat.zero_mod, mul_zero, zero_add]
    rw [hD0] at hle
    exact (not_lt_of_ge hle) (Nat.mul_pos hN (Nat.succ_pos k))

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
