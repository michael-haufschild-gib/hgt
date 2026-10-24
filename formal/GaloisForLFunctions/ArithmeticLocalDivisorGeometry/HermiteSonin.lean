import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteRootEdge

/-!
# Hermite critical-value geometry

A polynomial Sonin identity makes the outermost positive critical point the strict minimum
on the nonnegative axis. The proof retains exact critical values and excludes plateaus.
-/

open Polynomial Set
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- The Hermite ODE follows by differentiating the Gaussian raising relation. -/
theorem hermiteReal_ode (n : ℕ) :
    derivative (derivative (hermiteReal n)) - X * derivative (hermiteReal n) +
      C (n : ℝ) * hermiteReal n = 0 := by
  have h := congrArg derivative (hermiteReal_succ n)
  rw [derivative_hermiteReal_succ] at h
  simp only [gaussShift, derivative_sub, derivative_mul, derivative_X, one_mul, map_one] at h
  rw [map_add, map_one] at h
  linear_combination h

/-- A division-free Sonin polynomial for the Hermite equation. -/
def hermiteSonin (n : ℕ) : ℝ[X] :=
  C (n : ℝ) * hermiteReal n ^ 2 + derivative (hermiteReal n) ^ 2

/-- Sonin's derivative is a nonnegative square times the coordinate on the positive axis. -/
theorem derivative_hermiteSonin (n : ℕ) :
    derivative (hermiteSonin n) = C 2 * X * derivative (hermiteReal n) ^ 2 := by
  simp only [hermiteSonin, derivative_add, derivative_C_mul, derivative_pow,
    Nat.reduceSub, pow_one, Nat.cast_ofNat, map_ofNat]
  linear_combination 2 * derivative (hermiteReal n) * hermiteReal_ode n

theorem hermiteSonin_monotoneOn (n : ℕ) :
    MonotoneOn (hermiteSonin n).eval (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (hermiteSonin n).continuous.continuousOn (hermiteSonin n).differentiable.differentiableOn
  intro x hx
  have hx0 : 0 ≤ x := interior_subset hx
  rw [Polynomial.deriv, derivative_hermiteSonin]
  simp only [eval_mul, eval_C, eval_X, eval_pow]
  exact mul_nonneg (mul_nonneg (by norm_num) hx0) (sq_nonneg _)

/-- A polynomial monotone on a ray has no plateau unless it is constant. -/
private theorem strictMonoOn_polynomial_of_monotone {p : ℝ[X]} {a : ℝ}
    (hm : MonotoneOn p.eval (Ici a)) (hd : derivative p ≠ 0) :
    StrictMonoOn p.eval (Ici a) := by
  intro x hx y hy hxy
  have hle := hm hx hy hxy.le
  by_contra hn
  have heq : p.eval x = p.eval y := le_antisymm hle (le_of_not_gt hn)
  have hconst : p = C (p.eval x) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.Ioo_infinite hxy).mono
    intro z hz
    have hz0 : a ≤ z := hx.trans hz.1.le
    simp only [Set.mem_setOf_eq, eval_C]
    exact le_antisymm ((hm hz0 hy hz.2.le).trans heq.symm.le) (hm hx hz0 hz.1.le)
  exact hd (by rw [hconst, derivative_C])

/-- For positive Hermite degree, Sonin's quantity increases strictly on the positive axis. -/
theorem hermiteSonin_strictMonoOn (n : ℕ) :
    StrictMonoOn (hermiteSonin (n + 1)).eval (Ici 0) := by
  apply strictMonoOn_polynomial_of_monotone (hermiteSonin_monotoneOn (n + 1))
  intro hz
  have hx : 0 < hermiteEdge n + 1 := by linarith only [hermiteEdge_nonneg n]
  have hH : 0 < (hermiteReal n).eval (hermiteEdge n + 1) :=
    hermite_eval_pos_of_edge_lt (n := n) (by omega) (by linarith)
  have hd : 0 < (derivative (hermiteSonin (n + 1))).eval (hermiteEdge n + 1) := by
    rw [derivative_hermiteSonin, derivative_hermiteReal_succ]
    simp only [eval_mul, eval_C, eval_X, eval_pow]
    exact mul_pos (mul_pos (by norm_num) hx) (sq_pos_of_pos (mul_pos (by positivity) hH))
  rw [hz, eval_zero] at hd
  exact (lt_irrefl (0 : ℝ)) hd

/-- To the right of its outermost critical point, a Hermite polynomial increases strictly. -/
theorem hermite_strictMonoOn_right_edge (n : ℕ) :
    StrictMonoOn (hermiteReal (n + 2)).eval (Ici (hermiteEdge n)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (hermiteReal (n + 2)).continuous.continuousOn
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  rw [Polynomial.deriv, show n + 2 = (n + 1) + 1 by omega,
    derivative_hermiteReal_succ, eval_mul, eval_C]
  exact mul_pos (by positivity) (hermite_eval_pos_of_edge_lt (le_refl _) hx)

/-- The outermost positive critical value is the strict minimum on the nonnegative axis. -/
theorem hermite_edge_strict_min_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hne : x ≠ hermiteEdge n) :
    (hermiteReal (n + 2)).eval (hermiteEdge n) < (hermiteReal (n + 2)).eval x := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs := hermiteSonin_strictMonoOn (n + 1) hx (hermiteEdge_nonneg n) hlt
    have hd : (derivative (hermiteReal (n + 2))).eval (hermiteEdge n) = 0 := by
      rw [show n + 2 = (n + 1) + 1 by omega, derivative_hermiteReal_succ,
        eval_mul, eval_C, hermiteEdge_isRoot, mul_zero]
    change (hermiteSonin (n + 2)).eval x < (hermiteSonin (n + 2)).eval (hermiteEdge n) at hs
    simp only [hermiteSonin, eval_add, eval_mul, eval_C, eval_pow, hd,
      show (0 : ℝ) ^ 2 = 0 by ring, add_zero] at hs
    have hN : 0 < (n + 2 : ℕ) := by omega
    have hsquare : (hermiteReal (n + 2)).eval x ^ 2 <
        (hermiteReal (n + 2)).eval (hermiteEdge n) ^ 2 := by
      have hmul := (le_add_of_nonneg_right (sq_nonneg
        ((derivative (hermiteReal (n + 2))).eval x))).trans_lt hs
      exact (mul_lt_mul_iff_of_pos_left (by exact_mod_cast hN)).mp hmul
    nlinarith only [hsquare, hermite_eval_succ_edge_neg n]
  · exact hermite_strictMonoOn_right_edge n (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr hgt.le) hgt

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry

