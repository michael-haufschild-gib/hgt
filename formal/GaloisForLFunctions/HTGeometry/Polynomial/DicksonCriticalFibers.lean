import GaloisForLFunctions.HTGeometry.Polynomial.ChebyshevDifferential
import GaloisForLFunctions.HTGeometry.SpecialMapFixedPointMultiplier
import Mathlib.FieldTheory.Separable

/-!
# Critical fibers of the normalized Chebyshev maps

The differential energy identity supplies an explicit Bézout certificate
for separability in every positive degree in characteristic zero. It also
confines critical values to the two points `2` and `-2`.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial

/-- All positive-degree normalized Chebyshev polynomials are separable in characteristic zero. -/
theorem dickson_separable_succ {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    (dickson 1 (1 : K) (n + 1)).Separable := by
  have hn : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hc : (4 * ((n + 1 : ℕ) : K) ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hn)
  have hcancel : C ((4 * ((n + 1 : ℕ) : K) ^ 2)⁻¹) *
      (4 * ((n + 1 : ℕ) : K[X]) ^ 2) = 1 := by
    have h := congrArg (C : K → K[X]) (inv_mul_cancel₀ hc)
    simpa only [C_mul, C_pow, C_ofNat, C_eq_natCast, C_1] using h
  refine ⟨C ((4 * ((n + 1 : ℕ) : K) ^ 2)⁻¹) *
      ((n + 1 : ℕ) : K[X]) ^ 2 * dickson 1 1 (n + 1),
    -C ((4 * ((n + 1 : ℕ) : K) ^ 2)⁻¹) * (X ^ 2 - 4) *
      (dickson 1 1 (n + 1)).derivative, ?_⟩
  linear_combination
    -C ((4 * ((n + 1 : ℕ) : K) ^ 2)⁻¹) * dickson_differential_energy (R := K) (n + 1) +
      hcancel

/-- Every critical value of a positive-degree Dickson map belongs to `{2,-2}`. -/
theorem dicksonMap_critical_values (n : ℕ) :
    Set.MapsTo (dicksonMap (n + 1))
      {z | (dickson 1 (1 : ℂ) (n + 1)).derivative.eval z = 0} {2, -2} := by
  intro z hz
  change (dickson 1 (1 : ℂ) (n + 1)).derivative.eval z = 0 at hz
  have h := congrArg (Polynomial.eval z) (dickson_differential_energy (R := ℂ) (n + 1))
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_ofNat, eval_natCast, hz,
    zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero] at h
  have hn : (((n + 1 : ℕ) : ℂ) ^ 2) ≠ 0 :=
    pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
  have hsq := (mul_eq_zero.mp h.symm).resolve_left hn
  have hfac : ((dickson 1 (1 : ℂ) (n + 1)).eval z - 2) *
      ((dickson 1 (1 : ℂ) (n + 1)).eval z + 2) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with hp | hm
  · exact Or.inl (sub_eq_zero.mp hp)
  · exact Or.inr (eq_neg_of_add_eq_zero_left hm)

/-- The map composition law yields exact multiplication of degrees. -/
theorem dicksonMap_comp (m n : ℕ) (z : ℂ) :
    dicksonMap m (dicksonMap n z) = dicksonMap (m * n) z := by
  simp only [dicksonMap, dickson_one_one_mul, eval_comp]

/-- Iterating one Dickson map raises its degree to the iteration index. -/
theorem dicksonMap_iterate (m k : ℕ) : (dicksonMap m)^[k] = dicksonMap (m ^ k) := by
  induction k with
  | zero =>
    funext z
    simp only [Function.iterate_zero_apply, pow_zero, dicksonMap, dickson_one, eval_X]
  | succ k ih =>
    funext z
    rw [Function.iterate_succ_apply', ih, dicksonMap_comp, pow_succ, Nat.mul_comm]

end GaloisForLFunctions.HTGeometry
