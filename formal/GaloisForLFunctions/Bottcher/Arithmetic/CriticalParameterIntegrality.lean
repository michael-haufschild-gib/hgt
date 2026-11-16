import GaloisForLFunctions.Bottcher.Arithmetic.UnicriticalOrbitBounds
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Integral parameters from finite critical orbits

Successive critical iterates are monic integral polynomials in the parameter,
with strictly increasing degrees. Any collision gives a monic equation for
the parameter. The conclusion holds in every field, without a number-field
or algebraicity premise.
-/

noncomputable section
namespace Bottcher.Arithmetic
open Polynomial Set

/-- The critical iterate as an integral polynomial in the parameter. -/
def criticalParameterPoly (d : ℕ) : ℕ → ℤ[X]
  | 0 => 0
  | n + 1 => criticalParameterPoly d n ^ (d + 2) + X

/-- The parameter polynomial evaluates to the actual critical iterate. -/
theorem criticalParameterPoly_eval {K : Type*} [Field K]
    (d : ℕ) (c : K) (n : ℕ) :
    (criticalParameterPoly d n).eval₂ (Int.castRingHom K) c = criticalOrbit d c n := by
  induction n with
  | zero => simp only [criticalParameterPoly, eval₂_zero, criticalOrbit_zero]
  | succ n ih => simp only [criticalParameterPoly, eval₂_add, eval₂_pow,
      eval₂_X, ih, criticalOrbit_succ]

/-- Positive critical iterates are monic with degree `(d+2)^n`. -/
theorem criticalParameterPoly_monic_degree (d n : ℕ) :
    IsMonicOfDegree (criticalParameterPoly d (n + 1)) ((d + 2) ^ n) := by
  induction n with
  | zero =>
    simp only [criticalParameterPoly, zero_pow (by omega : d + 2 ≠ 0), zero_add, pow_zero]
    exact isMonicOfDegree_X ℤ
  | succ n ih =>
    have hp : 0 < (d + 2) ^ n := pow_pos (by omega) n
    have hx : (X : ℤ[X]).natDegree < (d + 2) ^ n * (d + 2) := by
      rw [natDegree_X]
      nlinarith only [hp, show 2 ≤ d + 2 by omega]
    simpa only [criticalParameterPoly, pow_succ] using (ih.pow (d + 2)).add_right hx

/-- Distinct iterate indices give distinct degrees in parameter space. -/
theorem criticalParameterPoly_degree_strictMono (d : ℕ) :
    StrictMono (fun n => (criticalParameterPoly d n).natDegree) := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero =>
    rw [(criticalParameterPoly_monic_degree d 0).natDegree_eq]
    simp only [criticalParameterPoly, natDegree_zero, pow_zero, Nat.zero_lt_one]
  | succ n =>
    rw [(criticalParameterPoly_monic_degree d n).natDegree_eq,
      (criticalParameterPoly_monic_degree d (n + 1)).natDegree_eq]
    exact Nat.pow_lt_pow_right (by omega) (by omega)

private theorem integral_of_critical_collision {K : Type*} [Field K]
    (d : ℕ) (c : K) {m n : ℕ} (hmn : m < n)
    (heq : criticalOrbit d c m = criticalOrbit d c n) : IsIntegral ℤ c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hd := criticalParameterPoly_degree_strictMono d hmn
  have hpoly : (criticalParameterPoly d (k + 1) - criticalParameterPoly d m).Monic := by
    rw [sub_eq_add_neg]
    apply ((criticalParameterPoly_monic_degree d k).add_right ?_).monic
    simpa only [natDegree_neg, (criticalParameterPoly_monic_degree d k).natDegree_eq] using hd
  refine ⟨criticalParameterPoly d (k + 1) - criticalParameterPoly d m, hpoly, ?_⟩
  change eval₂ (Int.castRingHom K) c
    (criticalParameterPoly d (k + 1) - criticalParameterPoly d m) = 0
  rw [eval₂_sub, criticalParameterPoly_eval, criticalParameterPoly_eval, ← heq, sub_self]

/-- A transcendental parameter has a collision-free critical orbit. -/
theorem criticalOrbit_injective_or_integral {K : Type*} [Field K] (d : ℕ) (c : K) :
    Function.Injective (criticalOrbit d c) ∨ IsIntegral ℤ c := by
  by_cases hi : Function.Injective (criticalOrbit d c)
  · exact Or.inl hi
  · right
    obtain ⟨m, n, heq, hne⟩ := Function.not_injective_iff.mp hi
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact integral_of_critical_collision d c hlt heq
    · exact integral_of_critical_collision d c hgt heq.symm

/-- Every parameter has an infinite critical orbit or is an algebraic integer. -/
theorem criticalOrbit_infinite_or_integral {K : Type*} [Field K] (d : ℕ) (c : K) :
    (range (criticalOrbit d c)).Infinite ∨ IsIntegral ℤ c := by
  exact (criticalOrbit_injective_or_integral d c).imp infinite_range_of_injective id

end Bottcher.Arithmetic

