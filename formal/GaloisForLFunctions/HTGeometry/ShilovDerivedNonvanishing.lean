import GaloisForLFunctions.HTGeometry.ShilovBoundaryMigrationDefect
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Derived non-vanishing for a surjective-cover tower

`ShilovBoundaryMigrationDefect.lean` shows that `lim¹` vanishes when the bonding maps are onto and,
separately, that it can vanish although no bonding map is onto.  The picture is completed here by
the missing direction: a countable tower whose bonding maps are **not** onto and whose `lim¹` is
**not** zero.

The tower is the polynomial ring at every stage with multiplication by `X` as every bond.  Solving
the Roos equation `xₙ - X·xₙ₊₁ = 1` forces `x₀` to have coefficient one in every degree, which no
polynomial has.

Consequently the derived acyclicity of a Shilov tower is not a formal consequence of having
surjective universal covers and vanishing escape: it is a statement about the Shilov ideals
themselves.
-/

namespace GaloisForLFunctions.HTGeometry

namespace BoundaryMigration

open Polynomial

variable (𝕜 : Type*) [Field 𝕜]

/-- Every stage of the polynomial tower is `𝕜[X]`. -/
abbrev polyStage : ℕ → Type _ := fun _ => Polynomial 𝕜

/-- Every bond of the polynomial tower is multiplication by `X`. -/
noncomputable def polyBond (n : ℕ) : polyStage 𝕜 (n + 1) →ₗ[𝕜] polyStage 𝕜 n :=
  LinearMap.mulLeft 𝕜 (X : Polynomial 𝕜)

theorem polyBond_apply (n : ℕ) (p : Polynomial 𝕜) :
    polyBond 𝕜 n p = X * p := rfl

/-- No bond of the polynomial tower is onto: multiplication by `X` misses the constants. -/
theorem not_surjective_polyBond (n : ℕ) : ¬ Function.Surjective (polyBond 𝕜 n) := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj 1
  have hcoeff := congrArg (fun q : Polynomial 𝕜 => q.coeff 0) hp
  simp [polyBond_apply, coeff_one] at hcoeff

/-- A solution of the Roos equation telescopes to a geometric partial sum. -/
theorem polyTower_telescope {x : ∀ n, polyStage 𝕜 n}
    (hx : ∀ n, x n - polyBond 𝕜 n (x (n + 1)) = 1) (m : ℕ) :
    x 0 = (∑ k ∈ Finset.range m, (X : Polynomial 𝕜) ^ k) + X ^ m * x m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep : x m = 1 + X * x (m + 1) := by
      have := hx m
      rw [polyBond_apply] at this
      linear_combination this
    rw [ih, hstep, Finset.sum_range_succ]
    ring

/-- **The polynomial tower has non-vanishing `lim¹`.**  Every solution of the Roos equation would
have coefficient one in every degree. -/
theorem not_subsingleton_derivedLimitOne_polyTower :
    ¬ Subsingleton (DerivedLimitOne (polyStage 𝕜) (polyBond 𝕜)) := by
  intro hsub
  have hrange : LinearMap.range (inverseDifference (polyStage 𝕜) (polyBond 𝕜)) = ⊤ := by
    rw [← Submodule.Quotient.subsingleton_iff]
    exact hsub
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp hrange (fun _ => (1 : Polynomial 𝕜))
  have hxn : ∀ n, x n - polyBond 𝕜 n (x (n + 1)) = 1 := fun n => congrFun hx n
  set d : ℕ := (x 0).natDegree + 1 with hd
  have hcoeff : (x 0).coeff d = 1 := by
    rw [polyTower_telescope 𝕜 hxn (d + 1), coeff_add]
    have h1 : (∑ k ∈ Finset.range (d + 1), (X : Polynomial 𝕜) ^ k).coeff d = 1 := by
      rw [finsetSum_coeff]
      simp [coeff_X_pow]
    have h2 : ((X : Polynomial 𝕜) ^ (d + 1) * x (d + 1)).coeff d = 0 := by
      rw [mul_comm, coeff_mul_X_pow']
      simp
    rw [h1, h2, add_zero]
  have hzero : (x 0).coeff d = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hzero] at hcoeff
  exact one_ne_zero hcoeff.symm

/-- **The completed independence picture.**  Linkwise non-surjectivity and global derived vanishing
are logically independent in both directions: `zero_scalar_bond_global_vanishing` gives a
non-surjective tower with vanishing `lim¹`, and the polynomial tower gives a non-surjective tower
with non-vanishing `lim¹`.  So no tower axiom alone decides derived acyclicity. -/
theorem polyTower_nonsurjective_and_nonvanishing :
    (∀ n : ℕ, ¬ Function.Surjective (polyBond 𝕜 n)) ∧
      ¬ Subsingleton (DerivedLimitOne (polyStage 𝕜) (polyBond 𝕜)) :=
  ⟨not_surjective_polyBond 𝕜, not_subsingleton_derivedLimitOne_polyTower 𝕜⟩

end BoundaryMigration

end GaloisForLFunctions.HTGeometry
