import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite ultrametric thermal truncation residual

Finite prefixes of the ultrametric thermal shell tower have an exact scale defect.  A prefix with
`N` positive shells obeys the infinite affine Mahler constraint up to precisely its next omitted
shell.  Thus finite resolution does not create an uncontrolled remainder: the constraint residual
is an exact boundary term.

The result is algebraic over an arbitrary field.  It does not assert convergence,
hypertranscendence, a de Sitter detector realization, or an infinite-spectrum limit.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- Positive ultrametric shell `k`, corresponding to spectral level `k + 1`. -/
def ultrametricThermalShell
    {K : Type*} [Field K] (p : ℕ) (w : K) (k : ℕ) : K :=
  (((p : K) - 1) ^ 2) * (p : K) ^ k * w ^ (p ^ (k + 1))

/-- The reduced ultrametric thermal trace with its base shell and the first `N` positive shells. -/
def ultrametricThermalTruncation
    {K : Type*} [Field K] (p : ℕ) (w : K) (N : ℕ) : K :=
  ((p : K) - 2) * w +
    ∑ k ∈ Finset.range N, ultrametricThermalShell p w k

@[simp]
theorem ultrametricThermalTruncation_zero
    {K : Type*} [Field K] (p : ℕ) (w : K) :
    ultrametricThermalTruncation p w 0 = ((p : K) - 2) * w := by
  simp [ultrametricThermalTruncation]

/-- Scaling the reporter coordinate shifts one positive shell and contributes one factor of `p`. -/
theorem ultrametricThermalShell_succ_eq_scale
    {K : Type*} [Field K] (p : ℕ) (w : K) (k : ℕ) :
    ultrametricThermalShell p w (k + 1) =
      (p : K) * ultrametricThermalShell p (w ^ p) k := by
  unfold ultrametricThermalShell
  rw [show (p : K) ^ (k + 1) = (p : K) ^ k * (p : K) by
    exact pow_succ _ _]
  rw [show (w ^ p) ^ (p ^ (k + 1)) = w ^ (p ^ (k + 2)) by
    rw [← pow_mul]
    congr 1
    calc
      p * p ^ (k + 1) = p ^ (k + 1) * p := Nat.mul_comm _ _
      _ = p ^ ((k + 1) + 1) := (pow_succ _ _).symm
      _ = p ^ (k + 2) := by congr 1]
  ring

/-- **Exact finite scale constraint.**  Adding one resolved shell is equivalent to applying the
scale substitution to the preceding prefix and restoring the two boundary terms. -/
theorem ultrametricThermalTruncation_succ_constraint
    {K : Type*} [Field K] (p : ℕ) (w : K) (N : ℕ) :
    ultrametricThermalTruncation p w (N + 1) =
      ((p : K) - 2) * w + w ^ p +
        (p : K) * ultrametricThermalTruncation p (w ^ p) N := by
  rw [ultrametricThermalTruncation, Finset.sum_range_succ']
  rw [ultrametricThermalTruncation]
  simp_rw [ultrametricThermalShell_succ_eq_scale]
  rw [← Finset.mul_sum]
  simp only [ultrametricThermalShell]
  ring

/-- The difference of consecutive finite resolutions is exactly the newly resolved shell. -/
theorem ultrametricThermalTruncation_succ_sub
    {K : Type*} [Field K] (p : ℕ) (w : K) (N : ℕ) :
    ultrametricThermalTruncation p w (N + 1) -
        ultrametricThermalTruncation p w N =
      ultrametricThermalShell p w N := by
  rw [ultrametricThermalTruncation, ultrametricThermalTruncation,
    Finset.sum_range_succ]
  ring

/-- **Finite-resolution residual.**  Applying the infinite affine scale constraint to an
`N`-shell prefix fails by exactly the negative of the next omitted shell. -/
theorem ultrametricThermalTruncation_constraint_residual
    {K : Type*} [Field K] (p : ℕ) (w : K) (N : ℕ) :
    ultrametricThermalTruncation p w N -
        (((p : K) - 2) * w + w ^ p +
          (p : K) * ultrametricThermalTruncation p (w ^ p) N) =
      -ultrametricThermalShell p w N := by
  rw [← ultrametricThermalTruncation_succ_constraint p w N,
    ← ultrametricThermalTruncation_succ_sub p w N]
  ring

end GaloisForLFunctions.HTGeometry
