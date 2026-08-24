import GaloisForLFunctions.HTGeometry.RegularizedDeterminantAlgebraicMultiplicity

/-!
# Generalized eigenspaces of symmetric Hilbert-space operators

A symmetric operator has no nontrivial Jordan chains.  The proof below is algebraic and does not
use compactness: if `B^(n+1) x = 0`, then `B^n x` lies both in the range and kernel of the
symmetric operator `B`, hence has zero squared norm.  Descending induction reduces every
generalized eigenvector to an ordinary eigenvector.
-/

open Complex
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem apply_eq_zero_of_pow_apply_eq_zero_of_isSymmetric
    (B : E →ₗ[ℂ] E) (hB : B.IsSymmetric) (x : E) :
    ∀ n : ℕ, (B ^ n) x = 0 → B x = 0 := by
  intro n
  induction n with
  | zero =>
      intro hx
      simpa using congrArg B hx
  | succ n ih =>
      intro hx
      cases n with
      | zero => simpa using hx
      | succ n =>
          have hBy : B ((B ^ (n + 1)) x) = 0 := by
            simpa [pow_succ'] using hx
          have hy : (B ^ (n + 1)) x = 0 := by
            apply (inner_self_eq_zero (𝕜 := ℂ)).mp
            calc
              inner ℂ ((B ^ (n + 1)) x) ((B ^ (n + 1)) x) =
                  inner ℂ (B ((B ^ n) x)) ((B ^ (n + 1)) x) := by
                    rw [pow_succ']
                    rfl
              _ = inner ℂ ((B ^ n) x) (B ((B ^ (n + 1)) x)) :=
                hB ((B ^ n) x) ((B ^ (n + 1)) x)
              _ = 0 := by rw [hBy, inner_zero_right]
          exact ih hy

/-- A symmetric complex-linear operator has no nontrivial generalized eigenvectors at a real
spectral value.  Equivalently, its maximal generalized eigenspace is its ordinary eigenspace. -/
theorem maxGenEigenspace_eq_eigenspace_of_isSymmetric
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (mu : ℂ)
    (hmu : star mu = mu) :
    Module.End.maxGenEigenspace T mu = Module.End.eigenspace T mu := by
  apply le_antisymm
  · intro x hx
    rw [Module.End.mem_maxGenEigenspace] at hx
    rw [Module.End.mem_eigenspace_iff]
    rcases hx with ⟨n, hn⟩
    have hB : (T - mu • 1).IsSymmetric := by
      change (starRingEnd ℂ) mu = mu at hmu
      intro u v
      change inner ℂ (T u - mu • u) v = inner ℂ u (T v - mu • v)
      rw [inner_sub_left, inner_sub_right, hT u v,
        inner_smul_left, inner_smul_right, hmu]
    have hzero := apply_eq_zero_of_pow_apply_eq_zero_of_isSymmetric
      (T - mu • 1) hB x n hn
    exact sub_eq_zero.mp hzero
  · exact Module.End.eigenspace_le_maxGenEigenspace

end

end GaloisForLFunctions.HTGeometry
