import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Vandermonde vanishing lemma (task03, Lemma 1 core)

The algebraic heart of the dyadic-monodromy transcendence and algebraic-independence arguments.
If a monodromy multiplies the coordinate by a root of unity `ζ` of order `> d`, analytically
continuing a degree-`d` relation `r` times yields the linear system

`∑_{j=0}^{d} a_j · ζ^{r·j} = 0`   for `r = 0, …, d`,

whose coefficient matrix `(ζ^{r j})_{r,j} = ((ζ^r)^j)` is Vandermonde in the nodes `ζ^r`.  Distinct
nodes (equivalently: `j ↦ ζ^j` injective on `{0,…,d}`) force the Vandermonde determinant to be
nonzero, hence the only solution is `a ≡ 0`.  This is exactly the step that kills the hypothetical
algebraic relation in the task03 answer.
-/

open scoped Matrix

namespace Bottcher

/-- **Vandermonde vanishing.**  Let `ζ ∈ ℂ` with the powers `ζ^0, …, ζ^d` pairwise distinct
(`j ↦ ζ^j` injective on `Fin (d+1)`).  If `∑_{j} a_j · ζ^{r·j} = 0` for every `r = 0, …, d`, then
every `a_j = 0`. -/
theorem eq_zero_of_vandermonde_sum {d : ℕ} {ζ : ℂ}
    (hζ : Function.Injective (fun j : Fin (d + 1) => ζ ^ (j : ℕ)))
    {a : Fin (d + 1) → ℂ}
    (h : ∀ r : Fin (d + 1), ∑ j, a j * ζ ^ ((r : ℕ) * (j : ℕ)) = 0) :
    a = 0 := by
  set v : Fin (d + 1) → ℂ := fun r => ζ ^ (r : ℕ) with hv
  apply Matrix.eq_zero_of_mulVec_eq_zero (M := Matrix.vandermonde v)
  · rw [Matrix.det_vandermonde_ne_zero_iff]; exact hζ
  · funext r
    have hrow : (Matrix.vandermonde v *ᵥ a) r = ∑ j : Fin (d + 1), v r ^ (j : ℕ) * a j := by
      simp [Matrix.mulVec, dotProduct, Matrix.vandermonde]
    rw [Pi.zero_apply, hrow, ← h r]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hv, ← pow_mul, mul_comm]

/-- Convenience form: under the same hypotheses, each individual coefficient vanishes. -/
theorem coeff_eq_zero_of_vandermonde_sum {d : ℕ} {ζ : ℂ}
    (hζ : Function.Injective (fun j : Fin (d + 1) => ζ ^ (j : ℕ)))
    {a : Fin (d + 1) → ℂ}
    (h : ∀ r : Fin (d + 1), ∑ j, a j * ζ ^ ((r : ℕ) * (j : ℕ)) = 0) (j : Fin (d + 1)) :
    a j = 0 := by
  have := eq_zero_of_vandermonde_sum hζ h
  rw [this]; rfl

end Bottcher
