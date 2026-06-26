/-
# Böttcher tower — existence of periodic points (entry to the interior natural boundary, D2)

The interior-Fatou-component case of the `J_c` natural boundary runs on **repelling periodic points**:
at a period-`p` point `z₀` with multiplier `λ` (`|λ|>1`), a hypothetical continuation of `φ_c` forces
the resonance `λ^m = 2^p` (from `φ_c(f^p z)=φ_c(z)^{2^p}`), impossible for nonexceptional `c`. The
entry point is the existence of periodic points: `f_c^[p] z = z` has a solution, because `f_c^[p]` is a
polynomial of degree `2^p` and `f_c^[p](z) - z` is a nonconstant polynomial over the algebraically
closed `ℂ`.

New file (hRigid connected lane, D2 foundation); consumes `BasinBranching`.
-/
import GaloisForLFunctions.Bottcher.BasinBranching

open Polynomial

namespace Bottcher

/-- **Periodic points exist.** For every period `p ≥ 1`, `f_c^[p]` has a fixed point (a periodic point
of `f_c` of period dividing `p`): `f_c^[p] z - z` is a degree-`2^p` polynomial over `ℂ`, hence has a
root. The dynamical foundation of the repelling-cycle route to the interior `J_c` natural boundary. -/
theorem exists_periodic_point (c : ℂ) (p : ℕ) (hp : 1 ≤ p) :
    ∃ z : ℂ, (quadratic c)^[p] z = z := by
  have hXlt : (Polynomial.X : Polynomial ℂ).natDegree < (quadraticPolyIterate c p).natDegree := by
    rw [Polynomial.natDegree_X, quadraticPolyIterate_natDegree]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  have hdeg : (quadraticPolyIterate c p - Polynomial.X).natDegree = 2 ^ p := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hXlt, quadraticPolyIterate_natDegree]
  have hdegpos : 0 < (quadraticPolyIterate c p - Polynomial.X).degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hdeg]; positivity)
  obtain ⟨z, hz⟩ := Complex.exists_root hdegpos
  have hz' : (quadraticPolyIterate c p - Polynomial.X).eval z = 0 := hz
  rw [Polynomial.eval_sub, Polynomial.eval_X, quadraticPolyIterate_eval, sub_eq_zero] at hz'
  exact ⟨z, hz'⟩

end Bottcher
