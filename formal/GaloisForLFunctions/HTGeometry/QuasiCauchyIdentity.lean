import GaloisForLFunctions.HTGeometry.SecondKindDividedDiff
import GaloisForLFunctions.HTGeometry.QuasiQuadrature

/-!
# The finite-level Nevanlinna identity

At a node `ξ` of `P = Q_{n+1} + t·Qₙ` one has `P(z) = −(ξ − z)·E(ξ)`, where `E` is the divided
difference of `P` at `z`.  So multiplying the quadrature Cauchy sum by `P(z)` turns it into minus the
quadrature of a polynomial of degree `n`, which the rule integrates exactly; and the moment functional
of that divided difference is `s₀·(R_{n+1}(z) + t·Rₙ(z))`.

The identity is therefore algebraic at each level — no residues, no partial fractions.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The divided difference of a quasi-orthogonal polynomial, in the two-term basis. -/
noncomputable def quasiDividedDiff (s : ℕ → ℝ) (n : ℕ) (t z : ℝ) : Polynomial ℝ :=
  firstKindDividedDiff s (n + 1) z + C t * firstKindDividedDiff s n z

theorem mul_quasiDividedDiff (s : ℕ → ℝ) (n : ℕ) (t z : ℝ) :
    (X - C z) * quasiDividedDiff s n t z
      = quasiOrtho s n t - C ((quasiOrtho s n t).eval z) := by
  have h1 := mul_firstKindDividedDiff s (n + 1) z
  have h2 := mul_firstKindDividedDiff s n z
  rw [quasiDividedDiff, quasiOrtho]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.C_add,
    Polynomial.C_mul]
  linear_combination h1 + C t * h2

/-- Each first-kind divided difference has degree below its index. -/
theorem firstKindDividedDiff_degree_lt (s : ℕ → ℝ) (n : ℕ) (z : ℝ) :
    (firstKindDividedDiff s n z).degree < ((n : ℕ) : WithBot ℕ) := by
  rcases n with _ | m
  · rw [firstKindDividedDiff_zero, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (by simp)
  · rcases eq_or_ne (firstKindDividedDiff s (m + 1) z) 0 with hz | hz
    · rw [hz, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (by simp)
    · have hnd : (firstKindDividedDiff s (m + 1) z).natDegree
          = (monicOrtho s (m + 1) - C ((monicOrtho s (m + 1)).eval z)).natDegree - 1 := by
        rw [firstKindDividedDiff, Polynomial.natDegree_divByMonic _ (monic_X_sub_C z),
          Polynomial.natDegree_X_sub_C]
      have hle : (monicOrtho s (m + 1) - C ((monicOrtho s (m + 1)).eval z)).natDegree ≤ m + 1 := by
        refine Polynomial.natDegree_le_iff_degree_le.mpr ?_
        refine le_trans (Polynomial.degree_sub_le _ _) ?_
        rw [monicOrtho_degree]
        exact max_le le_rfl (le_trans Polynomial.degree_C_le (by exact_mod_cast Nat.zero_le _))
      rw [Polynomial.degree_eq_natDegree hz]
      have hlt : (firstKindDividedDiff s (m + 1) z).natDegree < m + 1 := by omega
      exact_mod_cast hlt

/-- The quasi divided difference has degree below `n+1`, so the rule integrates it exactly. -/
theorem quasiDividedDiff_degree_lt (s : ℕ → ℝ) (n : ℕ) (t z : ℝ) :
    (quasiDividedDiff s n t z).degree < (((n + 1 : ℕ)) : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
  refine max_lt (firstKindDividedDiff_degree_lt s (n + 1) z) ?_
  refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
  have hC : (C t).degree ≤ 0 := Polynomial.degree_C_le
  have hE : (firstKindDividedDiff s n z).degree < ((n : ℕ) : WithBot ℕ) :=
    firstKindDividedDiff_degree_lt s n z
  calc (C t).degree + (firstKindDividedDiff s n z).degree
      ≤ 0 + (firstKindDividedDiff s n z).degree := add_le_add hC le_rfl
    _ = (firstKindDividedDiff s n z).degree := zero_add _
    _ < ((n : ℕ) : WithBot ℕ) := hE
    _ < (((n + 1 : ℕ)) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self n

/-- **The finite-level Nevanlinna identity.**  Off the node set,
`P(z)·∑_ξ w_ξ/(ξ − z) = −s₀·(R_{n+1}(z) + t·Rₙ(z))`. -/
theorem quasiCauchy_identity (h : PositiveMomentForm s) (n : ℕ) (t z : ℝ)
    (hz : (quasiOrtho s n t).eval z ≠ 0) :
    (quasiOrtho s n t).eval z *
        ∑ ξ ∈ quasiNodes s n t, quasiWeight s n t ξ / (ξ - z)
      = -(s 0) * ((secondKind s (n + 1)).eval z + t * (secondKind s n).eval z) := by
  classical
  have hterm : ∀ ξ ∈ quasiNodes s n t,
      quasiWeight s n t ξ * ((quasiOrtho s n t).eval z / (ξ - z))
        = -(quasiWeight s n t ξ * (quasiDividedDiff s n t z).eval ξ) := by
    intro ξ hξ
    have hroot : (quasiOrtho s n t).eval ξ = 0 := (mem_quasiNodes_iff n t ξ).mp hξ
    have hne : ξ - z ≠ 0 := by
      intro hc
      apply hz
      have : ξ = z := by linarith [sub_eq_zero.mp hc]
      rw [← this]
      exact hroot
    have hev := congrArg (Polynomial.eval ξ) (mul_quasiDividedDiff s n t z)
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      hroot] at hev
    have hval : (quasiOrtho s n t).eval z = -((ξ - z) * (quasiDividedDiff s n t z).eval ξ) := by
      linarith [hev]
    rw [hval, neg_div, mul_comm (ξ - z), mul_div_assoc, div_self hne, mul_one]
    ring
  have hsum : ∑ ξ ∈ quasiNodes s n t, quasiWeight s n t ξ * (quasiDividedDiff s n t z).eval ξ
      = momentFunctional s (quasiDividedDiff s n t z) :=
    (momentFunctional_eq_quasiSum_of_degree_lt h n t _
      (quasiDividedDiff_degree_lt s n t z)).symm
  have hL : momentFunctional s (quasiDividedDiff s n t z)
      = s 0 * ((secondKind s (n + 1)).eval z + t * (secondKind s n).eval z) := by
    have hML : ∀ p : Polynomial ℝ, momentFunctional s p = momentInner s p 1 := fun p => by
      rw [momentInner_def, mul_one]
    have hAdd : ∀ p q : Polynomial ℝ,
        momentFunctional s (p + q) = momentFunctional s p + momentFunctional s q := by
      intro p q
      rw [hML, hML, hML, momentInner_add_left]
    have hCmul : ∀ (c : ℝ) (p : Polynomial ℝ),
        momentFunctional s (C c * p) = c * momentFunctional s p := by
      intro c p
      rw [hML, hML, ← Polynomial.smul_eq_C_mul, momentInner_smul_left]
    rw [quasiDividedDiff, hAdd, hCmul,
      momentFunctional_firstKindDividedDiff h (n + 1) z,
      momentFunctional_firstKindDividedDiff h n z]
    ring
  calc (quasiOrtho s n t).eval z *
        ∑ ξ ∈ quasiNodes s n t, quasiWeight s n t ξ / (ξ - z)
      = ∑ ξ ∈ quasiNodes s n t,
          quasiWeight s n t ξ * ((quasiOrtho s n t).eval z / (ξ - z)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ξ _ => by ring
    _ = ∑ ξ ∈ quasiNodes s n t,
          -(quasiWeight s n t ξ * (quasiDividedDiff s n t z).eval ξ) :=
        Finset.sum_congr rfl hterm
    _ = -(momentFunctional s (quasiDividedDiff s n t z)) := by
        rw [← hsum]
        simp
    _ = -(s 0) * ((secondKind s (n + 1)).eval z + t * (secondKind s n).eval z) := by
        rw [hL]
        ring

end HTGeometry
