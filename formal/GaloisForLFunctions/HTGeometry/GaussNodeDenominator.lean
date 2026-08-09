import GaloisForLFunctions.HTGeometry.GaussQuadratureNodes
import GaloisForLFunctions.HTGeometry.SecondKindDividedDiff
import GaloisForLFunctions.HTGeometry.GaussQuadrature

/-!
# The orthogonal polynomial is the Gauss-node product

`monicOrtho s (n+1)` is monic of degree `n+1` with `n+1` simple real roots, so it factors over its
node set:

`monicOrtho s (n+1) (z) = ∏_{x ∈ gaussNodes s n} (z − x)`.

This identifies the denominator of the finite-stage Cauchy transform of the Gauss quadrature
measure with the orthogonal polynomial itself, which is the first half of the Weyl-disc
description.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The orthogonal polynomial factors over its node set.** -/
theorem eval_monicOrtho_eq_prod_gaussNodes (h : PositiveMomentForm s) (n : ℕ) (z : ℝ) :
    (monicOrtho s (n + 1)).eval z = ∏ x ∈ gaussNodes s n, (z - x) := by
  classical
  have hmonic : (monicOrtho s (n + 1)).Monic := monicOrtho_monic s (n + 1)
  have hnd : (monicOrtho s (n + 1)).natDegree = n + 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some (monicOrtho_degree s (n + 1))
  have hcard : (monicOrtho s (n + 1)).roots.card = (monicOrtho s (n + 1)).natDegree := by
    rw [monicOrtho_roots_card h n, hnd]
  have hfac := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  have heval := congrArg (fun p : Polynomial ℝ => p.eval z) hfac
  simp only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_apply,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heval
  rw [← heval, gaussNodes,
    Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (monicOrtho_roots_nodup h n)]

/-- The Gauss-node product is nonzero off the node set. -/
theorem prod_gaussNodes_ne_zero (h : PositiveMomentForm s) (n : ℕ) {z : ℝ}
    (hz : (monicOrtho s (n + 1)).eval z ≠ 0) :
    ∏ x ∈ gaussNodes s n, (z - x) ≠ 0 := by
  rw [← eval_monicOrtho_eq_prod_gaussNodes h n z]
  exact hz

/-! ## The finite-stage Cauchy transform is the second-kind ratio -/

open Polynomial in
/-- **Finite-stage closed form.**  Off the nodes, the Christoffel-weighted Cauchy sum of the Gauss
quadrature measure is `−s₀·q_{n+1}(z)/p_{n+1}(z)`.  This is the finite-`n` half of the Weyl-disc
description: the Cauchy transform of the stage-`n` measure is the ratio of the second-kind
polynomial to the orthogonal polynomial. -/
theorem gaussSum_cauchy_eq_secondKind_ratio (h : PositiveMomentForm s) (n : ℕ) {z : ℝ}
    (hz : (monicOrtho s (n + 1)).eval z ≠ 0) :
    ∑ x ∈ gaussNodes s n, christoffel s n x / (x - z)
      = -(s 0 * (secondKind s (n + 1)).eval z) / (monicOrtho s (n + 1)).eval z := by
  classical
  set p := monicOrtho s (n + 1) with hp
  set D := firstKindDividedDiff s (n + 1) z with hD
  have hdeg1 : p.degree = ((n + 1 : ℕ) : WithBot ℕ) := monicOrtho_degree s (n + 1)
  have hzeroC : ((0 : WithBot ℕ)) ≤ ((n + 1 : ℕ) : WithBot ℕ) := by
    exact_mod_cast Nat.zero_le (n + 1)
  have hsubne : p - C (p.eval z) ≠ 0 := by
    intro hcon
    have heq : p = C (p.eval z) := by rwa [sub_eq_zero] at hcon
    have hdc : p.degree ≤ 0 := by rw [heq]; exact Polynomial.degree_C_le
    rw [hdeg1] at hdc
    have : ((n + 1 : ℕ) : WithBot ℕ) ≤ 0 := hdc
    exact absurd this (by exact_mod_cast (by omega : ¬ (n + 1 ≤ 0)))
  have hsubdeg : (p - C (p.eval z)).degree ≤ ((n + 1 : ℕ) : WithBot ℕ) := by
    refine le_trans (Polynomial.degree_sub_le _ _) ?_
    exact max_le (le_of_eq hdeg1) (le_trans Polynomial.degree_C_le hzeroC)
  have hDdeg : D.degree < ((2 * n + 2 : ℕ) : WithBot ℕ) := by
    have hlt : D.degree < (p - C (p.eval z)).degree := by
      rw [hD, firstKindDividedDiff]
      refine Polynomial.degree_divByMonic_lt (p - C (p.eval z)) (X - C z) hsubne ?_
      rw [Polynomial.degree_X_sub_C]
      norm_num
    refine lt_of_lt_of_le (lt_of_lt_of_le hlt hsubdeg) ?_
    exact_mod_cast (by omega : (n + 1 : ℕ) ≤ 2 * n + 2)
  have hquad := momentFunctional_eq_gaussSum h n D hDdeg
  have hmom := momentFunctional_firstKindDividedDiff h (n + 1) z
  have hnode : ∀ x ∈ gaussNodes s n, D.eval x = -(p.eval z) / (x - z) := by
    intro x hx
    have hxz : x - z ≠ 0 := by
      intro hcon
      apply hz
      have : x = z := by linarith [sub_eq_zero.mp hcon]
      rw [← this]
      exact (mem_gaussNodes_iff n x).mp hx
    have hmul := congrArg (fun q : Polynomial ℝ => q.eval x) (mul_firstKindDividedDiff s (n + 1) z)
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      at hmul
    rw [(mem_gaussNodes_iff n x).mp hx] at hmul
    field_simp at hmul ⊢
    linarith [hmul]
  rw [hmom] at hquad
  rw [eq_div_iff hz]
  rw [Finset.sum_mul]
  have hlhs : ∀ x ∈ gaussNodes s n,
      christoffel s n x / (x - z) * p.eval z = christoffel s n x * D.eval x * (-1) := by
    intro x hx
    rw [hnode x hx]
    field_simp
  rw [Finset.sum_congr rfl hlhs, ← Finset.sum_mul, ← hquad]
  ring


end HTGeometry
