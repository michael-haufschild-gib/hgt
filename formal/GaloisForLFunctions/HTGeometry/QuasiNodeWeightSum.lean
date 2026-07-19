import GaloisForLFunctions.HTGeometry.QuasiTightness

/-!
# Christoffel limits over a node set sum to at most the total mass

The Lagrange basis polynomial at a node is normalised there, so the variational property of the
Christoffel limit bounds `λ` at that node by its own moment norm; exactness of the rule on the square
of that polynomial identifies the moment norm with the interpolatory weight.  The weights sum to `s₀`,
so the Christoffel limits over any node set do too.

This is the finite-level form of the inequality the leaf's atoms need.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The interpolatory weight is the moment norm of the Lagrange basis polynomial. -/
theorem quasiWeight_eq_momentInner_basis (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) {x : ℝ}
    (hx : x ∈ quasiNodes s n t) :
    quasiWeight s n t x
      = momentInner s (Lagrange.basis (quasiNodes s n t) id x)
          (Lagrange.basis (quasiNodes s n t) id x) := by
  classical
  set b := Lagrange.basis (quasiNodes s n t) id x with hbdef
  have hbdeg : b.degree ≤ ((n : ℕ) : WithBot ℕ) := by
    rw [hbdef]
    have hdb := Lagrange.degree_basis (v := (id : ℝ → ℝ)) (Set.injOn_id _) hx
    rw [hdb, quasiNodes_card h n t]
    simp
  have hsqdeg : (b * b).degree ≤ ((2 * n : ℕ) : WithBot ℕ) := by
    refine le_trans (degree_mul_le _ _) ?_
    calc b.degree + b.degree
        ≤ ((n : ℕ) : WithBot ℕ) + ((n : ℕ) : WithBot ℕ) := add_le_add hbdeg hbdeg
      _ = ((2 * n : ℕ) : WithBot ℕ) := by push_cast; ring
  have hexact := momentFunctional_eq_quasiSum h n t (b * b) hsqdeg
  have hval : ∀ y ∈ quasiNodes s n t, (b * b).eval y = if y = x then 1 else 0 := by
    intro y hy
    rw [eval_mul, hbdef]
    rcases eq_or_ne y x with rfl | hne
    · have hself := Lagrange.eval_basis_self (v := (id : ℝ → ℝ)) (Set.injOn_id _) hy
      simp only [id_eq] at hself
      rw [hself]
      simp
    · have hoff := Lagrange.eval_basis_of_ne (v := (id : ℝ → ℝ)) hne.symm hy
      simp only [id_eq] at hoff
      rw [hoff]
      simp [hne]
  rw [Finset.sum_congr rfl fun y hy => by rw [hval y hy]] at hexact
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', if_pos hx] at hexact
  rw [← hexact, momentInner_def]

/-- **The Christoffel limit at a node is at most its interpolatory weight.** -/
theorem christoffelLimit_le_quasiWeight (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) {ξ : ℝ}
    (hξ : ξ ∈ quasiNodes s n t) : christoffelLimit s ξ ≤ quasiWeight s n t ξ := by
  rw [quasiWeight_eq_momentInner_basis h n t hξ]
  refine christoffelLimit_le_momentInner_self h ξ _ ?_
  have hself := Lagrange.eval_basis_self (v := (id : ℝ → ℝ)) (Set.injOn_id _) hξ
  simpa using hself

/-- **The Christoffel limits over a quasi-orthogonal node set sum to at most `s₀`.** -/
theorem sum_christoffelLimit_quasiNodes_le (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) :
    ∑ ξ ∈ quasiNodes s n t, christoffelLimit s ξ ≤ s 0 := by
  have hsum : ∑ ξ ∈ quasiNodes s n t, quasiWeight s n t ξ = s 0 := by
    simpa using quasiSum_pow h n t 0 (by omega)
  calc ∑ ξ ∈ quasiNodes s n t, christoffelLimit s ξ
      ≤ ∑ ξ ∈ quasiNodes s n t, quasiWeight s n t ξ :=
        Finset.sum_le_sum fun ξ hξ => christoffelLimit_le_quasiWeight h n t hξ
    _ = s 0 := hsum

/-- The Gauss nodes are the quasi nodes of parameter zero. -/
theorem quasiOrtho_zero_param (s : ℕ → ℝ) (n : ℕ) :
    quasiOrtho s n 0 = monicOrtho s (n + 1) := by
  rw [quasiOrtho]
  simp

theorem quasiNodes_zero_param (s : ℕ → ℝ) (n : ℕ) : quasiNodes s n 0 = gaussNodes s n := by
  rw [quasiNodes, gaussNodes, quasiOrtho_zero_param]

/-- **The Christoffel limits over a Gauss node set sum to at most `s₀`.** -/
theorem sum_christoffelLimit_gaussNodes_le (h : PositiveMomentForm s) (n : ℕ) :
    ∑ ξ ∈ gaussNodes s n, christoffelLimit s ξ ≤ s 0 := by
  rw [← quasiNodes_zero_param]
  exact sum_christoffelLimit_quasiNodes_le h n 0

end HTGeometry
