import GaloisForLFunctions.HTGeometry.QuasiOrthogonal

/-!
# Quasi-orthogonal quadrature

The `n+1` nodes of `quasiOrtho s n t` carry an interpolatory rule, exact on degrees `≤ n` because
Lagrange interpolation is exact there.  It is in fact exact on degrees `≤ 2n`: dividing by the node
polynomial leaves a quotient of degree `< n`, and `quasiOrtho` is orthogonal to everything of degree
`< n`, so the quotient term contributes nothing to the moment functional while contributing nothing
to the sum either, the node polynomial vanishing at every node.

Exactness to order `2n` is one order short of the Gauss rule's `2n+1`, which costs nothing in the
limit.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

theorem momentFunctional_eq_inner_one (s : ℕ → ℝ) (p : Polynomial ℝ) :
    momentFunctional s p = momentInner s p 1 := by
  rw [momentInner_def, mul_one]

theorem momentInner_C_mul_left (s : ℕ → ℝ) (c : ℝ) (p q : Polynomial ℝ) :
    momentInner s (C c * p) q = c * momentInner s p q := by
  rw [← Polynomial.smul_eq_C_mul, momentInner_smul_left]

/-- **`quasiOrtho` is orthogonal to every polynomial of degree `< n`.**  Both summands are. -/
theorem quasiOrtho_inner_eq_zero (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) (p : Polynomial ℝ)
    (hp : p.degree < (n : WithBot ℕ)) :
    momentInner s (quasiOrtho s n t) p = 0 := by
  have h1 : momentInner s (monicOrtho s (n + 1)) p = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt h (n + 1) n (by omega) p hp
  have h2 : momentInner s (monicOrtho s n) p = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt h n n le_rfl p hp
  rw [quasiOrtho, momentInner_add_left, h1, momentInner_C_mul_left, h2, mul_zero, add_zero]

/-- The interpolatory weight at a node. -/
noncomputable def quasiWeight (s : ℕ → ℝ) (n : ℕ) (t : ℝ) (x : ℝ) : ℝ :=
  momentFunctional s (Lagrange.basis (quasiNodes s n t) id x)

/-- **Interpolatory exactness.**  On degrees below `n+1` the rule reproduces the moment
functional. -/
theorem momentFunctional_eq_quasiSum_of_degree_lt (h : PositiveMomentForm s) (n : ℕ) (t : ℝ)
    (p : Polynomial ℝ) (hp : p.degree < (((n + 1 : ℕ)) : WithBot ℕ)) :
    momentFunctional s p = ∑ x ∈ quasiNodes s n t, quasiWeight s n t x * p.eval x := by
  have hdeg : p.degree < ((quasiNodes s n t).card : WithBot ℕ) := by
    rw [quasiNodes_card h n t]
    exact hp
  have hint := Lagrange.eq_interpolate (v := (id : ℝ → ℝ)) (Set.injOn_id _) hdeg
  rw [Lagrange.interpolate_apply] at hint
  calc momentFunctional s p
      = momentFunctional s (∑ x ∈ quasiNodes s n t,
          C (p.eval (id x)) * Lagrange.basis (quasiNodes s n t) id x) := by rw [← hint]
    _ = ∑ x ∈ quasiNodes s n t, quasiWeight s n t x * p.eval x := by
        rw [momentFunctional_eq_inner_one, momentInner_sum_left]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [momentInner_C_mul_left, quasiWeight, momentFunctional_eq_inner_one]
        simp only [id_eq]
        ring

/-- **The quadrature is exact to order `2n`.** -/
theorem momentFunctional_eq_quasiSum (h : PositiveMomentForm s) (n : ℕ) (t : ℝ)
    (p : Polynomial ℝ) (hp : p.degree ≤ ((2 * n : ℕ) : WithBot ℕ)) :
    momentFunctional s p = ∑ x ∈ quasiNodes s n t, quasiWeight s n t x * p.eval x := by
  have hPm : (quasiOrtho s n t).Monic := quasiOrtho_monic s n t
  have hPdeg : (quasiOrtho s n t).degree = (((n + 1 : ℕ)) : WithBot ℕ) := quasiOrtho_degree s n t
  -- the quotient has degree below `n`
  have hq : (p /ₘ quasiOrtho s n t).degree < (n : WithBot ℕ) := by
    rcases eq_or_ne (p /ₘ quasiOrtho s n t) 0 with hz | hz
    · rw [hz, degree_zero]
      exact bot_lt_iff_ne_bot.mpr (by simp)
    · have hge : n + 1 ≤ p.natDegree := by
        by_contra hlt
        refine hz ((divByMonic_eq_zero_iff hPm).mpr ?_)
        rw [hPdeg]
        exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_of_not_le hlt)
      have hpnd : p.natDegree ≤ 2 * n := natDegree_le_iff_degree_le.mpr hp
      have hnd : (p /ₘ quasiOrtho s n t).natDegree = p.natDegree - (n + 1) := by
        rw [natDegree_divByMonic p hPm, quasiOrtho_natDegree]
      rw [degree_eq_natDegree hz]
      have hlt : (p /ₘ quasiOrtho s n t).natDegree < n := by omega
      exact_mod_cast hlt
  have hquot : momentInner s (quasiOrtho s n t) (p /ₘ quasiOrtho s n t) = 0 :=
    quasiOrtho_inner_eq_zero h n t _ hq
  -- the remainder has degree below `n+1`
  have hrem : (p %ₘ quasiOrtho s n t).degree < (((n + 1 : ℕ)) : WithBot ℕ) := by
    rw [← hPdeg]
    exact degree_modByMonic_lt p hPm
  have hr := momentFunctional_eq_quasiSum_of_degree_lt h n t _ hrem
  -- at a node the polynomial agrees with its remainder
  have hnode : ∀ x ∈ quasiNodes s n t, (p %ₘ quasiOrtho s n t).eval x = p.eval x := by
    intro x hx
    have hPx : (quasiOrtho s n t).eval x = 0 := (mem_quasiNodes_iff n t x).mp hx
    have hev := congrArg (Polynomial.eval x) (modByMonic_add_div p (quasiOrtho s n t))
    simp only [eval_add, eval_mul, hPx, zero_mul, add_zero] at hev
    exact hev
  calc momentFunctional s p
      = momentFunctional s (p %ₘ quasiOrtho s n t
          + quasiOrtho s n t * (p /ₘ quasiOrtho s n t)) := by
        rw [modByMonic_add_div]
    _ = momentFunctional s (p %ₘ quasiOrtho s n t)
          + momentInner s (quasiOrtho s n t) (p /ₘ quasiOrtho s n t) := by
        rw [momentFunctional_add, momentInner_def]
    _ = ∑ x ∈ quasiNodes s n t, quasiWeight s n t x * p.eval x := by
        rw [hquot, add_zero, hr]
        exact Finset.sum_congr rfl fun x hx => by rw [hnode x hx]

/-- **The weights are positive.**  The square of a Lagrange basis polynomial has degree `2n`, so the
rule computes its moment functional exactly; that value is the weight, and it is a positive moment
square. -/
theorem quasiWeight_pos (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) {x : ℝ}
    (hx : x ∈ quasiNodes s n t) : 0 < quasiWeight s n t x := by
  classical
  set b := Lagrange.basis (quasiNodes s n t) id x with hbdef
  have hbdeg : b.degree ≤ ((n : ℕ) : WithBot ℕ) := by
    rw [hbdef]
    have := Lagrange.degree_basis (v := (id : ℝ → ℝ)) (Set.injOn_id _) hx
    rw [this, quasiNodes_card h n t]
    simp
  have hsqdeg : (b * b).degree ≤ ((2 * n : ℕ) : WithBot ℕ) := by
    refine le_trans (degree_mul_le _ _) ?_
    have := add_le_add hbdeg hbdeg
    calc b.degree + b.degree ≤ ((n : ℕ) : WithBot ℕ) + ((n : ℕ) : WithBot ℕ) := this
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
  rw [Finset.sum_congr rfl (fun y hy => by rw [hval y hy])] at hexact
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', if_pos hx] at hexact
  have hbne : b ≠ 0 := by
    intro hzero
    have hself := Lagrange.eval_basis_self (v := (id : ℝ → ℝ)) (Set.injOn_id _) hx
    simp only [id_eq, ← hbdef, hzero] at hself
    simp at hself
  have hgoal : quasiWeight s n t x = momentInner s b b := by
    rw [← hexact, momentInner_def]
  rw [hgoal]
  exact h.pos_of_ne_zero b hbne

end HTGeometry
