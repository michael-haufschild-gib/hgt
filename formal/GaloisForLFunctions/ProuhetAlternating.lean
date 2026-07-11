import Mathlib

/-!
# Prouhet alternating annihilation

The signed sum of a polynomial over a cube of subset-sums vanishes whenever the polynomial
degree is smaller than the dimension: for any weights `w₀, …, w_{n−1}` and any polynomial `p`
with `natDegree p < n`,

`∑_{S ⊆ {0,…,n−1}} (−1)^{|S|} · p(∑_{i∈S} wᵢ) = 0`  (`prouhet_alternating_annihilation`).

Splitting on the top index turns the sum into the same sum for the one-step difference
`p(· + w_{n−1}) − p(·)`, whose degree has dropped; induction finishes.  With dyadic weights
`wᵢ = 2^i` the subsets enumerate an interval of integers and the sign is the Thue–Morse
parity, so this is the Prouhet–Tarry–Escott cancellation: a Prouhet class annihilates all
polynomial moments below its depth — the mechanism by which Prouhet clusters kill the
polynomial-scale part of coefficient identities, leaving only the phase relation.
-/

open Polynomial

namespace GaloisForLFunctions

/-- **Prouhet alternating annihilation**: a polynomial of degree less than the number of
weights is annihilated by the signed inclusion–exclusion over subset sums. -/
theorem prouhet_alternating_annihilation {n : ℕ} (w : ℕ → ℂ) (p : Polynomial ℂ)
    (hdeg : p.natDegree < n) :
    ∑ S ∈ (Finset.range n).powerset, (-1 : ℂ) ^ S.card * p.eval (∑ i ∈ S, w i) = 0 := by
  induction n generalizing p with
  | zero => exact absurd hdeg (Nat.not_lt_zero _)
  | succ n ih =>
    rw [Finset.range_succ,
      Finset.sum_powerset_insert (Finset.notMem_range_self)
        (fun S => (-1 : ℂ) ^ S.card * p.eval (∑ i ∈ S, w i)),
      ← Finset.sum_add_distrib]
    set q : Polynomial ℂ := taylor (w n) p - p with hq
    have heval : ∀ x : ℂ, q.eval x = p.eval (x + w n) - p.eval x := by
      intro x
      rw [hq, eval_sub, taylor_apply, eval_comp, eval_add, eval_X, eval_C]
    have hstep : ∀ T ∈ (Finset.range n).powerset,
        (-1 : ℂ) ^ T.card * p.eval (∑ i ∈ T, w i)
          + (-1 : ℂ) ^ (insert n T).card * p.eval (∑ i ∈ insert n T, w i)
        = -((-1 : ℂ) ^ T.card * q.eval (∑ i ∈ T, w i)) := by
      intro T hT
      have hnT : n ∉ T := fun hmem =>
        Finset.notMem_range_self (Finset.mem_powerset.mp hT hmem)
      rw [Finset.card_insert_of_notMem hnT, Finset.sum_insert hnT, heval, pow_succ]
      ring_nf
      rw [add_comm (w n) (∑ i ∈ T, w i)]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_neg_distrib]
    by_cases hq0 : q = 0
    · simp [hq0]
    · have hp0 : p ≠ 0 := by
        intro h0
        apply hq0
        rw [hq, h0, map_zero, sub_zero]
      have hpdeg : p.natDegree ≠ 0 → q.natDegree < p.natDegree := by
        intro hpd
        have htp0 : taylor (w n) p ≠ 0 := by
          intro h0
          apply hp0
          have h1 := congrArg (taylor (-w n)) h0
          rwa [taylor_taylor, neg_add_cancel, taylor_zero', LinearMap.id_apply, map_zero]
            at h1
        have hdegeq : (taylor (w n) p).degree = p.degree := by
          rw [degree_eq_natDegree htp0, degree_eq_natDegree hp0, natDegree_taylor]
        have hlc : (taylor (w n) p).leadingCoeff = p.leadingCoeff := by
          rw [taylor_apply, leadingCoeff_comp (by simp [natDegree_X_add_C]), leadingCoeff_X_add_C,
            one_pow, mul_one]
        have hdlt : q.degree < p.degree := by
          rw [hq]
          exact degree_sub_lt hdegeq htp0 hlc
        exact natDegree_lt_natDegree hq0 hdlt
      rcases Nat.eq_zero_or_pos p.natDegree with hpd | hpd
      · exfalso
        apply hq0
        obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp hpd
        rw [hq, taylor_C, sub_self]
      · have hqn : q.natDegree < n := by
          have := hpdeg (by omega)
          omega
        rw [ih q hqn, neg_zero]

end GaloisForLFunctions
