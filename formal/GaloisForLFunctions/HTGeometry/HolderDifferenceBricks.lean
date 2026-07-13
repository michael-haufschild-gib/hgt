import Mathlib

/-!
# Difference-equation bricks for Hölder's theorem

The classical difference-equation proof of Hölder's theorem (no algebraic differential
equation for `Γ`, equivalently for `ψ`) rests on two facts about the unit shift `X ↦ X + 1`
on rational functions, and both are purely polynomial:

* **Shift-periodic rational functions are constant** (`shift_periodic_quotient_constant`):
  if `p(X+1)·q(X) = p(X)·q(X+1)` with `p, q` coprime, then `p` and `q` are constants.  The shift preserves degree and leading coefficient, so coprime divisibility
  forces `p(X+1) = p(X)`, and a shift-invariant polynomial takes a single value on `ℕ`.

* **No rational function has a difference-derivative with a pole at one point of a
  `ℤ`-orbit** (`difference_single_pole_free`): if `w = p/q` satisfies
  `w(X+1) - w(X) = A(X)/X^{n+1}` with `natDegree A ≤ n`, then `A = 0`.  In cross-multiplied
  polynomial form, the extreme integer roots of `q` are pinched — evaluation at the largest
  integer root forces it to be `0`, evaluation below the smallest forces that to be `1`, so
  `q` has no integer roots; evaluating at `0` then kills the constant coefficient of `A`,
  and cancelling one factor of `X` descends by induction.

In Hölder's argument these bricks finish the proof.  A minimal-rank irreducible relation
`P` for `ψ` inherits, from `ψ(s+1) = ψ(s) + 1/s` and its derivatives, the functional
equation `P(s+1, (y_j + (-1)^j j!/s^{j+1})_j) = u(s)·P(s, y)`; the top homogeneous part in
the jet variables has shift-periodic coefficient ratios — constant by the first brick — and
after normalization the degree-`(D-1)` layer satisfies difference equations whose right
sides are `ℂ`-combinations of `1/s, …, 1/s^{n+1}` — killed by the second brick.  The
gradient of the top form then vanishes, impossible in characteristic zero for `D ≥ 1`.
What remains is differential-polynomial bookkeeping with no further analytic input.
-/

namespace GaloisForLFunctions

open Polynomial

/-- A polynomial invariant under the unit shift takes one value on `ℕ`, hence is constant. -/
theorem comp_X_add_one_eq_self {p : Polynomial ℂ}
    (h : p.comp (X + C 1) = p) : p = C (p.eval 0) := by
  have hval : ∀ n : ℕ, p.eval (n : ℂ) = p.eval 0 := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
      have hk := congrArg (Polynomial.eval (k : ℂ)) h
      simp only [eval_comp, eval_add, eval_X, eval_C] at hk
      push_cast
      rw [hk]
      exact ih
  have hsub : p - C (p.eval 0) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => (n : ℂ)) Nat.cast_injective
    intro n
    simp only [Set.mem_setOf_eq, IsRoot, eval_sub, eval_C, hval n, sub_self]
  exact eq_of_sub_eq_zero hsub

/-- **Shift-periodic rational functions are constant**: if `p(X+1)·q = p·q(X+1)` with
`p, q` coprime, both polynomials are constant. -/
theorem shift_periodic_quotient_constant {p q : Polynomial ℂ}
    (hco : IsCoprime p q) (h : p.comp (X + C 1) * q = p * q.comp (X + C 1)) :
    ∃ a b : ℂ, p = C a ∧ q = C b := by
  rcases eq_or_ne p 0 with rfl | hp
  · obtain ⟨c, _, hcq⟩ := Polynomial.isUnit_iff.mp (isCoprime_zero_left.mp hco)
    exact ⟨0, c, by simp, hcq.symm⟩
  · have hdvd0 : p ∣ p.comp (X + C 1) * q := ⟨q.comp (X + C 1), h⟩
    have hdvd : p ∣ p.comp (X + C 1) := hco.dvd_of_dvd_mul_right hdvd0
    obtain ⟨t, ht⟩ := hdvd
    have hcompne : p.comp (X + C 1) ≠ 0 := by
      intro h0
      exact hp ((Polynomial.comp_eq_zero_iff.mp h0).resolve_right
        (fun hh => by simpa using hh.2))
    have htne : t ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at ht
      exact hcompne ht
    have hdegX : (X + C (1 : ℂ)).natDegree = 1 := by
      simpa using Polynomial.natDegree_X_add_C (1 : ℂ)
    have hdegcomp : (p.comp (X + C 1)).natDegree = p.natDegree := by
      rw [Polynomial.natDegree_comp, hdegX, mul_one]
    have hdegt : t.natDegree = 0 := by
      have := hdegcomp
      rw [ht, Polynomial.natDegree_mul hp htne] at this
      omega
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdegt
    have hlead : (p.comp (X + C 1)).leadingCoeff = p.leadingCoeff := by
      rw [Polynomial.leadingCoeff_comp (by rw [hdegX]; norm_num),
        Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
    have hc1 : c = 1 := by
      have h2 : p.leadingCoeff * c = p.leadingCoeff := by
        have h3 := hlead
        rw [ht, ← hc, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C] at h3
        exact h3
      have hlp : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
      exact mul_left_cancel₀ hlp (h2.trans (mul_one p.leadingCoeff).symm)
    have hshift : p.comp (X + C 1) = p := by
      rw [ht, ← hc, hc1]
      simp
    have hpconst := comp_X_add_one_eq_self hshift
    -- transfer to q
    have hq' : C (p.eval 0) * q = C (p.eval 0) * q.comp (X + C 1) := by
      have := h
      rw [hshift, hpconst] at this
      linear_combination this
    have hp0 : (C (p.eval 0) : Polynomial ℂ) ≠ 0 := by
      rw [← hpconst]
      exact hp
    have hqshift : q.comp (X + C 1) = q := (mul_left_cancel₀ hp0 hq').symm
    exact ⟨p.eval 0, q.eval 0, hpconst, comp_X_add_one_eq_self hqshift⟩

private theorem descend {q B : Polynomial ℂ} (hq0 : q.eval 0 ≠ 0) (hq1 : q.eval 1 ≠ 0) :
    ∀ (n : ℕ) (A : Polynomial ℂ), A.natDegree ≤ n →
      X ^ (n + 1) * B = A * (q * q.comp (X + C 1)) → A = 0 := by
  have hval0 : ∀ (m : ℕ) (A : Polynomial ℂ),
      X ^ (m + 1) * B = A * (q * q.comp (X + C 1)) → A.eval 0 = 0 := by
    intro m A h
    have h0 := congrArg (Polynomial.eval (0 : ℂ)) h
    simp only [eval_mul, eval_pow, eval_X, eval_comp, eval_add, eval_C, zero_add] at h0
    rw [zero_pow (by omega : m + 1 ≠ 0), zero_mul] at h0
    rcases mul_eq_zero.mp h0.symm with h' | h'
    · exact h'
    · exact absurd h' (mul_ne_zero hq0 hq1)
  intro n
  induction n with
  | zero =>
    intro A hdeg h
    have hA0 : A.eval 0 = 0 := hval0 0 A h
    have hA := Polynomial.eq_C_of_natDegree_le_zero hdeg
    rw [hA, show A.coeff 0 = A.eval 0 from Polynomial.coeff_zero_eq_eval_zero A, hA0,
      map_zero]
  | succ k ih =>
    intro A hdeg h
    have hA0 : A.eval 0 = 0 := hval0 (k + 1) A h
    have hXdvd : X ∣ A := Polynomial.X_dvd_iff.mpr
      (by rw [Polynomial.coeff_zero_eq_eval_zero]; exact hA0)
    obtain ⟨A', rfl⟩ := hXdvd
    rcases eq_or_ne A' 0 with rfl | hA'
    · simp
    · exfalso
      apply hA'
      refine ih A' ?_ ?_
      · have hdX : (X * A').natDegree = 1 + A'.natDegree := by
          rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hA']
          simp
        omega
      · apply mul_left_cancel₀ (Polynomial.X_ne_zero (R := ℂ))
        linear_combination h

/-- **No rational function has a difference-derivative with a single-point pole.**
If `X^{n+1}·(p(X+1)·q − p·q(X+1)) = A·q·q(X+1)` — the cross-multiplied form of
`w(X+1) − w(X) = A(X)/X^{n+1}` for `w = p/q` — with `p, q` coprime, `q ≠ 0`, and
`natDegree A ≤ n`, then `A = 0`.  The extreme integer roots of `q` are pinched to `0`
and `1` simultaneously, so `q` has no integer roots, and evaluation at `0` descends. -/
theorem difference_single_pole_free {p q A : Polynomial ℂ} {n : ℕ} (hq : q ≠ 0)
    (hco : IsCoprime p q) (hdeg : A.natDegree ≤ n)
    (h : X ^ (n + 1) * (p.comp (X + C 1) * q - p * q.comp (X + C 1))
      = A * (q * q.comp (X + C 1))) :
    A = 0 := by
  have hpz : ∀ z : ℂ, q.eval z = 0 → p.eval z ≠ 0 := by
    intro z hqz hpz
    obtain ⟨a, b, hab⟩ := hco
    have := congrArg (Polynomial.eval z) hab
    simp only [eval_add, eval_mul, eval_one, hpz, hqz, mul_zero, add_zero] at this
    exact one_ne_zero this.symm
  have hnoint : ∀ m : ℤ, q.eval ((m : ℤ) : ℂ) ≠ 0 := by
    by_contra hcon
    simp only [not_forall, ne_eq, not_not] at hcon
    obtain ⟨m₀, hm₀⟩ := hcon
    have hfin : {m : ℤ | q.eval ((m : ℤ) : ℂ) = 0}.Finite := by
      have hroots : {x : ℂ | q.IsRoot x}.Finite := Polynomial.finite_setOf_isRoot hq
      exact Set.Finite.preimage Int.cast_injective.injOn hroots
    have hne : hfin.toFinset.Nonempty := ⟨m₀, by simpa using hm₀⟩
    set M : ℤ := hfin.toFinset.max' hne with hM_def
    set μ : ℤ := hfin.toFinset.min' hne with hμ_def
    have hMroot : q.eval ((M : ℤ) : ℂ) = 0 := by
      have := hfin.toFinset.max'_mem hne
      simpa using this
    have hμroot : q.eval ((μ : ℤ) : ℂ) = 0 := by
      have := hfin.toFinset.min'_mem hne
      simpa using this
    have hM1 : q.eval (((M + 1 : ℤ)) : ℂ) ≠ 0 := by
      intro hr
      have hmem : (M + 1 : ℤ) ∈ hfin.toFinset := by simpa using hr
      have := hfin.toFinset.le_max' _ hmem
      omega
    have hμ1 : q.eval (((μ - 1 : ℤ)) : ℂ) ≠ 0 := by
      intro hr
      have hmem : (μ - 1 : ℤ) ∈ hfin.toFinset := by simpa using hr
      have := hfin.toFinset.min'_le _ hmem
      omega
    -- evaluate the identity at the largest integer root: forces M = 0
    have hMzero : M = 0 := by
      have hM := congrArg (Polynomial.eval ((M : ℤ) : ℂ)) h
      simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_comp, eval_add, eval_C] at hM
      rw [hMroot] at hM
      have hcast : ((M : ℤ) : ℂ) + 1 = (((M + 1 : ℤ)) : ℂ) := by push_cast; ring
      rw [hcast] at hM
      simp only [mul_zero, zero_mul, zero_sub, mul_neg] at hM
      have hMpow : (((M : ℤ) : ℂ)) ^ (n + 1) = 0 := by
        rcases mul_eq_zero.mp (neg_eq_zero.mp hM) with h' | h'
        · exact h'
        · exact absurd h' (mul_ne_zero (hpz _ hMroot) hM1)
      have : ((M : ℤ) : ℂ) = 0 := pow_eq_zero_iff (by omega : n + 1 ≠ 0) |>.mp hMpow
      exact_mod_cast this
    -- evaluate one below the smallest integer root: forces μ = 1
    have hμone : μ = 1 := by
      have hm := congrArg (Polynomial.eval (((μ - 1 : ℤ)) : ℂ)) h
      simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_comp, eval_add, eval_C] at hm
      have hcast : (((μ - 1 : ℤ)) : ℂ) + 1 = ((μ : ℤ) : ℂ) := by push_cast; ring
      rw [hcast, hμroot] at hm
      simp only [mul_zero, sub_zero] at hm
      have hμpow : ((((μ - 1 : ℤ)) : ℂ)) ^ (n + 1) = 0 := by
        rcases mul_eq_zero.mp hm with h' | h'
        · exact h'
        · exact absurd h' (mul_ne_zero (hpz _ hμroot) hμ1)
      have : (((μ - 1 : ℤ)) : ℂ) = 0 := pow_eq_zero_iff (by omega : n + 1 ≠ 0) |>.mp hμpow
      have : (μ - 1 : ℤ) = 0 := by exact_mod_cast this
      omega
    have hle := hfin.toFinset.min'_le _ (hfin.toFinset.max'_mem hne)
    omega
  have hq0 : q.eval 0 ≠ 0 := by
    have := hnoint 0
    simpa using this
  have hq1 : q.eval 1 ≠ 0 := by
    have := hnoint 1
    simpa using this
  exact descend hq0 hq1 n A hdeg h

end GaloisForLFunctions
