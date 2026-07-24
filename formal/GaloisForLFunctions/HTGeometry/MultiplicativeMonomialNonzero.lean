import GaloisForLFunctions.HTGeometry.MultiplicativeMonomial

/-!
# Characters multiplicative on the nonzero part are monomials

The clock cocharacter is indexed by the multiplicative group `C^*` (a factor-zero semilinear map
would annihilate every derivative, impossible for an automorphism), so its scaling character is
multiplicative only on the nonzero elements.  A nonzero polynomial `P` with
`P(xy) = P(x)P(y)` for all nonzero `x, y` is still a monomial `P = X^k`: the two places in the
full-multiplicativity proof that used a possibly-zero argument are rescued by "a polynomial vanishing
on the (infinite) nonzero locus is zero."

This is the exact bridge for the clock family: `commuting_family_scaling_character` yields a character
multiplicative on `C^*`, and this identifies it with `λ ↦ λ^k` — feeding `charged_clock_family_pow`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- A polynomial over an algebraically closed field that vanishes on every nonzero point is zero;
the nonzero locus is infinite. -/
private theorem eq_zero_of_eval_zero_on_nonzero {C : Type*} [Field C] [IsAlgClosed C]
    {P : Polynomial C} (h : ∀ t : C, t ≠ 0 → P.eval t = 0) : P = 0 := by
  have hinf : {x : C | x ≠ 0}.Infinite := by
    have h0 := (Set.finite_singleton (0 : C)).infinite_compl
    rwa [Set.compl_singleton_eq] at h0
  exact Polynomial.eq_zero_of_infinite_isRoot P (hinf.mono (fun t ht => h t ht))

/-- **Nonzero-multiplicative polynomials are monomials.**  Over an algebraically closed field a
nonzero polynomial with `P(xy) = P(x)P(y)` for all nonzero `x, y` equals `X ^ (deg P)`. -/
theorem multiplicative_polynomial_eq_X_pow_of_nonzero {C : Type*} [Field C] [IsAlgClosed C]
    {P : Polynomial C} (hP : P ≠ 0)
    (hmul : ∀ x y : C, x ≠ 0 → y ≠ 0 → P.eval (x * y) = P.eval x * P.eval y) :
    P = Polynomial.X ^ P.natDegree := by
  have hev1 : P.eval 1 = 1 := by
    have h := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    have hsq : P.eval 1 * (P.eval 1 - 1) = 0 := by rw [mul_sub, mul_one]; linear_combination -h
    rcases mul_eq_zero.mp hsq with h0 | h0
    · exact absurd (eq_zero_of_eval_zero_on_nonzero (fun t ht => by
        have := hmul 1 t one_ne_zero ht; rwa [one_mul, h0, zero_mul] at this)) hP
    · exact sub_eq_zero.mp h0
  have hnr : ∀ r ∈ P.roots, r = 0 := by
    intro r hr'
    by_contra hr0
    have hev : P.eval r = 0 := Polynomial.isRoot_of_mem_roots hr'
    exact hP (eq_zero_of_eval_zero_on_nonzero (fun t ht => by
      have hh := hmul r (r⁻¹ * t) hr0 (mul_ne_zero (inv_ne_zero hr0) ht)
      rwa [mul_inv_cancel_left₀ hr0, hev, zero_mul] at hh))
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hprod := hsplit.eq_prod_roots
  have hmapeq : (P.roots.map (fun x => X - Polynomial.C x))
      = Multiset.replicate P.roots.card X := by
    rw [show (P.roots.map (fun x => X - Polynomial.C x))
        = P.roots.map (fun _ => (X : Polynomial C)) from
      Multiset.map_congr rfl (fun r hr' => by rw [hnr r hr']; simp)]
    exact Multiset.map_const' _ _
  rw [hmapeq, Multiset.prod_replicate] at hprod
  have hcard : P.roots.card = P.natDegree :=
    (Polynomial.splits_iff_card_roots.mp hsplit)
  rw [hcard] at hprod
  have hlead : P.leadingCoeff = 1 := by
    have he : P.eval 1 = P.leadingCoeff := by rw [hprod]; simp
    rw [hev1] at he; exact he.symm
  rw [hlead, map_one, one_mul] at hprod
  exact hprod

/-- **Nonzero-multiplicative polynomial characters are `λ^k`.**  A map `e : C → C` given by a nonzero
polynomial and multiplicative on the nonzero elements is `e(λ) = λ^k` (for every `λ`, including `0`,
since `e = P.eval` is total). -/
theorem multiplicative_eval_eq_pow_of_nonzero {C : Type*} [Field C] [IsAlgClosed C]
    {P : Polynomial C} (hP : P ≠ 0) (e : C → C)
    (he : ∀ lam, e lam = P.eval lam)
    (hmul : ∀ lam mu, lam ≠ 0 → mu ≠ 0 → e (lam * mu) = e lam * e mu) :
    ∃ k : ℕ, ∀ lam, e lam = lam ^ k := by
  have hpmul : ∀ x y : C, x ≠ 0 → y ≠ 0 → P.eval (x * y) = P.eval x * P.eval y := by
    intro x y hx hy; rw [← he x, ← he y, ← he (x * y)]; exact hmul x y hx hy
  have hX : P = Polynomial.X ^ P.natDegree := multiplicative_polynomial_eq_X_pow_of_nonzero hP hpmul
  refine ⟨P.natDegree, fun lam => ?_⟩
  rw [he lam]
  nth_rewrite 1 [hX]
  rw [Polynomial.eval_pow, Polynomial.eval_X]

end GaloisForLFunctions.HTGeometry
