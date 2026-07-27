import Mathlib

/-!
# Nonzero multivariate polynomials evaluate nonzero on an infinite grid

A nonzero `P : MvPolynomial (Fin r) ℤ` has an **injective** evaluation point whose every
coordinate lies in a prescribed infinite set `T ⊆ ℤ` and at which `P` does not vanish
(`exists_injective_eval_ne_zero`).  Proof is the standard variable-peeling: write `P` as a
univariate polynomial in the first coordinate over `MvPolynomial (Fin r) ℤ`, apply the inductive
hypothesis to a nonzero coefficient to fix the last `r` coordinates in `T` (injectively), then
choose the first coordinate in the still-infinite `T` minus the finitely many already used
coordinates and the finitely many roots of the resulting nonzero univariate polynomial.

This supplies the transfer from "the permanent leading symbol is a nonzero polynomial" to "it is
nonzero at distinct support scales `bnat Mᵢ`" in the distinct-index hypertranscendence argument.
-/

open MvPolynomial Polynomial

namespace GaloisForLFunctions

/-- A nonzero univariate polynomial over an integral domain has a non-root in any infinite set:
its root set is finite. -/
theorem exists_mem_eval_ne_zero_of_infinite_domain {R : Type*} [CommRing R] [IsDomain R]
    (p : Polynomial R) (hp : p ≠ 0) {S : Set R}
    (hS : S.Infinite) : ∃ x ∈ S, p.eval x ≠ 0 := by
  classical
  have hfin : {x : R | p.eval x = 0}.Finite := by
    apply Set.Finite.subset (p.roots.toFinset.finite_toSet)
    intro x hx
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hp, hx⟩
  obtain ⟨x, hxS, hx⟩ := (hS.diff hfin).nonempty
  exact ⟨x, hxS, hx⟩

/-- **Injective non-vanishing evaluation over an integral domain.**  A nonzero
`P : MvPolynomial (Fin r) R` has an injective evaluation point with every coordinate in a
prescribed infinite `T ⊆ R` at which `P` does not vanish.  Variable peeling: view `P` as a
univariate polynomial in the first coordinate, fix the last `r` coordinates by induction so one
coefficient survives, then pick the first coordinate in `T` minus the finitely many already used
coordinates and the finitely many roots of the resulting univariate polynomial. -/
theorem exists_injective_eval_ne_zero_domain {R : Type*} [CommRing R] [IsDomain R] :
    ∀ {r : ℕ} (P : MvPolynomial (Fin r) R), P ≠ 0 → ∀ {T : Set R}, T.Infinite →
      ∃ a : Fin r → R, Function.Injective a ∧ (∀ i, a i ∈ T) ∧ MvPolynomial.eval a P ≠ 0 := by
  intro r
  induction r with
  | zero =>
    intro P hP _ hT
    refine ⟨Fin.elim0, Function.injective_of_subsingleton _, fun i => i.elim0, ?_⟩
    intro hcontra
    apply hP
    obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective (Fin 0) P
    rw [MvPolynomial.eval_C] at hcontra
    rw [hcontra, map_zero]
  | succ r IH =>
    intro P hP T hT
    set Q := (MvPolynomial.finSuccEquiv R r) P with hQdef
    have hQ : Q ≠ 0 := (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv R r).injective).mpr hP
    obtain ⟨k, hk⟩ : ∃ n, Q.coeff n ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ (Polynomial.ext (fun n => by rw [h n, Polynomial.coeff_zero]))
    -- fix the last r coordinates so the k-th coefficient survives
    obtain ⟨a', ha'inj, ha'T, ha'ne⟩ := IH (Q.coeff k) hk hT
    -- the resulting univariate polynomial is nonzero
    set Q' := Q.map (MvPolynomial.eval a') with hQ'def
    have hQ'k : Q'.coeff k ≠ 0 := by rw [hQ'def, Polynomial.coeff_map]; exact ha'ne
    have hQ' : Q' ≠ 0 := fun h => hQ'k (by rw [h]; simp)
    -- choose the first coordinate in T avoiding the used values and the roots
    have hTinf : (T \ Set.range a').Infinite := hT.diff (Set.finite_range a')
    obtain ⟨y, hyT, hyne⟩ := exists_mem_eval_ne_zero_of_infinite_domain Q' hQ' hTinf
    refine ⟨Fin.cons y a', ?_, ?_, ?_⟩
    · intro i j hij
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rfl
      · rw [Fin.cons_zero, Fin.cons_succ] at hij
        exact absurd ⟨j', hij.symm⟩ hyT.2
      · rw [Fin.cons_zero, Fin.cons_succ] at hij
        exact absurd ⟨i', hij⟩ hyT.2
      · rw [Fin.cons_succ, Fin.cons_succ] at hij
        rw [ha'inj hij]
    · intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · rw [Fin.cons_zero]; exact hyT.1
      · rw [Fin.cons_succ]; exact ha'T i'
    · rw [MvPolynomial.eval_eq_eval_mv_eval', ← hQdef, ← hQ'def]
      exact hyne

/-- A nonzero integer univariate polynomial has a non-root in any infinite set of integers. -/
theorem exists_mem_eval_ne_zero_of_infinite (p : Polynomial ℤ) (hp : p ≠ 0) {S : Set ℤ}
    (hS : S.Infinite) : ∃ x ∈ S, p.eval x ≠ 0 :=
  exists_mem_eval_ne_zero_of_infinite_domain p hp hS

/-- **Infinite-grid nonvanishing.**  A nonzero `MvPolynomial (Fin r) ℤ` is nonzero at some
injective tuple valued in any infinite integer set. -/
theorem exists_injective_eval_ne_zero :
    ∀ {r : ℕ} (P : MvPolynomial (Fin r) ℤ), P ≠ 0 → ∀ {T : Set ℤ}, T.Infinite →
      ∃ a : Fin r → ℤ, Function.Injective a ∧ (∀ i, a i ∈ T) ∧ MvPolynomial.eval a P ≠ 0 :=
  fun {_r} P hP {_T} hT => exists_injective_eval_ne_zero_domain P hP hT

end GaloisForLFunctions
