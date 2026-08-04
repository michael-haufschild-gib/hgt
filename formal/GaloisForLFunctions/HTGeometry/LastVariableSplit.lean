import GaloisForLFunctions.HTGeometry.MultiVarAlgebraicBound

/-!
# Splitting off the last variable of a multivariate polynomial

`MvPolynomial.finSuccEquiv` splits off the *first* variable.  Reading a relation among states in the
*last* one — the newest state of a cascade — needs the corresponding renaming, which is the cycle
carrying the last index to the head.

With it, a relation among `(X_0, …, X_{m-1}, F)` becomes a polynomial in `F` whose coefficients are
polynomials in the earlier states, of positive degree as soon as those states admit no relation of
their own.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- The renaming that moves the last variable to the head. -/
def lastHead (m : ℕ) : Fin (m + 1) → Fin (m + 1) :=
  fun i => if h : (i : ℕ) < m then (⟨i, h⟩ : Fin m).succ else 0

theorem lastHead_castSucc {m : ℕ} (j : Fin m) :
    lastHead m (Fin.castSucc j) = j.succ := by
  have h : ((Fin.castSucc j : Fin (m + 1)) : ℕ) < m := by simp
  rw [lastHead, dif_pos h]
  rfl

theorem lastHead_last (m : ℕ) : lastHead m (Fin.last m) = 0 := by
  rw [lastHead, dif_neg (by simp)]

theorem lastHead_injective (m : ℕ) : Function.Injective (lastHead m) := by
  intro i i'
  refine Fin.lastCases ?_ ?_ i
  · refine Fin.lastCases ?_ ?_ i'
    · intro _
      rfl
    · intro j hj
      rw [lastHead_last, lastHead_castSucc] at hj
      exact absurd hj.symm (Fin.succ_ne_zero j)
  · intro j
    refine Fin.lastCases ?_ ?_ i'
    · intro hj
      rw [lastHead_castSucc, lastHead_last] at hj
      exact absurd hj (Fin.succ_ne_zero j)
    · intro j' hj
      rw [lastHead_castSucc, lastHead_castSucc] at hj
      rw [Fin.succ_inj.mp hj]

/-- The renaming turns a head-extended vector into a tail-extended one. -/
theorem cons_comp_lastHead {m : ℕ} {α : Type*} (w : Fin m → α) (y : α) :
    (Fin.cons y w : Fin (m + 1) → α) ∘ lastHead m = Fin.snoc w y := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [Function.comp_apply, lastHead_last, Fin.cons_zero, Fin.snoc_last]
  · intro j
    simp only [Function.comp_apply, lastHead_castSucc, Fin.cons_succ, Fin.snoc_castSucc]

/-- **A relation among states, read in the last one.**  If the earlier states admit no relation, a
relation involving the last one has positive degree there, with a nonzero top coefficient. -/
theorem exists_top_multi_var_relation {m : ℕ} {X : Fin m → ℂ → ℂ} {F : ℂ → ℂ}
    (hind : ∀ Q : MvPolynomial (Fin m) ℂ, Q ≠ 0 →
      ¬ (∀ z : ℂ, MvPolynomial.eval (fun j => X j z) Q = 0))
    {P : MvPolynomial (Fin (m + 1)) ℂ} (hP : P ≠ 0)
    (hrel : ∀ z : ℂ, MvPolynomial.eval (Fin.snoc (fun j => X j z) (F z)) P = 0) :
    ∃ (D : ℕ) (A : ℕ → MvPolynomial (Fin m) ℂ), 1 ≤ D ∧ A D ≠ 0 ∧
      ∀ z : ℂ, ∑ i ∈ Finset.range (D + 1),
        MvPolynomial.eval (fun j => X j z) (A i) * (F z) ^ i = 0 := by
  set Q : MvPolynomial (Fin (m + 1)) ℂ := rename (lastHead m) P with hQ
  have hQ0 : Q ≠ 0 := by
    rw [hQ]
    intro hc
    exact hP (rename_injective (lastHead m) (lastHead_injective m) (by rw [hc, map_zero]))
  set p : Polynomial (MvPolynomial (Fin m) ℂ) := finSuccEquiv ℂ m Q with hp
  have hp0 : p ≠ 0 := by
    rw [hp]
    intro hc
    exact hQ0 ((finSuccEquiv ℂ m).injective (by rw [hc, map_zero]))
  set D : ℕ := p.natDegree with hD
  have hAD : p.coeff D ≠ 0 := by
    rw [hD]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hsum : ∀ z : ℂ, ∑ i ∈ Finset.range (D + 1),
      MvPolynomial.eval (fun j => X j z) (p.coeff i) * (F z) ^ i = 0 := by
    intro z
    have hQeval : MvPolynomial.eval (Fin.cons (F z) (fun j => X j z)) Q = 0 := by
      rw [hQ, eval_rename, cons_comp_lastHead]
      exact hrel z
    have hev := MvPolynomial.eval_eq_eval_mv_eval' (R := ℂ) (n := m)
      (fun j => X j z) (F z) Q
    rw [← hp, hQeval] at hev
    have hdeg : (Polynomial.map (MvPolynomial.eval (fun j => X j z)) p).natDegree < D + 1 :=
      Nat.lt_succ_of_le (le_trans Polynomial.natDegree_map_le (le_of_eq hD.symm))
    rw [Polynomial.eval_eq_sum_range' hdeg] at hev
    rw [← hev.symm]
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [Polynomial.coeff_map]
  rcases Nat.eq_zero_or_pos D with hD0 | hD1
  · exfalso
    refine hind (p.coeff 0) ?_ ?_
    · rw [hD0] at hAD
      exact hAD
    · intro z
      have hz := hsum z
      rw [hD0] at hz
      simp only [zero_add, Finset.sum_range_one, pow_zero, mul_one] at hz
      exact hz
  · exact ⟨D, fun i => p.coeff i, hD1, hAD, hsum⟩

end GaloisForLFunctions.HTGeometry
