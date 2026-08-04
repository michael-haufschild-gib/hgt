import GaloisForLFunctions.HTGeometry.FirstOrderDerivativeDegree

/-!
# A three-variable relation, read in its last variable

A polynomial relation between the coordinate and two entire functions, read as a polynomial in the
second function, has positive degree there: degree zero would be a relation between the coordinate
and the first function alone, impossible for a transcendental entire function.

The mechanism is the same as for a first-order differential equation read in the derivative — move the
last variable to the head and apply `MvPolynomial.finSuccEquiv`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open MvPolynomial

/-- **A three-variable relation, in top-degree coefficient form.**  If the coordinate and `F₁` admit
no relation, a relation between `(z, F₁, F₂)` has degree at least one in `F₂`, with a nonzero
two-variable top coefficient. -/
theorem exists_top_two_var_relation {F₁ F₂ : ℂ → ℂ} (hF₁ : TranscendentalEntire F₁)
    {P : MvPolynomial (Fin 3) ℂ} (hP : P ≠ 0)
    (hrel : ∀ z : ℂ, MvPolynomial.eval ![z, F₁ z, F₂ z] P = 0) :
    ∃ (D : ℕ) (A : ℕ → MvPolynomial (Fin 2) ℂ), 1 ≤ D ∧ A D ≠ 0 ∧
      ∀ z : ℂ, ∑ i ∈ Finset.range (D + 1),
        MvPolynomial.eval ![z, F₁ z] (A i) * (F₂ z) ^ i = 0 := by
  set Q : MvPolynomial (Fin 3) ℂ := rename derivHead P with hQ
  have hQ0 : Q ≠ 0 := by
    rw [hQ]
    intro hc
    exact hP (rename_injective derivHead derivHead_injective (by rw [hc, map_zero]))
  set p : Polynomial (MvPolynomial (Fin 2) ℂ) := finSuccEquiv ℂ 2 Q with hp
  have hp0 : p ≠ 0 := by
    rw [hp]
    intro hc
    exact hQ0 ((finSuccEquiv ℂ 2).injective (by rw [hc, map_zero]))
  set D : ℕ := p.natDegree with hD
  have hAD : p.coeff D ≠ 0 := by
    rw [hD]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hsum : ∀ z : ℂ, ∑ i ∈ Finset.range (D + 1),
      MvPolynomial.eval ![z, F₁ z] (p.coeff i) * (F₂ z) ^ i = 0 := by
    intro z
    have hshift : (Fin.cons (F₂ z) ![z, F₁ z] : Fin 3 → ℂ) ∘ derivHead
        = fun i : Fin 3 => ![z, F₁ z, F₂ z] i := by
      funext i
      fin_cases i <;> rfl
    have hQeval : MvPolynomial.eval (Fin.cons (F₂ z) ![z, F₁ z]) Q = 0 := by
      rw [hQ, eval_rename, hshift]
      exact hrel z
    have hev := MvPolynomial.eval_eq_eval_mv_eval' (R := ℂ) (n := 2) ![z, F₁ z] (F₂ z) Q
    rw [← hp, hQeval] at hev
    have hdeg : (Polynomial.map (MvPolynomial.eval ![z, F₁ z]) p).natDegree < D + 1 :=
      Nat.lt_succ_of_le (le_trans Polynomial.natDegree_map_le (le_of_eq hD.symm))
    rw [Polynomial.eval_eq_sum_range' hdeg] at hev
    rw [← hev.symm]
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [Polynomial.coeff_map]
  rcases Nat.eq_zero_or_pos D with hD0 | hD1
  · exfalso
    refine not_differentiallyAlgebraicOfOrder_zero_of_transcendental hF₁.1 hF₁.2
      ⟨p.coeff 0, ?_, ?_⟩
    · rw [hD0] at hAD
      exact hAD
    · intro z
      have hz := hsum z
      rw [hD0] at hz
      simp only [zero_add, Finset.sum_range_one, pow_zero, mul_one] at hz
      have hvec : (Fin.cons z fun j : Fin 1 => iteratedDeriv (j : ℕ) F₁ z) = ![z, F₁ z] := by
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp
        · rw [Fin.cons_succ]
          fin_cases i
          simp [iteratedDeriv_zero]
      rw [hvec]
      exact hz
  · exact ⟨D, fun i => p.coeff i, hD1, hAD, hsum⟩

end GaloisForLFunctions.HTGeometry
