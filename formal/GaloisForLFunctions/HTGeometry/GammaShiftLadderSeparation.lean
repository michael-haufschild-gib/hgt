import GaloisForLFunctions.HTGeometry.GammaShiftLadderCoeffTop

/-!
# The shifted ladder separates exponent vectors

`finite-archimedean-gamma-product-boundary-law` §5 reads the residues of `∑_k e_k ψ(s+λ_k)` at
`s^{-m}` and recovers `e` from them.  The two facts that make this work are now Lean-proved:

* `natDegree_shiftLadderCoeffPoly` — `d_m` is a polynomial in the shift of degree exactly `m+1`;
* `shiftLadderCoeffPoly_coeff_top_ne_zero` — its top coefficient is `(-1)^{m+1}/(m+1) ≠ 0`.

So `1, d_0, d_1, …, d_{r-2}` is a *triangular* family of degrees `0,1,…,r-1`, hence spans every
polynomial of degree below `r`; feeding in the Lagrange basis of the `λ_k` recovers each coordinate.
No `NoIntegerRelation` hypothesis appears: distinctness of the shifts is all that is used, which is
exactly the situation of commensurable scales that defeated the order-one signature.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- **Triangularity**: vanishing of the constant moment and of the first `r-1` ladder moments forces
every polynomial moment of degree below `r` to vanish. -/
theorem sum_eval_eq_zero_of_ladder_moments {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℂ)
    (h0 : ∑ k, g k = 0)
    (hm : ∀ m : ℕ, m + 2 ≤ r → ∑ k, g k * shiftLadderCoeff (lam k) m = 0) :
    ∀ (P : Polynomial ℂ), P.natDegree < r → ∑ k, g k * P.eval (lam k) = 0 := by
  have hmp : ∀ m : ℕ, m + 2 ≤ r →
      ∑ k, g k * (shiftLadderCoeffPoly m).eval (lam k) = 0 := by
    intro m hmr
    have h := hm m hmr
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => by rw [shiftLadderCoeff_eq_eval]
  have key : ∀ j : ℕ, j < r → ∀ P : Polynomial ℂ, P.natDegree ≤ j →
      ∑ k, g k * P.eval (lam k) = 0 := by
    intro j
    induction j with
    | zero =>
        intro _ P hP
        have hC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hP
        rw [hC]
        simp only [Polynomial.eval_C]
        rw [← Finset.sum_mul, h0, zero_mul]
    | succ i ih =>
        intro hr P hP
        have hir : i + 2 ≤ r := by omega
        set D : Polynomial ℂ := shiftLadderCoeffPoly i with hD
        have hDdeg : D.natDegree = i + 1 := natDegree_shiftLadderCoeffPoly i
        have ht : D.coeff (i + 1) ≠ 0 := shiftLadderCoeffPoly_coeff_top_ne_zero i
        obtain ⟨a, ha⟩ : ∃ a : ℂ, a * D.coeff (i + 1) = P.coeff (i + 1) :=
          ⟨P.coeff (i + 1) / D.coeff (i + 1), by field_simp⟩
        set P' : Polynomial ℂ := P - Polynomial.C a * D with hP'
        have hmulle : (Polynomial.C a * D).natDegree ≤ i + 1 := by
          refine le_trans (Polynomial.natDegree_C_mul_le a D) ?_
          rw [hDdeg]
        have hP'le : P'.natDegree ≤ i + 1 := by
          rw [hP']
          exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le hP hmulle)
        have hP'top : P'.coeff (i + 1) = 0 := by
          rw [hP', Polynomial.coeff_sub, Polynomial.coeff_C_mul, ha, sub_self]
        have hP'lt : P'.natDegree ≤ i := by
          rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
          intro m hm'
          rcases Nat.lt_or_ge m (i + 1) with h | h
          · omega
          · rcases Nat.eq_or_lt_of_le h with h' | h'
            · rw [← h']; exact hP'top
            · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP'le h')
        have hIH := ih (by omega) P' hP'lt
        have hDsum := hmp i hir
        have hsplit : ∀ k : Fin r, g k * P.eval (lam k)
            = g k * P'.eval (lam k) + a * (g k * D.eval (lam k)) := by
          intro k
          rw [hP']
          simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
          ring
        rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib,
          ← Finset.mul_sum, hIH, hDsum]
        ring
  intro P hP
  exact key P.natDegree hP P le_rfl

/-- **The ladder moments separate**: distinct shifts and vanishing moments force the coefficient
vector to vanish. -/
theorem eq_zero_of_ladder_moments_vanish {r : ℕ} (lam : Fin r → ℂ)
    (hinj : Function.Injective lam) (g : Fin r → ℂ)
    (h0 : ∑ k, g k = 0)
    (hm : ∀ m : ℕ, m + 2 ≤ r → ∑ k, g k * shiftLadderCoeff (lam k) m = 0) :
    ∀ k, g k = 0 := by
  classical
  intro k0
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exact absurd k0.isLt (by omega)
    · exact h
  have hinjOn : Set.InjOn lam ((Finset.univ : Finset (Fin r)) : Set (Fin r)) :=
    Set.injOn_of_injective hinj
  set B : Polynomial ℂ := Lagrange.basis (Finset.univ : Finset (Fin r)) lam k0 with hB
  have hdeg : B.natDegree = (Finset.univ : Finset (Fin r)).card - 1 :=
    Lagrange.natDegree_basis hinjOn (Finset.mem_univ k0)
  have hcard : (Finset.univ : Finset (Fin r)).card = r := by simp
  have hdegr : B.natDegree < r := by rw [hdeg, hcard]; omega
  have hsum := sum_eval_eq_zero_of_ladder_moments lam g h0 hm B hdegr
  have hval : ∑ k, g k * B.eval (lam k) = g k0 := by
    rw [Finset.sum_eq_single k0]
    · rw [Lagrange.eval_basis_self hinjOn (Finset.mem_univ k0), mul_one]
    · intro b _ hb
      rw [Lagrange.eval_basis_of_ne (Ne.symm hb) (Finset.mem_univ b), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k0) h
  rw [hval] at hsum
  exact hsum

end

end GaloisForLFunctions.HTGeometry
