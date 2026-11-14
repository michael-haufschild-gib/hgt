import GaloisForLFunctions.HTGeometry.Polynomial.QuadraticLifting
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Quartic equations for polynomial zero sets

Squaring and summing the equations of a quadratic lifting gives a single
integer polynomial of degree at most four. Its rational zeros project
exactly to the original zero set. The construction works for every
integer polynomial, without any assumption on its zeros.
-/

namespace GaloisForLFunctions.HTGeometry.Polynomial

open MvPolynomial

universe u

namespace QuadraticLift

variable {σ : Type u} {p : MvPolynomial σ ℤ}

/-- Sum of squares of all gate errors and the linear output. -/
noncomputable def quartic (L : QuadraticLift p) : MvPolynomial (σ ⊕ L.Aux) ℤ :=
  L.output ^ 2 + ∑ a, L.constraints a ^ 2

theorem quartic_totalDegree (L : QuadraticLift p) : L.quartic.totalDegree ≤ 4 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_pow _ _).trans (by have h := L.output_degree; omega)
  · apply totalDegree_finsetSum_le
    intro a _
    exact (totalDegree_pow _ _).trans (by have h := L.constraint_degree a; omega)

theorem quartic_eval_zero_iff (L : QuadraticLift p) (x : σ → ℚ) (w : L.Aux → ℚ) :
    rationalEval (Sum.elim x w) L.quartic = 0 ↔
      rationalEval (Sum.elim x w) L.output = 0 ∧
        ∀ a, rationalEval (Sum.elim x w) (L.constraints a) = 0 := by
  classical
  rw [quartic, map_add, map_pow, map_sum]
  simp only [map_pow]
  have hsum : 0 ≤ ∑ a, (rationalEval (Sum.elim x w) (L.constraints a)) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hout := sq_nonneg (rationalEval (Sum.elim x w) L.output)
  constructor
  · intro h
    have ho : (rationalEval (Sum.elim x w) L.output) ^ 2 = 0 := by
      linarith only [h, hsum, hout]
    have hs : ∑ a, (rationalEval (Sum.elim x w) (L.constraints a)) ^ 2 = 0 := by
      linarith only [h, ho]
    refine ⟨sq_eq_zero_iff.mp ho, ?_⟩
    intro a
    exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => sq_nonneg (rationalEval (Sum.elim x w) (L.constraints b)))).mp hs a
        (Finset.mem_univ a))
  · rintro ⟨ho, hc⟩
    simp only [ho, hc, zero_pow (by omega : 2 ≠ 0), Finset.sum_const_zero, add_zero]

/-- Every original zero has a lift, and every quartic zero projects to
an original zero. -/
theorem exists_quartic_zero_iff (L : QuadraticLift p) (x : σ → ℚ) :
    (∃ w : L.Aux → ℚ, rationalEval (Sum.elim x w) L.quartic = 0) ↔
      rationalEval x p = 0 := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨hout, hc⟩ := (L.quartic_eval_zero_iff x w).mp hw
    exact (L.sound x w hc).symm.trans hout
  · intro hp
    obtain ⟨w, hw⟩ := L.complete x
    exact ⟨w, (L.quartic_eval_zero_iff x w).mpr ⟨(L.sound x w hw).trans hp, hw⟩⟩

end QuadraticLift

/-- Every integer polynomial equation is the rational projection of one
integer quartic equation in finitely many additional variables. -/
theorem exists_quartic_encoding {σ : Type u} (p : MvPolynomial σ ℤ) :
    ∃ (N : ℕ) (Q : MvPolynomial (σ ⊕ Fin N) ℤ), Q.totalDegree ≤ 4 ∧
      ∀ x : σ → ℚ, rationalEval x p = 0 ↔
        ∃ w : Fin N → ℚ, rationalEval (Sum.elim x w) Q = 0 := by
  classical
  obtain ⟨L⟩ := exists_quadraticLift p
  let e := Fintype.equivFin L.Aux
  refine ⟨Fintype.card L.Aux, auxiliaryRename e L.quartic,
    (totalDegree_auxiliaryRename_le _ _).trans L.quartic_totalDegree, ?_⟩
  intro x
  constructor
  · intro hp
    obtain ⟨w, hw⟩ := (L.exists_quartic_zero_iff x).mpr hp
    refine ⟨w ∘ e.symm, ?_⟩
    rw [rationalEval_auxiliaryRename]
    have he : (w ∘ e.symm) ∘ e = w := by
      funext a
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rwa [he]
  · rintro ⟨w, hw⟩
    apply (L.exists_quartic_zero_iff x).mp
    exact ⟨w ∘ e, (rationalEval_auxiliaryRename e L.quartic x w).symm.trans hw⟩

#print axioms exists_quartic_encoding

end GaloisForLFunctions.HTGeometry.Polynomial
