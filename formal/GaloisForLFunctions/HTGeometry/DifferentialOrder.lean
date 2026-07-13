import Mathlib
import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# Differential algebraicity graded by order

The order-graded form of differential algebraicity: `DifferentiallyAlgebraicOfOrder f n`
holds when some nonzero differential polynomial in the point and the jets up to order `n`
annihilates `f`.  Order is monotone — an order-`n` relation is an order-`m` relation for
every `m ≥ n`, by renaming the jet frame along the initial inclusion
(`DifferentiallyAlgebraicOfOrder.mono`) — and differential algebraicity is exactly the
existence of some finite order (`differentiallyAlgebraic_iff_exists_order`).  This is the
vocabulary of differential-order cost laws: a minimal-order statement asserts an order-`n`
relation together with the failure of every order below it.
-/

open MvPolynomial

namespace GaloisForLFunctions

/-- `f` satisfies a nonzero algebraic differential equation of order at most `n`. -/
def DifferentiallyAlgebraicOfOrder (f : ℂ → ℂ) (n : ℕ) : Prop :=
  ∃ P : MvPolynomial (Fin (n + 2)) ℂ, P ≠ 0 ∧
    ∀ z : ℂ, MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0

/-- Differential algebraicity is the existence of some finite order. -/
theorem differentiallyAlgebraic_iff_exists_order {f : ℂ → ℂ} :
    DifferentiallyAlgebraic f ↔ ∃ n, DifferentiallyAlgebraicOfOrder f n :=
  Iff.rfl

/-- One padding step: an order-`n` relation is an order-`n+1` relation. -/
theorem DifferentiallyAlgebraicOfOrder.succ {f : ℂ → ℂ} {n : ℕ}
    (h : DifferentiallyAlgebraicOfOrder f n) : DifferentiallyAlgebraicOfOrder f (n + 1) := by
  obtain ⟨P, hP0, hPz⟩ := h
  refine ⟨rename (Fin.castSucc) P, ?_, ?_⟩
  · intro h0
    exact hP0 (MvPolynomial.rename_injective _ (Fin.castSucc_injective _) (by
      rw [h0, map_zero]))
  · intro z
    rw [MvPolynomial.eval_rename]
    have hvec : ((Fin.cons z fun j : Fin (n + 2) => iteratedDeriv (j : ℕ) f z)
          ∘ (Fin.castSucc : Fin (n + 2) → Fin (n + 3)))
        = Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z := by
      funext i
      induction i using Fin.cases with
      | zero => simp
      | succ j =>
        simp only [Function.comp_apply, ← Fin.succ_castSucc, Fin.cons_succ,
          Fin.val_castSucc]
    rw [hvec]
    exact hPz z

/-- **Order monotonicity**: an order-`n` relation is an order-`m` relation for every
`m ≥ n`. -/
theorem DifferentiallyAlgebraicOfOrder.mono {f : ℂ → ℂ} {n m : ℕ}
    (h : DifferentiallyAlgebraicOfOrder f n) (hnm : n ≤ m) :
    DifferentiallyAlgebraicOfOrder f m := by
  induction m with
  | zero =>
    have hn0 : n = 0 := Nat.le_zero.mp hnm
    rwa [hn0] at h
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · exact (ih (by omega)).succ
    · have hn : n = m + 1 := by omega
      rwa [hn] at h

/-- A hypertranscendental function admits no relation of any order. -/
theorem Hypertranscendental.not_differentiallyAlgebraicOfOrder {f : ℂ → ℂ}
    (hf : Hypertranscendental f) (n : ℕ) : ¬ DifferentiallyAlgebraicOfOrder f n :=
  fun h => hf ⟨n, h⟩

end GaloisForLFunctions
