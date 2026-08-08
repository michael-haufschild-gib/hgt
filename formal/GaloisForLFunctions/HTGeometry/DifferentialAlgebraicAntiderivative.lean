import GaloisForLFunctions.HTGeometry.DifferentialAdjoinFiniteTrdeg
import GaloisForLFunctions.HTGeometry.AffineFirstOrderDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicTransitivity
import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# Antiderivatives of differentially algebraic elements

Differential algebraicity is stable under integration, not only under differentiation.  If `y′` is
differentially algebraic over `k`, then the differential field `k⟨y′⟩` has finite transcendence
degree, `y` satisfies the first-order relation `y′ = c` with `c ∈ k⟨y′⟩`, and finite-transcendence
descent returns a relation over `k` itself.

The analytic counterpart is a pure change of jet coordinates: a differential relation among the
jets of `f'` is a relation among the jets of `f` after shifting every slot by one.

* `differentialAlgebraicOver_of_deriv` — the field statement;
* `differentiallyAlgebraic_of_deriv` — the statement for functions on `ℂ`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- **Differential algebraicity passes to antiderivatives.**  If the derivative of `y` is
differentially algebraic over `k`, so is `y`. -/
theorem differentialAlgebraicOver_of_deriv
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Differential k] [Differential K] [DifferentialAlgebra k K] [CharZero K]
    {y : K} (hy : DifferentialAlgebraicOver k y′) :
    DifferentialAlgebraicOver k y := by
  set F : IntermediateField k K := differentialAdjoin k ({y′} : Set K) with hF
  have hmem : y′ ∈ F := subset_differentialAdjoin k ({y′} : Set K) rfl
  have hclosed : DerivationClosed F := derivationClosed_differentialAdjoin k _
  have hfinite : Algebra.trdeg k F < Cardinal.aleph0 :=
    differentialAdjoin_trdeg_lt_aleph0_of_differentialAlgebraic hy
  have hyF : DifferentialAlgebraicOver F y :=
    differentialAlgebraicOver_of_deriv_eq_base (F := F) (E := K) ⟨y′, hmem⟩ rfl
  exact differentialAlgebraicOver_of_intermediate_trdeg_lt_aleph0 F hclosed hfinite hyF

/-! ### The analytic form -/

/-- The jet reindexing that turns a relation among the jets of `f'` into one among the jets of
`f`: the point slot is fixed and every value slot moves up by one. -/
def jetShiftIndex (n : ℕ) : Fin (n + 2) → Fin (n + 3) :=
  fun i => if i = 0 then 0 else i.succ

theorem jetShiftIndex_injective (n : ℕ) : Function.Injective (jetShiftIndex n) := by
  intro i j hij
  simp only [jetShiftIndex] at hij
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · rw [hi, hj]
  · rw [if_pos hi, if_neg hj] at hij
    exact absurd hij.symm (Fin.succ_ne_zero j)
  · rw [if_neg hi, if_pos hj] at hij
    exact absurd hij (Fin.succ_ne_zero i)
  · rw [if_neg hi, if_neg hj] at hij
    exact Fin.succ_injective _ hij

/-- **A function whose derivative is differentially algebraic is differentially algebraic.** -/
theorem differentiallyAlgebraic_of_deriv {f : ℂ → ℂ}
    (hf : DifferentiallyAlgebraic (deriv f)) : DifferentiallyAlgebraic f := by
  obtain ⟨n, P, hP, hrel⟩ := hf
  refine ⟨n + 1, MvPolynomial.rename (jetShiftIndex n) P, ?_, ?_⟩
  · exact fun h => hP (MvPolynomial.rename_injective _ (jetShiftIndex_injective n) (by simpa using h))
  · intro z
    rw [MvPolynomial.eval_rename]
    have hcomp : (Fin.cons z (fun j : Fin (n + 2) => iteratedDeriv (j : ℕ) f z) :
          Fin (n + 3) → ℂ) ∘ jetShiftIndex n
        = Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (deriv f) z) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [jetShiftIndex]
      · intro j
        have hne : (Fin.succ j : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero j
        simp only [Function.comp_apply, jetShiftIndex, if_neg hne, Fin.cons_succ]
        rw [Fin.val_succ, iteratedDeriv_succ']
    rw [hcomp]
    exact hrel z

end GaloisForLFunctions.HTGeometry
