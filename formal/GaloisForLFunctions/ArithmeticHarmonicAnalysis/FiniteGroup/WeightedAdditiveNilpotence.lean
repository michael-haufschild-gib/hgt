import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Logic.Function.Iterate

/-!
# Nilpotence from strict descent of coefficient weights

A map that only moves coefficients to lower natural-number weights
kills every vector after a bounded number of iterations. For additive
maps preserving scalar lines, it suffices to check descent on a basis;
linearity over the coefficient field is not required.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Strict coefficient-weight descent kills vectors supported below the number of iterations. -/
theorem iterate_zero_of_coefficient_weight_descent
    {V A ι : Type*} [Zero V] [Zero A] (T : V → V) (coefficient : V → ι → A)
    (weight : ι → ℕ)
    (hdetect : ∀ v, (∀ i, coefficient v i = 0) → v = 0)
    (hstep : ∀ v i, (∀ j, weight i < weight j → coefficient v j = 0) →
      coefficient (T v) i = 0)
    (e : ℕ) (v : V) (hv : ∀ i, e ≤ weight i → coefficient v i = 0) :
    T^[e] v = 0 := by
  induction e generalizing v with
  | zero => exact hdetect v (fun i => hv i (Nat.zero_le _))
  | succ e ih =>
    change T^[e] (T v) = 0
    apply ih
    intro i hi
    apply hstep
    intro j hj
    exact hv j (Nat.succ_le_of_lt (lt_of_le_of_lt hi hj))

/-- An additive map preserving scalar lines and strictly lowering basis weights is nilpotent. -/
theorem additive_basis_weight_descent_nilpotent
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (B : Module.Basis ι K V) (T : V →+ V) (weight : ι → ℕ)
    (hscalar : ∀ a : K, ∀ v : V, ∃ b : K, T (a • v) = b • T v)
    (hlower : ∀ j i, weight j ≤ weight i → B.repr (T (B j)) i = 0)
    (N : ℕ) (hbound : ∀ i, weight i < N) (v : V) :
    (T : V → V)^[N] v = 0 := by
  classical
  have hdetect : ∀ v : V, (∀ i, B.repr v i = 0) → v = 0 := by
    intro v hv
    apply B.repr.injective
    apply Finsupp.ext
    intro i
    rw [map_zero, Finsupp.zero_apply]
    exact hv i
  have hstep : ∀ v : V, ∀ i,
      (∀ j, weight i < weight j → B.repr v j = 0) → B.repr (T v) i = 0 := by
    intro v i hv
    conv_lhs => rw [← B.sum_repr v]
    rw [map_sum, map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j _
    by_cases h : weight i < weight j
    · rw [hv j h, zero_smul, map_zero, map_zero, Finsupp.zero_apply]
    · obtain ⟨a, ha⟩ := hscalar (B.repr v j) (B j)
      rw [ha, map_smul, Finsupp.smul_apply, hlower j i (le_of_not_gt h), smul_zero]
  apply iterate_zero_of_coefficient_weight_descent (T : V → V) (fun v i => B.repr v i)
    weight hdetect hstep N v
  intro i hi
  exact (not_le_of_gt (hbound i) hi).elim

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
