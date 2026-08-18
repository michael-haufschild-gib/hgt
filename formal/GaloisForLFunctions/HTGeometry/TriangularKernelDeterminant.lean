import GaloisForLFunctions.HTGeometry.FredholmDeterminantExamples

/-!
# Determinant blindness of a strictly triangular kernel

A Hilbert--Schmidt kernel supported strictly above the diagonal of the graded index set has
vanishing diagonal in every power, hence vanishing trace in every power.  The regularized
determinant exponent is therefore identically zero and

```text
det₂(1 − zK) = det₁(1 − zK) = 1     for every complex z.
```

No convergence hypothesis is needed: the exponent series is termwise zero.  This is the
infinite-dimensional half of the statement that a strictly filtration-lowering defect carries no
determinant invariant.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.TriangularKernel

open HilbertSchmidt

theorem tsum_eq_zero_of_forall {α : Type*} {f : α → ℂ} (h : ∀ a, f a = 0) : ∑' a, f a = 0 := by
  have hf : f = fun _ => (0 : ℂ) := funext h
  rw [hf, tsum_zero]

/-- A kernel supported strictly above the diagonal of the graded index set. -/
def StrictlyUpperKernel (K : ℕ × ℕ → ℂ) : Prop := ∀ i j : ℕ, j ≤ i → K (i, j) = 0

/-- Every kernel power of a strictly triangular kernel is supported one step further above the
diagonal. -/
theorem hsPow_eq_zero_of_strictlyUpper {K : ℕ × ℕ → ℂ} (hK : StrictlyUpperKernel K) :
    ∀ (n i j : ℕ), j ≤ i + n → hsPow K n (i, j) = 0 := by
  intro n
  induction n with
  | zero =>
      intro i j hij
      exact hK i j (by omega)
  | succ n ih =>
      intro i j hij
      show hsComp K (hsPow K n) (i, j) = 0
      rw [hsComp]
      refine tsum_eq_zero_of_forall (fun k => ?_)
      by_cases hk : k ≤ i
      · rw [hK i k hk, zero_mul]
      · rw [ih k j (by omega), mul_zero]

/-- The diagonal of every kernel power vanishes. -/
theorem hsPow_diag_eq_zero {K : ℕ × ℕ → ℂ} (hK : StrictlyUpperKernel K) (n i : ℕ) :
    hsPow K n (i, i) = 0 :=
  hsPow_eq_zero_of_strictlyUpper hK n i i (by omega)

/-- **The regularized determinant exponent of a strictly triangular kernel vanishes identically.** -/
theorem fredholmExp_eq_zero {K : ℕ × ℕ → ℂ} (hK : StrictlyUpperKernel K) (z : ℂ) :
    fredholmExp K z = 0 := by
  rw [fredholmExp]
  refine tsum_eq_zero_of_forall (fun n => ?_)
  have hinner : (∑' i : ℕ, hsPow K (n + 1) (i, i)) = 0 :=
    tsum_eq_zero_of_forall (fun i => hsPow_diag_eq_zero hK (n + 1) i)
  rw [hinner, mul_zero]

/-- **The regularized Fredholm determinant is identically one.** -/
theorem fredholmDet_eq_one {K : ℕ × ℕ → ℂ} (hK : StrictlyUpperKernel K) (z : ℂ) :
    fredholmDet K z = 1 := by
  rw [fredholmDet, fredholmExp_eq_zero hK, neg_zero, Complex.exp_zero]

/-- The diagonal trace of a strictly triangular kernel vanishes. -/
theorem hsTraceDiag_eq_zero {K : ℕ × ℕ → ℂ} (hK : StrictlyUpperKernel K) :
    hsTraceDiag K = 0 := by
  rw [hsTraceDiag]
  exact tsum_eq_zero_of_forall (fun i => hK i i le_rfl)

/-- **Determinant blindness.**  The trace-class Fredholm determinant of a strictly triangular
kernel is identically one, for every complex `z`. -/
theorem fredholmDet1_eq_one {K : ℕ × ℕ → ℂ} (hK : StrictlyUpperKernel K) (z : ℂ) :
    fredholmDet1 K z = 1 := by
  rw [fredholmDet1, fredholmDet_eq_one hK, hsTraceDiag_eq_zero hK, mul_zero, neg_zero,
    Complex.exp_zero, mul_one]

end GaloisForLFunctions.HTGeometry.TriangularKernel
