import GaloisForLFunctions.HTGeometry.NumberFieldIntegerFiniteness
import GaloisForLFunctions.HTGeometry.SiegelEntryBound
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanCone
import GaloisForLFunctions.HTGeometry.ComplexCongruenceDiagonal

/-!
# Bounded overlap at every archimedean place

A congruence carrying a uniformly coercive form to a form with bounded diagonal has bounded matrix
entries. This is proved for real symmetric and complex Hermitian forms. Applied at every infinite
place, mixed Minkowski discreteness makes the possible number-ring congruence matrices finite.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField

variable {n : ℕ}

/-- A real congruence between a coercive source and diagonally bounded target has bounded entries. -/
theorem real_congruence_entry_bound
    {c C : ℝ} (hc : 0 < c)
    {A A' G : Matrix (Fin n) (Fin n) ℝ}
    (hlow : ∀ v : Fin n → ℝ,
      c * ∑ k, (v k) ^ 2 ≤ v ⬝ᵥ (A *ᵥ v))
    (hdiag : ∀ i, A' i i ≤ C)
    (hform : A' = G * A * Gᵀ)
    (i j : Fin n) :
    |G i j| ≤ Real.sqrt (C / c) := by
  let γ := Gᵀ
  let v : Fin n → ℝ := fun m => γ m i
  have hv (m : Fin n) : v m = G i m := rfl
  have hquad : A' i i = v ⬝ᵥ (A *ᵥ v) := by
    rw [hform]
    change (γᵀ * A * γ) i i = _
    exact congr_diag_eq_quadForm_col A γ i
  have hsingle : (G i j) ^ 2 ≤ ∑ k, (v k) ^ 2 := by
    rw [← hv j]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ j)
  have hsqc : c * (G i j) ^ 2 ≤ C := by
    calc
      c * (G i j) ^ 2 ≤ c * ∑ k, (v k) ^ 2 :=
        mul_le_mul_of_nonneg_left hsingle hc.le
      _ ≤ v ⬝ᵥ (A *ᵥ v) := hlow v
      _ = A' i i := hquad.symm
      _ ≤ C := hdiag i
  have hsq : (G i j) ^ 2 ≤ C / c := by
    rw [le_div_iff₀ hc]
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs] at hsqrt

/-- A complex Hermitian congruence between a coercive source and diagonally bounded target has
bounded entries. -/
theorem complex_congruence_entry_bound
    {c C : ℝ} (hc : 0 < c)
    {A A' G : Matrix (Fin n) (Fin n) ℂ}
    (hlow : ∀ v : Fin n → ℂ,
      c * ∑ k, ‖v k‖ ^ 2 ≤ (star v ⬝ᵥ (A *ᵥ v)).re)
    (hdiag : ∀ i, (A' i i).re ≤ C)
    (hform : A' = G * A * Gᴴ)
    (i j : Fin n) :
    ‖G i j‖ ≤ Real.sqrt (C / c) := by
  let γ := Gᴴ
  let v : Fin n → ℂ := fun m => γ m i
  have hv (m : Fin n) : v m = star (G i m) := by
    simp [v, γ, Matrix.conjTranspose_apply]
  have hquad : A' i i = star v ⬝ᵥ (A *ᵥ v) := by
    rw [hform]
    simpa [γ, v] using conjCongr_diag_eq_quadForm_col A (Gᴴ) i
  have hsingle : ‖G i j‖ ^ 2 ≤ ∑ k, ‖v k‖ ^ 2 := by
    calc
      ‖G i j‖ ^ 2 = ‖v j‖ ^ 2 := by rw [hv j, norm_star]
      _ ≤ ∑ k, ‖v k‖ ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg ‖v k‖) (Finset.mem_univ j)
  have hsqc : c * ‖G i j‖ ^ 2 ≤ C := by
    calc
      c * ‖G i j‖ ^ 2 ≤ c * ∑ k, ‖v k‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsingle hc.le
      _ ≤ (star v ⬝ᵥ (A *ᵥ v)).re := hlow v
      _ = (A' i i).re := congrArg Complex.re hquad.symm
      _ ≤ C := hdiag i
  have hsq : ‖G i j‖ ^ 2 ≤ C / c := by
    rw [le_div_iff₀ hc]
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at hsqrt

variable {K : Type*} [Field K] [NumberField K]

/-- Real-place congruence witnesses with a common coercivity and diagonal bound. -/
def NumberFieldRealCongruenceBound (c C : ℝ)
    (N : Matrix (Fin n) (Fin n) (𝓞 K)) : Prop :=
  ∀ w : {w : InfinitePlace K // IsReal w},
    ∃ A A' : Matrix (Fin n) (Fin n) ℝ,
      (∀ v : Fin n → ℝ,
        c * ∑ k, (v k) ^ 2 ≤ v ⬝ᵥ (A *ᵥ v)) ∧
      (∀ i, A' i i ≤ C) ∧
      A' = numberFieldRealOrderMatrixAt w N * A *
        (numberFieldRealOrderMatrixAt w N)ᵀ

/-- Complex-place congruence witnesses with a common coercivity and diagonal bound. -/
def NumberFieldComplexCongruenceBound (c C : ℝ)
    (N : Matrix (Fin n) (Fin n) (𝓞 K)) : Prop :=
  ∀ w : {w : InfinitePlace K // IsComplex w},
    ∃ A A' : Matrix (Fin n) (Fin n) ℂ,
      (∀ v : Fin n → ℂ,
        c * ∑ k, ‖v k‖ ^ 2 ≤ (star v ⬝ᵥ (A *ᵥ v)).re) ∧
      (∀ i, (A' i i).re ≤ C) ∧
      A' = numberFieldComplexOrderMatrixAt w N * A *
        (numberFieldComplexOrderMatrixAt w N)ᴴ

/-- Integral matrices carrying uniformly coercive forms to diagonally bounded forms at every
archimedean place form a finite set. -/
theorem finite_numberFieldIntegerMatrix_of_archimedean_congruenceBounds
    (n : ℕ) (c C : ℝ) (hc : 0 < c) :
    {N : Matrix (Fin n) (Fin n) (𝓞 K) |
      NumberFieldRealCongruenceBound c C N ∧
      NumberFieldComplexCongruenceBound c C N}.Finite := by
  refine (finite_numberFieldIntegerMatrix_of_archimedean_bound
    (K := K) n (Real.sqrt (C / c)) (Real.sqrt_nonneg _)).subset ?_
  intro N hN
  constructor
  · intro i j w
    obtain ⟨A, A', hlow, hdiag, hform⟩ := hN.1 w
    have hbound := real_congruence_entry_bound hc hlow hdiag hform i j
    simpa [numberFieldRealOrderMatrixAt] using hbound
  · intro i j w
    obtain ⟨A, A', hlow, hdiag, hform⟩ := hN.2 w
    have hbound := complex_congruence_entry_bound hc hlow hdiag hform i j
    simpa [numberFieldComplexOrderMatrixAt] using hbound

end GaloisForLFunctions.HTGeometry
