import GaloisForLFunctions.HTGeometry.PauliHilbertSchmidtNorm

/-!
# Operator norm of a Pauli combination

Each Pauli word is unitary, so a Pauli combination has operator norm at most its coefficient sum.
Conversely the squared Hilbert–Schmidt size of a matrix is at most the Hilbert dimension times its
squared operator norm, and the Hilbert–Schmidt size of a Pauli combination is exactly the dimension
times its squared coefficient sum, so the operator norm is at least the Euclidean length of the
coefficient vector.
-/

open Matrix

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section OpNorm

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- One column of a matrix has Euclidean length at most the operator norm. -/
theorem sum_normSq_column_le_opNorm_sq (M : Matrix α α ℂ) (y : α) :
    (∑ x, ‖M x y‖ ^ (2 : ℕ)) ≤ ‖M‖ ^ (2 : ℕ) := by
  classical
  have hnn : (0 : ℝ) ≤ ∑ x, ‖M x y‖ ^ (2 : ℕ) := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hcol : M *ᵥ ((EuclideanSpace.single y (1 : ℂ) : EuclideanSpace ℂ α)).ofLp =
      fun x => M x y := by
    funext x
    simp [Matrix.mulVec, dotProduct, EuclideanSpace.single]
  have hone : ‖(EuclideanSpace.single y (1 : ℂ) : EuclideanSpace ℂ α)‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have hsum : (∑ i, ‖((EuclideanSpace.single y (1 : ℂ) : EuclideanSpace ℂ α)).ofLp i‖ ^ (2 : ℕ))
        = 1 := by
      rw [Finset.sum_eq_single y]
      · simp [EuclideanSpace.single]
      · intro b _ hb
        simp [EuclideanSpace.single, hb]
      · intro h
        exact absurd (Finset.mem_univ y) h
    rw [hsum, Real.sqrt_one]
  have hle := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single y (1 : ℂ))
  rw [hcol, hone, mul_one] at hle
  have hlhs : ‖((EuclideanSpace.equiv α ℂ).symm fun x => M x y)‖ =
      Real.sqrt (∑ x, ‖M x y‖ ^ (2 : ℕ)) := by
    rw [EuclideanSpace.norm_eq]
    rfl
  rw [hlhs] at hle
  calc (∑ x, ‖M x y‖ ^ (2 : ℕ)) = (Real.sqrt (∑ x, ‖M x y‖ ^ (2 : ℕ))) ^ (2 : ℕ) := (Real.sq_sqrt hnn).symm
    _ ≤ ‖M‖ ^ (2 : ℕ) := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2

/-- **The Hilbert–Schmidt size is at most the dimension times the operator norm.** -/
theorem frobSq_le_card_mul_opNorm_sq (M : Matrix α α ℂ) :
    frobSq M ≤ (Fintype.card α : ℝ) * ‖M‖ ^ (2 : ℕ) := by
  classical
  rw [frobSq, Finset.sum_comm]
  calc (∑ y, ∑ x, ‖M x y‖ ^ (2 : ℕ)) ≤ ∑ _y : α, ‖M‖ ^ (2 : ℕ) :=
        Finset.sum_le_sum fun y _ => sum_normSq_column_le_opNorm_sq M y
    _ = (Fintype.card α : ℝ) * ‖M‖ ^ (2 : ℕ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

end OpNorm

section Pauli

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem finitePauliMatrix_mem_unitary (P : σ → Option (Fin 3)) :
    finitePauliMatrix P ∈
      unitary (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) := by
  have hstar : star (finitePauliMatrix P) = finitePauliMatrix P := finitePauliMatrix_isHermitian P
  refine ⟨?_, ?_⟩ <;> rw [hstar] <;> exact finitePauliMatrix_mul_self P

/-- Every Pauli word has operator norm one. -/
theorem norm_finitePauliMatrix (P : σ → Option (Fin 3)) : ‖finitePauliMatrix P‖ = 1 :=
  CStarRing.norm_coe_unitary ⟨_, finitePauliMatrix_mem_unitary P⟩

/-- **Upper half of the sandwich.**  The operator norm of a Pauli combination is at most its
coefficient sum. -/
theorem opNorm_pauliCombination_le (J : (σ → Option (Fin 3)) → ℂ) :
    ‖∑ P, J P • finitePauliMatrix P‖ ≤ ∑ P, ‖J P‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun P _ => ?_)
  rw [norm_smul, norm_finitePauliMatrix, mul_one]

/-- **Lower half of the sandwich.**  The operator norm of a Pauli combination is at least the
Euclidean length of its coefficient vector. -/
theorem le_opNorm_pauliCombination (J : (σ → Option (Fin 3)) → ℂ) :
    Real.sqrt (∑ P, ‖J P‖ ^ (2 : ℕ)) ≤ ‖∑ P, J P • finitePauliMatrix P‖ := by
  classical
  have hcardnat : Fintype.card (FiniteQubitConfiguration σ) = 2 ^ Fintype.card σ := by
    simp
  have hcard : (Fintype.card (FiniteQubitConfiguration σ) : ℝ) = 2 ^ Fintype.card σ := by
    rw [hcardnat]
    push_cast
    ring
  have hpos : (0 : ℝ) < 2 ^ Fintype.card σ := by positivity
  have hle := frobSq_le_card_mul_opNorm_sq (∑ P, J P • finitePauliMatrix P)
  rw [frobSq_pauliCombination, hcard] at hle
  have hstep : (∑ P, ‖J P‖ ^ (2 : ℕ)) ≤ ‖∑ P, J P • finitePauliMatrix P‖ ^ (2 : ℕ) :=
    le_of_mul_le_mul_left hle hpos
  calc Real.sqrt (∑ P, ‖J P‖ ^ (2 : ℕ))
      ≤ Real.sqrt (‖∑ P, J P • finitePauliMatrix P‖ ^ (2 : ℕ)) := Real.sqrt_le_sqrt hstep
    _ = ‖∑ P, J P • finitePauliMatrix P‖ := Real.sqrt_sq (norm_nonneg _)

/-- **Cauchy–Schwarz form of the upper half.**  A Pauli combination supported on `S` labels has
operator norm at most `√|S|` times the Euclidean length of its coefficient vector. -/
theorem opNorm_pauliCombination_le_sqrt_card (S : Finset (σ → Option (Fin 3)))
    (J : (σ → Option (Fin 3)) → ℂ) (hJ : ∀ P ∉ S, J P = 0) :
    ‖∑ P, J P • finitePauliMatrix P‖ ≤
      Real.sqrt (S.card) * Real.sqrt (∑ P, ‖J P‖ ^ (2 : ℕ)) := by
  classical
  have hsupp : (∑ P, ‖J P‖) = ∑ P ∈ S, ‖J P‖ := by
    refine (Finset.sum_subset (Finset.subset_univ S) fun P _ hP => ?_).symm
    rw [hJ P hP, norm_zero]
  have hcs : (∑ P ∈ S, ‖J P‖ * 1) ^ (2 : ℕ) ≤ (∑ P ∈ S, ‖J P‖ ^ (2 : ℕ)) * ∑ _P ∈ S, (1 : ℝ) ^ (2 : ℕ) :=
    Finset.sum_mul_sq_le_sq_mul_sq S (fun P => ‖J P‖) (fun _ => 1)
  have hcard : (∑ _P ∈ S, (1 : ℝ) ^ (2 : ℕ)) = (S.card : ℝ) := by
    rw [Finset.sum_const]
    simp
  have hsub : (∑ P ∈ S, ‖J P‖ ^ (2 : ℕ)) ≤ ∑ P, ‖J P‖ ^ (2 : ℕ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun P _ _ => sq_nonneg _
  have hnn : (0 : ℝ) ≤ ∑ P ∈ S, ‖J P‖ := Finset.sum_nonneg fun P _ => norm_nonneg _
  rw [hcard] at hcs
  have hsq : (∑ P ∈ S, ‖J P‖) ^ (2 : ℕ) ≤ (S.card : ℝ) * ∑ P, ‖J P‖ ^ (2 : ℕ) := by
    calc (∑ P ∈ S, ‖J P‖) ^ (2 : ℕ) ≤ (∑ P ∈ S, ‖J P‖ ^ (2 : ℕ)) * (S.card : ℝ) := by simpa using hcs
      _ ≤ (∑ P, ‖J P‖ ^ (2 : ℕ)) * (S.card : ℝ) :=
          mul_le_mul_of_nonneg_right hsub (Nat.cast_nonneg _)
      _ = (S.card : ℝ) * ∑ P, ‖J P‖ ^ (2 : ℕ) := mul_comm _ _
  have hA : (∑ P ∈ S, ‖J P‖) ≤ Real.sqrt ((S.card : ℝ) * ∑ P, ‖J P‖ ^ (2 : ℕ)) := by
    calc (∑ P ∈ S, ‖J P‖) = Real.sqrt ((∑ P ∈ S, ‖J P‖) ^ (2 : ℕ)) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((S.card : ℝ) * ∑ P, ‖J P‖ ^ (2 : ℕ)) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (by positivity)] at hA
  exact le_trans (le_trans (opNorm_pauliCombination_le J) (le_of_eq hsupp)) hA

end Pauli

end GaloisForLFunctions.HTGeometry
