import GaloisForLFunctions.SelbergClass.Primon.KestenFiniteGreenBoundary

/-!
# Dirichlet truncation of the prime Green operator

Inverting the compressed source pencil imposes a terminal Dirichlet
boundary. Woodbury's identity compares this inverse with the exact
compressed Green operator: the difference is one positive rank-one
terminal response. Its scalar coefficient is explicit at every depth.
-/

open _root_.RHTower Matrix
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

theorem kestenCompressedGreenPencil_eq_inverse_add_terminal (p : Nat.Primes) (n : ℕ) :
    kestenCompressedGreenPencil p n = (kestenFiniteGreen p n)⁻¹ + kestenTerminalSelfEnergy p n :=
  (eq_sub_iff_add_eq.mp (kestenFiniteGreen_inverse_eq_compressed_sub_terminal p n)).symm

theorem posSemidef_kestenTerminalSelfEnergy (p : Nat.Primes) (n : ℕ) :
    (kestenTerminalSelfEnergy p n).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  by_cases hi : i = Fin.last n
  · simp [hi, (primeReciprocal_pos p).le]
  · simp [hi]

/-- The uncorrected finite source pencil is positive definite. -/
theorem posDef_kestenCompressedGreenPencil (p : Nat.Primes) (n : ℕ) :
    (kestenCompressedGreenPencil p n).PosDef := by
  rw [kestenCompressedGreenPencil_eq_inverse_add_terminal]
  exact (posDef_kestenFiniteGreen_inverse p n).add_posSemidef (posSemidef_kestenTerminalSelfEnergy p n)

/-- The Green matrix obtained by directly inverting the compressed infinite source pencil. -/
def kestenDirichletGreen (p : Nat.Primes) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (kestenCompressedGreenPencil p n)⁻¹

theorem posDef_kestenDirichletGreen (p : Nat.Primes) (n : ℕ) :
    (kestenDirichletGreen p n).PosDef :=
  (posDef_kestenCompressedGreenPencil p n).inv

theorem kestenCompressedGreenPencil_dirichletGreen (p : Nat.Primes) (n : ℕ) :
    kestenCompressedGreenPencil p n * kestenDirichletGreen p n = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (posDef_kestenCompressedGreenPencil p n).isUnit)

theorem kestenDirichletGreen_compressedPencil (p : Nat.Primes) (n : ℕ) :
    kestenDirichletGreen p n * kestenCompressedGreenPencil p n = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (posDef_kestenCompressedGreenPencil p n).isUnit)

/-- The response to a terminal character source, restricted to the finite section. -/
def kestenGreenTerminalResponse (p : Nat.Primes) (n : ℕ) : Fin (n + 1) → ℝ :=
  fun i => kestenGreenEntry p i n

/-- The positive scalar multiplying the rank-one truncation loss. -/
def kestenDirichletCorrection (p : Nat.Primes) (n : ℕ) : ℝ :=
  ((primeReciprocal p)⁻¹ + kestenGreenEntry p n n)⁻¹

theorem kestenDirichletCorrection_pos (p : Nat.Primes) (n : ℕ) :
    0 < kestenDirichletCorrection p n :=
  inv_pos.mpr (add_pos (inv_pos.mpr (primeReciprocal_pos p)) (kestenGreenEntry_pos p n n))

private def terminalChannel (n : ℕ) : Matrix (Fin (n + 1)) (Fin 1) ℝ :=
  fun i _ => if i = Fin.last n then 1 else 0

private def scalarMatrix (a : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => a

private theorem scalarMatrix_inv (a : ℝ) : (scalarMatrix a)⁻¹ = scalarMatrix a⁻¹ := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.inv_subsingleton, scalarMatrix]

private theorem terminal_factor (p : Nat.Primes) (n : ℕ) :
    terminalChannel n * scalarMatrix (primeReciprocal p) * (terminalChannel n).transpose =
      kestenTerminalSelfEnergy p n := by
  ext i j
  by_cases hi : i = Fin.last n <;> by_cases hj : j = Fin.last n
  · subst i; subst j
    simp [terminalChannel, scalarMatrix, Matrix.mul_apply, kestenTerminalSelfEnergy]
  · simp [terminalChannel, scalarMatrix, Matrix.mul_apply, kestenTerminalSelfEnergy,
      Matrix.diagonal, Pi.single_apply, hi, hj, eq_comm]
  · simp [terminalChannel, scalarMatrix, Matrix.mul_apply, kestenTerminalSelfEnergy,
      Matrix.diagonal, Pi.single_apply, hi, hj]
  · simp [terminalChannel, scalarMatrix, Matrix.mul_apply, kestenTerminalSelfEnergy,
      Matrix.diagonal, Pi.single_apply, hi, hj]

private theorem terminal_schur (p : Nat.Primes) (n : ℕ) :
    (scalarMatrix (primeReciprocal p))⁻¹ +
      (terminalChannel n).transpose * kestenFiniteGreen p n * terminalChannel n =
        scalarMatrix ((primeReciprocal p)⁻¹ + kestenGreenEntry p n n) := by
  rw [scalarMatrix_inv]
  ext i j
  simp [scalarMatrix, terminalChannel, Matrix.mul_apply, kestenFiniteGreen]

private theorem terminal_pullback (p : Nat.Primes) (n : ℕ) :
    kestenFiniteGreen p n * terminalChannel n *
      (scalarMatrix ((primeReciprocal p)⁻¹ + kestenGreenEntry p n n))⁻¹ *
        (terminalChannel n).transpose * kestenFiniteGreen p n =
      kestenDirichletCorrection p n •
        Matrix.vecMulVec (kestenGreenTerminalResponse p n) (kestenGreenTerminalResponse p n) := by
  rw [scalarMatrix_inv]
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, scalarMatrix, terminalChannel,
    kestenFiniteGreen, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    kestenGreenTerminalResponse, kestenDirichletCorrection]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.univ_unique, Finset.sum_singleton, Fin.val_last]
  rw [kestenGreenEntry_symm p n j]
  ring

/-- The exact finite Green section exceeds the Dirichlet inverse by one positive rank-one response. -/
theorem kestenDirichletGreen_rank_one (p : Nat.Primes) (n : ℕ) :
    kestenDirichletGreen p n = kestenFiniteGreen p n -
      kestenDirichletCorrection p n •
        Matrix.vecMulVec (kestenGreenTerminalResponse p n) (kestenGreenTerminalResponse p n) := by
  have hG : IsUnit (kestenFiniteGreen p n).det :=
    isUnit_iff_ne_zero.mpr (det_kestenFiniteGreen_pos p n).ne'
  have hGinv : IsUnit ((kestenFiniteGreen p n)⁻¹) := (posDef_kestenFiniteGreen_inverse p n).isUnit
  have hC : IsUnit (scalarMatrix (primeReciprocal p)) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_eq_elem_of_subsingleton _ 0]
    exact isUnit_iff_ne_zero.mpr (primeReciprocal_pos p).ne'
  have hS : IsUnit ((scalarMatrix (primeReciprocal p))⁻¹ +
      (terminalChannel n).transpose * ((kestenFiniteGreen p n)⁻¹)⁻¹ * terminalChannel n) := by
    rw [Matrix.nonsing_inv_nonsing_inv _ hG, terminal_schur]
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_eq_elem_of_subsingleton _ 0]
    exact isUnit_iff_ne_zero.mpr
      (add_pos (inv_pos.mpr (primeReciprocal_pos p)) (kestenGreenEntry_pos p n n)).ne'
  have h := Matrix.add_mul_mul_inv_eq_sub ((kestenFiniteGreen p n)⁻¹)
    (terminalChannel n) (scalarMatrix (primeReciprocal p)) (terminalChannel n).transpose hGinv hC hS
  rw [Matrix.nonsing_inv_nonsing_inv _ hG, terminal_factor, terminal_schur, terminal_pullback] at h
  rw [kestenDirichletGreen, kestenCompressedGreenPencil_eq_inverse_add_terminal]
  exact h

/-- The entrywise truncation error is a product of two terminal responses. -/
theorem kestenDirichletGreen_entry (p : Nat.Primes) (n : ℕ) (i j : Fin (n + 1)) :
    kestenDirichletGreen p n i j = kestenGreenEntry p i j -
      kestenDirichletCorrection p n * kestenGreenEntry p i n * kestenGreenEntry p j n := by
  rw [kestenDirichletGreen_rank_one]
  change kestenGreenEntry p i j - kestenDirichletCorrection p n *
    (kestenGreenEntry p i n * kestenGreenEntry p j n) = _
  ring

theorem kestenDirichletGreen_entry_symm (p : Nat.Primes) (n : ℕ) (i j : Fin (n + 1)) :
    kestenDirichletGreen p n i j = kestenDirichletGreen p n j i := by
  rw [kestenDirichletGreen_entry, kestenDirichletGreen_entry, kestenGreenEntry_symm p i j]
  ring

/-- Every Dirichlet entry strictly underestimates the corresponding infinite Green entry. -/
theorem kestenDirichletGreen_entry_lt (p : Nat.Primes) (n : ℕ) (i j : Fin (n + 1)) :
    kestenDirichletGreen p n i j < kestenGreenEntry p i j := by
  rw [kestenDirichletGreen_entry]
  exact sub_lt_self _ (mul_pos (mul_pos (kestenDirichletCorrection_pos p n)
    (kestenGreenEntry_pos p i n)) (kestenGreenEntry_pos p j n))

/-- The entire quadratic truncation loss is one squared terminal response. -/
theorem kestenDirichletGreen_energy (p : Nat.Primes) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ (kestenDirichletGreen p n *ᵥ c) = c ⬝ᵥ (kestenFiniteGreen p n *ᵥ c) -
      kestenDirichletCorrection p n * (∑ i, c i * kestenGreenEntry p i n) ^ 2 := by
  have hform : c ⬝ᵥ ((kestenDirichletCorrection p n •
      Matrix.vecMulVec (kestenGreenTerminalResponse p n) (kestenGreenTerminalResponse p n)) *ᵥ c) =
      kestenDirichletCorrection p n * (c ⬝ᵥ kestenGreenTerminalResponse p n) ^ 2 := by
    rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, IsCentralScalar.op_smul_eq_smul,
      dotProduct_smul, dotProduct_smul]
    have hc : kestenGreenTerminalResponse p n ⬝ᵥ c = c ⬝ᵥ kestenGreenTerminalResponse p n := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    rw [hc]
    simp only [smul_eq_mul]
    ring
  rw [kestenDirichletGreen_rank_one, Matrix.sub_mulVec, dotProduct_sub, hform]
  rfl

/-- Dirichlet truncation decreases every Green quadratic form. -/
theorem kestenDirichletGreen_energy_le (p : Nat.Primes) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ (kestenDirichletGreen p n *ᵥ c) ≤ c ⬝ᵥ (kestenFiniteGreen p n *ᵥ c) := by
  rw [kestenDirichletGreen_energy]
  exact sub_le_self _ (mul_nonneg (kestenDirichletCorrection_pos p n).le (sq_nonneg _))

end
end GaloisForLFunctions.SelbergClass.Primon
