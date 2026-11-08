import GaloisForLFunctions.SelbergClass.Primon.KestenFiniteGreen
import GaloisForLFunctions.SelbergClass.Primon.KestenCharacterPackets
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheGcdStratification

/-!
# The exact terminal self-energy of a finite prime Green section

The finite Green inverse differs from the compressed infinite pencil
`λ_p I-J` by exactly `-q` on the terminal diagonal. Thus eliminating the
infinite tail changes only one boundary coordinate, at every depth.
-/

open _root_.RHTower Matrix
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The precision energy in prime rather than reciprocal-prime coordinates. -/
theorem kestenFiniteGreen_inverse_prime_energy (p : Nat.Primes) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ ((kestenFiniteGreen p n)⁻¹ *ᵥ c) =
      ((p : ℝ) + 1) * c 0 ^ 2 +
        (p : ℝ) * ∑ i : Fin n, (c i.succ - c i.castSucc / (p : ℝ)) ^ 2 := by
  rw [kestenFiniteGreen_inverse_energy]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have he : (1 + primeReciprocal p) / primeReciprocal p = (p : ℝ) + 1 := by
    unfold primeReciprocal
    field_simp
  rw [he]
  simp only [primeReciprocal, inv_inv, div_eq_mul_inv, mul_comm]

/-- Expanding the inverse energy exposes both endpoint diagonal corrections. -/
theorem kestenFiniteGreen_inverse_expanded_energy (p : Nat.Primes) (n : ℕ)
    (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ ((kestenFiniteGreen p n)⁻¹ *ᵥ c) =
      ((primeReciprocal p)⁻¹ + primeReciprocal p) * (∑ i, c i ^ 2) -
        2 * (∑ i : Fin n, c i.castSucc * c i.succ) + c 0 ^ 2 -
          primeReciprocal p * c (Fin.last n) ^ 2 := by
  rw [kestenFiniteGreen_inverse_energy]
  have hsum : (∑ i : Fin n, (c i.succ - primeReciprocal p * c i.castSucc) ^ 2) =
      (∑ i : Fin n, c i.succ ^ 2) -
        2 * primeReciprocal p * (∑ i : Fin n, c i.castSucc * c i.succ) +
          primeReciprocal p ^ 2 * (∑ i : Fin n, c i.castSucc ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hzero : (∑ i : Fin n, c i.succ ^ 2) = (∑ i, c i ^ 2) - c 0 ^ 2 := by
    rw [Fin.sum_univ_succ]
    ring
  have hlast : (∑ i : Fin n, c i.castSucc ^ 2) = (∑ i, c i ^ 2) - c (Fin.last n) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    ring
  rw [hsum, hzero, hlast]
  field_simp [(primeReciprocal_pos p).ne']
  ring

/-- Eliminating the infinite tail subtracts exactly `q` times the terminal coefficient square. -/
theorem kestenFiniteGreen_inverse_boundary_energy (p : Nat.Primes) (n : ℕ)
    (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ ((kestenFiniteGreen p n)⁻¹ *ᵥ c) =
      inner ℝ (kestenCharacterPacket n c)
        (kestenGreenParameter p • kestenCharacterPacket n c -
          kestenSquareJacobi (kestenCharacterPacket n c)) -
            primeReciprocal p * c (Fin.last n) ^ 2 := by
  rw [inner_sub_right,
    _root_.inner_smul_right (𝕜 := ℝ) (kestenCharacterPacket n c)
      (kestenCharacterPacket n c) (kestenGreenParameter p),
    real_inner_self_eq_norm_sq, norm_sq_kestenCharacterPacket, inner_kestenCharacterPacket_jacobi,
    kestenFiniteGreen_inverse_expanded_energy]
  have hp : kestenGreenParameter p = (primeReciprocal p)⁻¹ + 2 + primeReciprocal p := by
    rw [kestenGreenParameter_eq]
    simp only [primeReciprocal, inv_inv]
  rw [hp]
  ring

/-- The finite matrix of the actual infinite source pencil `λ_p I-J`. -/
def kestenCompressedGreenPencil (p : Nat.Primes) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => inner ℝ (kestenCharacterState i)
    (kestenGreenParameter p • kestenCharacterState j - kestenSquareJacobi (kestenCharacterState j))

/-- The exact terminal self-energy contributed by the eliminated infinite tail. -/
def kestenTerminalSelfEnergy (p : Nat.Primes) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (Pi.single (Fin.last n) (primeReciprocal p))

theorem isSymm_kestenCompressedGreenPencil (p : Nat.Primes) (n : ℕ) :
    (kestenCompressedGreenPencil p n).IsSymm := by
  change (kestenCompressedGreenPencil p n).transpose = kestenCompressedGreenPencil p n
  ext i j
  change inner ℝ (kestenCharacterState j)
    (kestenGreenParameter p • kestenCharacterState i - kestenSquareJacobi (kestenCharacterState i)) =
      inner ℝ (kestenCharacterState i)
        (kestenGreenParameter p • kestenCharacterState j - kestenSquareJacobi (kestenCharacterState j))
  rw [inner_sub_right, inner_sub_right,
    _root_.inner_smul_right (𝕜 := ℝ) (kestenCharacterState j) (kestenCharacterState i) (kestenGreenParameter p),
    _root_.inner_smul_right (𝕜 := ℝ) (kestenCharacterState i) (kestenCharacterState j) (kestenGreenParameter p),
    real_inner_comm (kestenCharacterState i) (kestenCharacterState j),
    ← inner_kestenSquareJacobi,
    real_inner_comm (kestenCharacterState i) (kestenSquareJacobi (kestenCharacterState j))]

/-- Matrix compression and Hilbert-space restriction give the same source energy. -/
theorem kestenCompressedGreenPencil_energy (p : Nat.Primes) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ (kestenCompressedGreenPencil p n *ᵥ c) =
      inner ℝ (kestenCharacterPacket n c)
        (kestenGreenParameter p • kestenCharacterPacket n c -
          kestenSquareJacobi (kestenCharacterPacket n c)) := by
  exact kestenCharacterPacket_operator_form n
    (kestenGreenParameter p • ContinuousLinearMap.id ℝ KestenLikelihoodHilbert - kestenSquareJacobi) c c

/-- The terminal self-energy reads only the last coefficient square. -/
theorem kestenTerminalSelfEnergy_energy (p : Nat.Primes) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ (kestenTerminalSelfEnergy p n *ᵥ c) = primeReciprocal p * c (Fin.last n) ^ 2 := by
  simp [kestenTerminalSelfEnergy, dotProduct, Matrix.mulVec_diagonal, Pi.single_apply,
    mul_ite, ite_mul]
  ring

/-- The finite inverse is the compressed infinite source operator minus exactly one terminal diagonal term. -/
theorem kestenFiniteGreen_inverse_eq_compressed_sub_terminal (p : Nat.Primes) (n : ℕ) :
    (kestenFiniteGreen p n)⁻¹ = kestenCompressedGreenPencil p n - kestenTerminalSelfEnergy p n := by
  apply GaloisForLFunctions.HodgeTheoryWithoutVarieties.eq_of_qf_eq
    (isSymm_kestenFiniteGreen_inverse p n)
    ((isSymm_kestenCompressedGreenPencil p n).sub (Matrix.isSymm_diagonal _))
  intro c
  change c ⬝ᵥ ((kestenFiniteGreen p n)⁻¹ *ᵥ c) =
    c ⬝ᵥ ((kestenCompressedGreenPencil p n - kestenTerminalSelfEnergy p n) *ᵥ c)
  rw [Matrix.sub_mulVec, dotProduct_sub, kestenCompressedGreenPencil_energy,
    kestenTerminalSelfEnergy_energy]
  exact kestenFiniteGreen_inverse_boundary_energy p n c

/-- The finite precision diagonal has the initial Jacobi defect and the terminal tail correction. -/
theorem kestenFiniteGreen_inverse_diagonal (p : Nat.Primes) (n : ℕ) (i : Fin (n + 1)) :
    (kestenFiniteGreen p n)⁻¹ i i =
      kestenGreenParameter p - (if i = 0 then 1 else 2) -
        (if i = Fin.last n then primeReciprocal p else 0) := by
  rw [kestenFiniteGreen_inverse_eq_compressed_sub_terminal]
  change inner ℝ (kestenCharacterState i)
    (kestenGreenParameter p • kestenCharacterState i - kestenSquareJacobi (kestenCharacterState i)) -
      Matrix.diagonal (Pi.single (Fin.last n) (primeReciprocal p)) i i = _
  rw [inner_sub_right,
    _root_.inner_smul_right (𝕜 := ℝ) (kestenCharacterState i) (kestenCharacterState i) (kestenGreenParameter p),
    inner_kestenCharacterStates, inner_character_jacobi_self, Matrix.diagonal_apply_eq]
  have hz : i.val = 0 ↔ i = 0 := by
    constructor
    · exact fun h => Fin.ext h
    · intro h; simp [h]
  simp [Pi.single_apply, hz, eq_comm]

/-- Every adjacent finite precision entry is exactly `-1`, independent of prime and depth. -/
theorem kestenFiniteGreen_inverse_adjacent (p : Nat.Primes) (n : ℕ) (i : Fin n) :
    (kestenFiniteGreen p n)⁻¹ i.castSucc i.succ = -1 := by
  have hi : i.castSucc ≠ i.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  rw [kestenFiniteGreen_inverse_eq_compressed_sub_terminal]
  change inner ℝ (kestenCharacterState i.castSucc)
    (kestenGreenParameter p • kestenCharacterState i.succ - kestenSquareJacobi (kestenCharacterState i.succ)) -
      Matrix.diagonal (Pi.single (Fin.last n) (primeReciprocal p)) i.castSucc i.succ = -1
  rw [Matrix.diagonal_apply_ne _ hi, sub_zero, inner_sub_right,
    _root_.inner_smul_right (𝕜 := ℝ) (kestenCharacterState i.castSucc)
      (kestenCharacterState i.succ) (kestenGreenParameter p), inner_kestenCharacterStates]
  simp only [Fin.val_castSucc, Fin.val_succ, if_neg (show i.val ≠ i.val + 1 by omega),
    mul_zero, zero_sub, inner_character_jacobi_succ]

end
end GaloisForLFunctions.SelbergClass.Primon
