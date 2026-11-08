import GaloisForLFunctions.SelbergClass.Primon.KestenSquareJacobi

/-!
# Finite character packets in the actual likelihood Hilbert space

Finite coefficient vectors embed isometrically through the even
characters. The unilateral shift pairs adjacent coefficients, while
the square-coordinate Jacobi form has one initial diagonal defect.
-/

open _root_.RHTower Matrix
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem inner_state_smul_left (a : ℝ) (f g : KestenLikelihoodHilbert) :
    inner ℝ (a • f) g = a * inner ℝ f g := by
  simpa only [conj_trivial] using (_root_.inner_smul_left (𝕜 := ℝ) f g a)

private theorem inner_state_smul_right (a : ℝ) (f g : KestenLikelihoodHilbert) :
    inner ℝ f (a • g) = a * inner ℝ f g :=
  _root_.inner_smul_right (𝕜 := ℝ) f g a

/-- A finite coefficient vector represented by actual even-character states. -/
def kestenCharacterPacket (n : ℕ) (c : Fin (n + 1) → ℝ) : KestenLikelihoodHilbert :=
  ∑ i, c i • kestenCharacterState i

theorem inner_kestenCharacterStates (n m : ℕ) :
    inner ℝ (kestenCharacterState n) (kestenCharacterState m) = if n = m then 1 else 0 := by
  rw [inner_kestenCharacterState]
  simp [kestenCharacterState, lp.single_apply, Pi.single_apply]

/-- The square-Jacobi diagonal is `1,2,2,...` in the actual character basis. -/
theorem inner_character_jacobi_self (n : ℕ) :
    inner ℝ (kestenCharacterState n) (kestenSquareJacobi (kestenCharacterState n)) =
      if n = 0 then 1 else 2 := by
  cases n with
  | zero =>
      rw [kestenSquareJacobi_vacuum, inner_add_right, inner_kestenCharacterStates,
        inner_kestenCharacterStates]
      norm_num
  | succ n =>
      rw [kestenSquareJacobi_character_succ, inner_add_right, inner_add_right,
        inner_state_smul_right, inner_kestenCharacterStates,
        inner_kestenCharacterStates, inner_kestenCharacterStates]
      simp

/-- Every adjacent character coupling of the square-Jacobi operator equals one. -/
theorem inner_character_jacobi_succ (n : ℕ) :
    inner ℝ (kestenCharacterState n) (kestenSquareJacobi (kestenCharacterState (n + 1))) = 1 := by
  rw [kestenSquareJacobi_character_succ, inner_add_right, inner_add_right,
    inner_state_smul_right, inner_kestenCharacterStates,
    inner_kestenCharacterStates, inner_kestenCharacterStates]
  simp

/-- Reading an included character recovers its coefficient exactly. -/
theorem inner_character_kestenCharacterPacket (n : ℕ) (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    inner ℝ (kestenCharacterState i) (kestenCharacterPacket n c) = c i := by
  simp only [kestenCharacterPacket, inner_sum, inner_state_smul_right,
    inner_kestenCharacterStates, ← Fin.ext_iff]
  simp

/-- All character coordinates beyond the finite packet vanish. -/
theorem inner_character_kestenCharacterPacket_outside (n : ℕ) (c : Fin (n + 1) → ℝ) (m : ℕ) :
    n < m → inner ℝ (kestenCharacterState m) (kestenCharacterPacket n c) = 0 := by
  intro hm
  rw [kestenCharacterPacket, inner_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [inner_state_smul_right, inner_kestenCharacterStates, if_neg (by omega), mul_zero]

/-- Packet inner products are ordinary finite coefficient inner products. -/
theorem inner_kestenCharacterPackets (n : ℕ) (c d : Fin (n + 1) → ℝ) :
    inner ℝ (kestenCharacterPacket n c) (kestenCharacterPacket n d) = ∑ i, c i * d i := by
  change inner ℝ (∑ i, c i • kestenCharacterState i) (kestenCharacterPacket n d) = _
  rw [sum_inner]
  simp only [inner_state_smul_left, inner_character_kestenCharacterPacket]

theorem norm_sq_kestenCharacterPacket (n : ℕ) (c : Fin (n + 1) → ℝ) :
    ‖kestenCharacterPacket n c‖ ^ 2 = ∑ i, c i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_kestenCharacterPackets]
  simp only [pow_two]

/-- Compressing an operator to characters preserves its form on every finite packet. -/
theorem kestenCharacterPacket_operator_form (n : ℕ) (T : KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert)
    (c d : Fin (n + 1) → ℝ) :
    c ⬝ᵥ ((fun i j : Fin (n + 1) => inner ℝ (kestenCharacterState i) (T (kestenCharacterState j))) *ᵥ d) =
      inner ℝ (kestenCharacterPacket n c) (T (kestenCharacterPacket n d)) := by
  change c ⬝ᵥ (_ *ᵥ d) = inner ℝ (∑ i, c i • kestenCharacterState i)
    (T (∑ j, d j • kestenCharacterState j))
  rw [sum_inner]
  simp only [dotProduct, Matrix.mulVec, map_sum, map_smul,
    inner_sum, inner_state_smul_left, inner_state_smul_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The shift form pairs exactly the adjacent coefficients of the packet. -/
theorem inner_kestenCharacterPacket_shift (n : ℕ) (c : Fin (n + 1) → ℝ) :
    inner ℝ (kestenCharacterPacket n c) (kestenShift (kestenCharacterPacket n c)) =
      ∑ i : Fin n, c i.castSucc * c i.succ := by
  rw [real_inner_comm (kestenShift (kestenCharacterPacket n c)) (kestenCharacterPacket n c)]
  change inner ℝ (kestenShift (∑ i, c i • kestenCharacterState i)) (kestenCharacterPacket n c) = _
  rw [map_sum, sum_inner, Fin.sum_univ_castSucc]
  simp only [map_smul, kestenShift_character, inner_state_smul_left, Fin.val_castSucc, Fin.val_last]
  rw [inner_character_kestenCharacterPacket_outside n c (n + 1) (by omega), mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  have h := inner_character_kestenCharacterPacket n c i.succ
  change inner ℝ (kestenCharacterState (i.val + 1)) (kestenCharacterPacket n c) = c i.succ at h
  rw [h]

/-- The square-Jacobi energy is the bulk tridiagonal form minus the initial coordinate square. -/
theorem inner_kestenCharacterPacket_jacobi (n : ℕ) (c : Fin (n + 1) → ℝ) :
    inner ℝ (kestenCharacterPacket n c) (kestenSquareJacobi (kestenCharacterPacket n c)) =
      2 * (∑ i, c i ^ 2) + 2 * (∑ i : Fin n, c i.castSucc * c i.succ) - c 0 ^ 2 := by
  have hc : hardyLikelihoodUnitary.symm (kestenCharacterPacket n c) 0 = c 0 := by
    rw [← inner_kestenCharacterState]
    exact inner_character_kestenCharacterPacket n c 0
  have hb : inner ℝ (kestenCharacterPacket n c) (kestenBackshift (kestenCharacterPacket n c)) =
      inner ℝ (kestenCharacterPacket n c) (kestenShift (kestenCharacterPacket n c)) := by
    change inner ℝ (kestenCharacterPacket n c)
      (kestenShift.toContinuousLinearMap.adjoint (kestenCharacterPacket n c)) = _
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
    rfl
  rw [kestenSquareJacobi_eq_shift, inner_sub_right, inner_add_right, inner_add_right,
    inner_state_smul_right, inner_state_smul_right, hb, inner_kestenCharacterPacket_shift,
    real_inner_self_eq_norm_sq, norm_sq_kestenCharacterPacket, hc,
    real_inner_comm (kestenCharacterState 0) (kestenCharacterPacket n c)]
  have hz := inner_character_kestenCharacterPacket n c 0
  change inner ℝ (kestenCharacterState 0) (kestenCharacterPacket n c) = c 0 at hz
  rw [hz]
  ring

end
end GaloisForLFunctions.SelbergClass.Primon
