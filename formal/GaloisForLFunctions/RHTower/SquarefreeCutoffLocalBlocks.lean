import GaloisForLFunctions.HTGeometry.InertiaScalingSwap
import GaloisForLFunctions.HTGeometry.TensorFamilyInertia

/-!
# The local blocks of the squarefree cutoff jump

At a local scale `P = k + 2` the Boolean shear kernel has three normalized blocks on the
`P`-dimensional coordinate space: the rank-one **anchor** `A = e eᴴ`, the **density** block
`T = e eᴴ − w wᴴ` with `w = P⁻¹ u − e`, and the diagonal **occupancy** block

`Δ = 2P⁻¹ e eᴴ − P⁻² 1 = diagonal ((2P−1)/P², −P⁻², …, −P⁻²)`.

The anchor and the occupancy block are diagonal, so their inertia is a direct count; the density
block is `U J₀ Uᴴ` for the frame `U = [e, w]` and `J₀ = diag(1, −1)`.
-/

namespace RHTower

open Matrix GaloisForLFunctions.HTGeometry

noncomputable section

/-- The local scale `P = k + 2`. -/
def localScale (k : ℕ) : ℂ := (k : ℂ) + 2

theorem localScale_ne_zero (k : ℕ) : localScale k ≠ 0 := by
  rw [localScale]
  intro h
  have hre : ((k : ℂ) + 2).re = (k : ℝ) + 2 := by simp
  rw [h] at hre
  simp at hre
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

theorem two_localScale_sub_one_ne_zero (k : ℕ) : 2 * localScale k - 1 ≠ 0 := by
  rw [localScale]
  intro h
  have hre : (2 * ((k : ℂ) + 2) - 1).re = 2 * ((k : ℝ) + 2) - 1 := by simp
  rw [h] at hre
  simp at hre
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

/-- The local anchor block `A = e eᴴ`. -/
def localAnchorBlock (k : ℕ) : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ :=
  diagonal fun a => if a = 0 then 1 else 0

/-- The local occupancy block `Δ = 2P⁻¹ e eᴴ − P⁻² 1`. -/
def localOccupancyBlock (k : ℕ) : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ :=
  diagonal fun a =>
    if a = 0 then (2 * localScale k - 1) / localScale k ^ 2 else -(localScale k ^ 2)⁻¹

/-- The `P × 1` anchor column. -/
def localColumn (k : ℕ) : Matrix (Fin (k + 2)) (Fin 1) ℂ :=
  Matrix.of fun a _ => if a = 0 then 1 else 0

/-- The local frame `U = [e, w]` with `w = P⁻¹ u − e`. -/
def localFrame (k : ℕ) : Matrix (Fin (k + 2)) (Fin 2) ℂ :=
  Matrix.of fun a j =>
    if j = 0 then (if a = 0 then 1 else 0)
    else (localScale k)⁻¹ - (if a = 0 then 1 else 0)

/-- The binary signature `J₀ = diag(1, −1)`. -/
def binaryJ : Matrix (Fin 2) (Fin 2) ℂ := diagonal fun j => if j = 0 then 1 else -1

/-- The local density block `T = U J₀ Uᴴ`. -/
def localDensityBlock (k : ℕ) : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ :=
  localFrame k * binaryJ * (localFrame k)ᴴ

theorem localColumn_conjTranspose_mul (k : ℕ) :
    (localColumn k)ᴴ * localColumn k = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, localColumn, Matrix.of_apply,
    Matrix.one_apply_eq]
  rw [Finset.sum_eq_single (0 : Fin (k + 2))]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem localColumn_mul_conjTranspose (k : ℕ) :
    localColumn k * (localColumn k)ᴴ = localAnchorBlock k := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, localColumn, Matrix.of_apply,
    localAnchorBlock, Finset.univ_unique, Finset.sum_singleton]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [ha, hb, Matrix.diagonal_apply, eq_comm]

theorem isHermitian_localAnchorBlock (k : ℕ) : (localAnchorBlock k).IsHermitian := by
  rw [localAnchorBlock, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases ha : a = 0 <;> simp [ha]

theorem isHermitian_localOccupancyBlock (k : ℕ) : (localOccupancyBlock k).IsHermitian := by
  rw [localOccupancyBlock, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases ha : a = 0 <;> simp [ha, localScale]

theorem conj_localScale (k : ℕ) : (starRingEnd ℂ) (localScale k) = localScale k := by
  rw [localScale]
  simp [Complex.ext_iff]

theorem star_localFrame (k : ℕ) (a : Fin (k + 2)) (i : Fin 2) :
    star (localFrame k a i) = localFrame k a i := by
  rw [localFrame]
  by_cases hi : i = 0 <;> by_cases ha : a = 0 <;>
    simp [hi, ha, conj_localScale]

/-- The row of the frame at the origin. -/
def frameRowZero (k : ℕ) (i : Fin 2) : ℂ := if i = 0 then 1 else (localScale k)⁻¹ - 1

/-- The row of the frame away from the origin. -/
def frameRowOther (k : ℕ) (i : Fin 2) : ℂ := if i = 0 then 0 else (localScale k)⁻¹

theorem localFrame_apply (k : ℕ) (a : Fin (k + 2)) (i : Fin 2) :
    localFrame k a i = if a = 0 then frameRowZero k i else frameRowOther k i := by
  rw [localFrame, frameRowZero, frameRowOther]
  by_cases hi : i = 0 <;> by_cases ha : a = 0 <;> simp [hi, ha]

/-- The Gram of the frame against a diagonal weight. -/
theorem frameGram_eq (k : ℕ) (d : Fin (k + 2) → ℂ) (i j : Fin 2) :
    ((localFrame k)ᴴ * diagonal d * localFrame k) i j
      = frameRowZero k i * d 0 * frameRowZero k j
        + frameRowOther k i * (∑ a ∈ Finset.univ.erase (0 : Fin (k + 2)), d a)
            * frameRowOther k j := by
  classical
  have hleft : ∀ b : Fin (k + 2),
      ((localFrame k)ᴴ * diagonal d) i b = localFrame k b i * d b := by
    intro b
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [Matrix.diagonal_apply_eq, Matrix.conjTranspose_apply, star_localFrame]
    · intro c _ hc
      rw [Matrix.diagonal_apply_ne _ hc, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ b) h
  have hentry : ((localFrame k)ᴴ * diagonal d * localFrame k) i j
      = ∑ a, localFrame k a i * d a * localFrame k a j := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => by rw [hleft b]
  have h0 : localFrame k 0 i * d 0 * localFrame k 0 j
      = frameRowZero k i * d 0 * frameRowZero k j := by
    simp only [localFrame_apply, if_pos]
  have hrest : (∑ a ∈ Finset.univ.erase (0 : Fin (k + 2)),
        localFrame k a i * d a * localFrame k a j)
      = frameRowOther k i * (∑ a ∈ Finset.univ.erase (0 : Fin (k + 2)), d a)
          * frameRowOther k j := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
    simp only [localFrame_apply, if_neg ha0]
  rw [hentry, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (k + 2))), h0, hrest]

theorem sum_erase_const (k : ℕ) (c : ℂ) :
    (∑ _a ∈ Finset.univ.erase (0 : Fin (k + 2)), c) = ((k : ℂ) + 1) * c := by
  classical
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  simp only [nsmul_eq_mul]
  congr 1
  push_cast
  ring

/-- The diagonal of the inverse occupancy block. -/
def localOccupancyInvDiag (k : ℕ) : Fin (k + 2) → ℂ :=
  fun a => if a = 0 then localScale k ^ 2 / (2 * localScale k - 1) else -(localScale k ^ 2)

theorem localOccupancyBlock_mul_inv (k : ℕ) :
    localOccupancyBlock k * diagonal (localOccupancyInvDiag k) = 1 := by
  have hP := localScale_ne_zero k
  have hQ := two_localScale_sub_one_ne_zero k
  rw [localOccupancyBlock, Matrix.diagonal_mul_diagonal]
  rw [show (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) = diagonal (fun _ => (1 : ℂ)) by
    simp [Matrix.diagonal_one]]
  congr 1
  funext a
  simp only [localOccupancyInvDiag]
  by_cases ha : a = 0
  · rw [if_pos ha, if_pos ha]
    field_simp
  · rw [if_neg ha, if_neg ha]
    field_simp

theorem inv_localOccupancyBlock (k : ℕ) :
    (localOccupancyBlock k)⁻¹ = diagonal (localOccupancyInvDiag k) :=
  Matrix.inv_eq_right_inv (localOccupancyBlock_mul_inv k)

theorem isUnit_localOccupancyBlock (k : ℕ) : IsUnit (localOccupancyBlock k) :=
  ⟨⟨localOccupancyBlock k, diagonal (localOccupancyInvDiag k), localOccupancyBlock_mul_inv k,
    mul_eq_one_comm.mp (localOccupancyBlock_mul_inv k)⟩, rfl⟩

theorem sum_erase_localOccupancyInvDiag (k : ℕ) :
    (∑ a ∈ Finset.univ.erase (0 : Fin (k + 2)), localOccupancyInvDiag k a)
      = ((k : ℂ) + 1) * (-(localScale k ^ 2)) := by
  classical
  rw [← sum_erase_const k (-(localScale k ^ 2))]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [localOccupancyInvDiag, if_neg (Finset.ne_of_mem_erase ha)]

/-- The local Gram `G = Uᴴ Δ⁻¹ U`. -/
def localGram (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (localFrame k)ᴴ * (localOccupancyBlock k)⁻¹ * localFrame k

theorem localScale_sub_one (k : ℕ) : localScale k - 1 = (k : ℂ) + 1 := by
  rw [localScale]; ring

/-- **The explicit local Gram.** -/
theorem localGram_eq (k : ℕ) :
    localGram k = (2 * localScale k - 1)⁻¹ •
      !![localScale k ^ 2, -(localScale k * (localScale k - 1));
         -(localScale k * (localScale k - 1)), -(localScale k * (localScale k - 1))] := by
  have hP := localScale_ne_zero k
  have hQ := two_localScale_sub_one_ne_zero k
  have hk : ((k : ℂ) + 1) = localScale k - 1 := (localScale_sub_one k).symm
  have hQ' : -1 + localScale k * 2 ≠ 0 := by
    intro h
    exact hQ (by linear_combination h)
  have hDinv : (-1 + localScale k * 2) * (-1 + localScale k * 2)⁻¹ = 1 := mul_inv_cancel₀ hQ'
  ext i j
  rw [localGram, inv_localOccupancyBlock, frameGram_eq, sum_erase_localOccupancyInvDiag, hk,
    localOccupancyInvDiag]
  fin_cases i <;> fin_cases j <;>
    simp [frameRowZero, frameRowOther] <;> field_simp <;> ring_nf
  all_goals linear_combination (localScale k - 1) * hDinv

/-- The local scale as a positive real. -/
def realScale (k : ℕ) : ℝ := (k : ℝ) + 2

theorem realScale_pos (k : ℕ) : 0 < realScale k := by
  rw [realScale]
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

theorem localScale_eq (k : ℕ) : localScale k = ((realScale k : ℝ) : ℂ) := by
  rw [localScale, realScale]
  push_cast
  ring

theorem binaryJ_mul_self : binaryJ * binaryJ = 1 := by
  rw [binaryJ, Matrix.diagonal_mul_diagonal]
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) = diagonal (fun _ => (1 : ℂ)) by simp [Matrix.diagonal_one]]
  congr 1
  funext j
  by_cases hj : j = 0 <;> simp [hj]

theorem isUnit_binaryJ : IsUnit binaryJ :=
  ⟨⟨binaryJ, binaryJ, binaryJ_mul_self, binaryJ_mul_self⟩, rfl⟩

theorem isHermitian_binaryJ : binaryJ.IsHermitian := by
  rw [binaryJ, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  by_cases hj : j = 0 <;> simp [hj]

/-- The unscaled local Gram `G̃ = (2P−1) G`. -/
def localGramRaw (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![localScale k ^ 2, -(localScale k * (localScale k - 1));
     -(localScale k * (localScale k - 1)), -(localScale k * (localScale k - 1))]

theorem localGram_eq_smul (k : ℕ) :
    localGram k = (2 * localScale k - 1)⁻¹ • localGramRaw k := by
  rw [localGramRaw]
  exact localGram_eq k

/-- The unscaled local pencil `M̃ = J₀ G̃`. -/
def localPencilRaw (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ := binaryJ * localGramRaw k

theorem localPencilRaw_eq (k : ℕ) :
    localPencilRaw k =
      !![localScale k ^ 2, -(localScale k * (localScale k - 1));
         localScale k * (localScale k - 1), localScale k * (localScale k - 1)] := by
  rw [localPencilRaw, localGramRaw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryJ, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The rotation part of the unscaled pencil. -/
def localRotationRaw (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![localScale k / 2, -(localScale k * (localScale k - 1));
     localScale k * (localScale k - 1), -(localScale k / 2)]

/-- Half the trace of the unscaled pencil. -/
def localHalfTraceRaw (k : ℕ) : ℂ := localScale k * (2 * localScale k - 1) / 2

theorem localPencilRaw_eq_add (k : ℕ) :
    localPencilRaw k
      = localHalfTraceRaw k • (1 : Matrix (Fin 2) (Fin 2) ℂ) + localRotationRaw k := by
  rw [localPencilRaw_eq, localRotationRaw, localHalfTraceRaw]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> ring

/-- The squared rotation radius of the unscaled pencil. -/
def localOmegaSqRaw (k : ℕ) : ℝ :=
  realScale k ^ 2 * (realScale k - 1) ^ 2 - realScale k ^ 2 / 4

theorem localOmegaSqRaw_pos (k : ℕ) : 0 < localOmegaSqRaw k := by
  rw [localOmegaSqRaw, realScale]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [sq_nonneg ((k : ℝ) + 2)]

theorem localOmegaSqRaw_cast (k : ℕ) :
    ((localOmegaSqRaw k : ℝ) : ℂ)
      = localScale k ^ 2 * (localScale k - 1) ^ 2 - localScale k ^ 2 / 4 := by
  rw [localOmegaSqRaw, localScale_eq]
  push_cast
  ring

/-- `Ñ² = −ω̃²·1`. -/
theorem localRotationRaw_sq (k : ℕ) :
    localRotationRaw k * localRotationRaw k
      = -((localOmegaSqRaw k : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [localOmegaSqRaw_cast, localRotationRaw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

theorem conjTranspose_localRotationRaw (k : ℕ) :
    (localRotationRaw k)ᴴ =
      !![localScale k / 2, localScale k * (localScale k - 1);
         -(localScale k * (localScale k - 1)), -(localScale k / 2)] := by
  rw [localRotationRaw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, map_div₀, map_neg, map_mul, map_sub, conj_localScale]

theorem conjTranspose_localRotationRaw_sq (k : ℕ) :
    (localRotationRaw k)ᴴ * (localRotationRaw k)ᴴ
      = -((localOmegaSqRaw k : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [localOmegaSqRaw_cast, conjTranspose_localRotationRaw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

end

end RHTower
