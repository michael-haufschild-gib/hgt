import GaloisForLFunctions.HTGeometry.InertiaScalingSwap
import GaloisForLFunctions.HTGeometry.TensorFamilyInertia
import GaloisForLFunctions.RHTower.SquarefreeShearKernelSignedTensor

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

theorem binaryJ_eq : binaryJ = !![1, 0; 0, -1] := by
  rw [binaryJ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

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
  rw [localPencilRaw, localGramRaw, binaryJ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

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
  fin_cases i <;> fin_cases j <;> simp <;> ring

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
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem conjTranspose_localRotationRaw (k : ℕ) :
    (localRotationRaw k)ᴴ =
      !![localScale k / 2, localScale k * (localScale k - 1);
         -(localScale k * (localScale k - 1)), -(localScale k / 2)] := by
  rw [localRotationRaw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, conj_localScale]

theorem conjTranspose_localRotationRaw_sq (k : ℕ) :
    (localRotationRaw k)ᴴ * (localRotationRaw k)ᴴ
      = -((localOmegaSqRaw k : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [localOmegaSqRaw_cast, conjTranspose_localRotationRaw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The local metric `P₀ = ω̃²·1 + ÑᴴÑ`. -/
def localMetric (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((localOmegaSqRaw k : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    + (localRotationRaw k)ᴴ * localRotationRaw k

theorem isPosDefOn_localMetric (k : ℕ) : IsPosDefOn (localMetric k) ⊤ :=
  isPosDefOn_top_smul_one_add_gram (localOmegaSqRaw_pos k) (localRotationRaw k)

theorem isHermitian_localMetric (k : ℕ) : (localMetric k).IsHermitian := by
  rw [localMetric, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one]
  congr 1
  simp [Complex.conj_ofReal]

theorem posIndex_localMetric (k : ℕ) : hermPosIndex (localMetric k) = 2 := by
  have hlow : 2 ≤ hermPosIndex (localMetric k) := by
    have h := finrank_le_posIndex (isPosDefOn_localMetric k)
    simpa using h
  have hhigh : hermPosIndex (localMetric k) ≤ 2 := by
    have h := posIndex_add_negIndex_add_nullIndex (isHermitian_localMetric k)
    simp only [Fintype.card_fin] at h
    omega
  omega

theorem localMetric_eq (k : ℕ) :
    localMetric k =
      !![2 * (localScale k * (localScale k - 1)) ^ 2, -(localScale k ^ 2 * (localScale k - 1));
         -(localScale k ^ 2 * (localScale k - 1)),
           2 * (localScale k * (localScale k - 1)) ^ 2] := by
  rw [localMetric, localOmegaSqRaw_cast, conjTranspose_localRotationRaw, localRotationRaw]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The multiplier of the local metric under the unscaled pencil. -/
def localMetricScalar (k : ℕ) : ℝ :=
  realScale k ^ 2 * (2 * realScale k - 1) * (realScale k - 1)

theorem localMetricScalar_cast (k : ℕ) :
    ((localMetricScalar k : ℝ) : ℂ)
      = localScale k ^ 2 * (2 * localScale k - 1) * (localScale k - 1) := by
  rw [localMetricScalar, localScale_eq]
  push_cast
  ring

theorem conjTranspose_localPencilRaw (k : ℕ) :
    (localPencilRaw k)ᴴ =
      !![localScale k ^ 2, localScale k * (localScale k - 1);
         -(localScale k * (localScale k - 1)), localScale k * (localScale k - 1)] := by
  rw [localPencilRaw_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, conj_localScale]

/-- **The unscaled pencil scales the local metric.** -/
theorem localPencilRaw_metric (k : ℕ) :
    (localPencilRaw k)ᴴ * localMetric k * localPencilRaw k
      = ((localMetricScalar k : ℝ) : ℂ) • localMetric k := by
  rw [localMetricScalar_cast, localMetric_eq, conjTranspose_localPencilRaw, localPencilRaw_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem two_realScale_sub_one_pos (k : ℕ) : 0 < 2 * realScale k - 1 := by
  rw [realScale]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

theorem two_realScale_sub_one_lt_metricScalar (k : ℕ) :
    2 * realScale k - 1 < realScale k ^ 2 * (realScale k - 1) := by
  rw [realScale]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [sq_nonneg ((k : ℝ) + 2), sq_nonneg ((k : ℝ) + 1)]

/-- The local balance matrix, which anti-congrues both `J₀` and the raw Gram. -/
def localBalance (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-1, 2 * (localScale k - 1); -(2 * (localScale k - 1)), 1]

/-- The positive factor produced by the balance congruence. -/
def localBalanceFactor (k : ℕ) : ℝ := 4 * (realScale k - 1) ^ 2 - 1

theorem localBalanceFactor_pos (k : ℕ) : 0 < localBalanceFactor k := by
  rw [localBalanceFactor, realScale]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

theorem localBalanceFactor_cast (k : ℕ) :
    ((localBalanceFactor k : ℝ) : ℂ) = 4 * (localScale k - 1) ^ 2 - 1 := by
  rw [localBalanceFactor, localScale_eq]
  push_cast
  ring

theorem isUnit_localBalance (k : ℕ) : IsUnit (localBalance k) := by
  rw [Matrix.isUnit_iff_isUnit_det, localBalance, Matrix.det_fin_two_of]
  have hne : (-1 : ℂ) * 1 - 2 * (localScale k - 1) * -(2 * (localScale k - 1))
      = ((localBalanceFactor k : ℝ) : ℂ) := by
    rw [localBalanceFactor_cast]
    ring
  rw [hne]
  refine (Ne.isUnit ?_)
  simpa using (ne_of_gt (localBalanceFactor_pos k))

theorem conjTranspose_localBalance (k : ℕ) :
    (localBalance k)ᴴ =
      !![-1, -(2 * (localScale k - 1)); 2 * (localScale k - 1), 1] := by
  rw [localBalance]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, conj_localScale]

/-- **The balance matrix anti-congrues the binary signature.** -/
theorem localBalance_binaryJ (k : ℕ) :
    (localBalance k)ᴴ * binaryJ * localBalance k
      = -((localBalanceFactor k : ℝ) : ℂ) • binaryJ := by
  rw [localBalanceFactor_cast, conjTranspose_localBalance, localBalance, binaryJ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- **The balance matrix anti-congrues the raw Gram.** -/
theorem localBalance_gramRaw (k : ℕ) :
    (localBalance k)ᴴ * localGramRaw k * localBalance k
      = -((localBalanceFactor k : ℝ) : ℂ) • localGramRaw k := by
  rw [localBalanceFactor_cast, conjTranspose_localBalance, localBalance, localGramRaw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem localDensityBlock_apply (k : ℕ) (a b : Fin (k + 2)) :
    localDensityBlock k a b
      = (localScale k)⁻¹ * (if a = 0 then 1 else 0)
        + (localScale k)⁻¹ * (if b = 0 then 1 else 0) - ((localScale k) ^ 2)⁻¹ := by
  have hP := localScale_ne_zero k
  rw [localDensityBlock, binaryJ_eq]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_localFrame, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero]
  rw [localFrame]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [ha, hb] <;> field_simp <;> ring

/-- The normalized density block is the arithmetic shear kernel of the parent card, divided by
the square of the local scale. -/
theorem localDensityBlock_eq_smul_shearKernel (k : ℕ) :
    localDensityBlock k
      = ((localScale k) ^ 2)⁻¹ • localShearKernel (localScale k) (0 : Fin (k + 2)) := by
  have hP := localScale_ne_zero k
  ext a b
  rw [localDensityBlock_apply, Matrix.smul_apply, smul_eq_mul, localShearKernel]
  field_simp

/-- The real eigenvalues of the local occupancy block. -/
def localOccupancyEigen (k : ℕ) (a : Fin (k + 2)) : ℝ :=
  if a = 0 then (2 * realScale k - 1) / realScale k ^ 2 else -((realScale k) ^ 2)⁻¹

theorem localOccupancyBlock_eq_diagonal (k : ℕ) :
    localOccupancyBlock k = diagonal fun a => ((localOccupancyEigen k a : ℝ) : ℂ) := by
  rw [localOccupancyBlock]
  congr 1
  funext a
  rw [localOccupancyEigen, localScale_eq]
  by_cases ha : a = 0 <;> simp [ha]

theorem localOccupancyEigen_pos_zero (k : ℕ) : 0 < localOccupancyEigen k (0 : Fin (k + 2)) := by
  rw [localOccupancyEigen, if_pos rfl, realScale]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : 0 < 2 * ((k : ℝ) + 2) - 1 := by linarith
  have h2 : 0 < ((k : ℝ) + 2) ^ 2 := by positivity
  positivity

theorem localOccupancyEigen_neg_of_ne (k : ℕ) {a : Fin (k + 2)} (ha : a ≠ 0) :
    localOccupancyEigen k a < 0 := by
  rw [localOccupancyEigen, if_neg ha, realScale]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h2 : 0 < ((k : ℝ) + 2) ^ 2 := by positivity
  simp only [neg_lt_zero, inv_pos]
  exact h2

theorem localOccupancyEigen_ne_zero (k : ℕ) (a : Fin (k + 2)) : localOccupancyEigen k a ≠ 0 := by
  by_cases ha : a = 0
  · subst ha
    exact (localOccupancyEigen_pos_zero k).ne'
  · exact (localOccupancyEigen_neg_of_ne k ha).ne

theorem card_pos_localOccupancyEigen (k : ℕ) :
    ({a : Fin (k + 2) | 0 < localOccupancyEigen k a} : Finset (Fin (k + 2))).card = 1 := by
  classical
  have hset : ({a : Fin (k + 2) | 0 < localOccupancyEigen k a} : Finset (Fin (k + 2)))
      = {(0 : Fin (k + 2))} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      by_contra ha
      exact absurd h (not_lt.mpr (localOccupancyEigen_neg_of_ne k ha).le)
    · rintro rfl
      exact localOccupancyEigen_pos_zero k
  rw [hset, Finset.card_singleton]

theorem card_neg_localOccupancyEigen (k : ℕ) :
    ({a : Fin (k + 2) | localOccupancyEigen k a < 0} : Finset (Fin (k + 2))).card = k + 1 := by
  classical
  have hset : ({a : Fin (k + 2) | localOccupancyEigen k a < 0} : Finset (Fin (k + 2)))
      = Finset.univ.erase (0 : Fin (k + 2)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · intro h ha
      subst ha
      exact absurd h (not_lt.mpr (localOccupancyEigen_pos_zero k).le)
    · intro ha
      exact localOccupancyEigen_neg_of_ne k ha
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

theorem isHermitian_localDensityBlock (k : ℕ) : (localDensityBlock k).IsHermitian := by
  rw [localDensityBlock, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, isHermitian_binaryJ.eq, Matrix.mul_assoc]

theorem trace_localOccupancyBlock (k : ℕ) :
    Matrix.trace (localOccupancyBlock k) = (localScale k)⁻¹ := by
  classical
  have hP := localScale_ne_zero k
  rw [localOccupancyBlock, Matrix.trace_diagonal,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (k + 2)))]
  have hrest : (∑ a ∈ Finset.univ.erase (0 : Fin (k + 2)),
      if a = 0 then (2 * localScale k - 1) / localScale k ^ 2 else -(localScale k ^ 2)⁻¹)
      = ((k : ℂ) + 1) * (-(localScale k ^ 2)⁻¹) := by
    rw [← sum_erase_const k (-(localScale k ^ 2)⁻¹)]
    exact Finset.sum_congr rfl fun a ha => if_neg (Finset.ne_of_mem_erase ha)
  have hk : ((k : ℂ) + 1) = localScale k - 1 := (localScale_sub_one k).symm
  have hPinv : localScale k * (localScale k)⁻¹ = 1 := mul_inv_cancel₀ hP
  rw [hrest, if_pos rfl, hk, div_eq_mul_inv, ← inv_pow]
  linear_combination (localScale k)⁻¹ * hPinv

theorem trace_localDensityBlock (k : ℕ) :
    Matrix.trace (localDensityBlock k) = (localScale k)⁻¹ := by
  classical
  have hP := localScale_ne_zero k
  rw [Matrix.trace]
  simp only [Matrix.diag, localDensityBlock_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (k + 2)))]
  have hrest : (∑ a ∈ Finset.univ.erase (0 : Fin (k + 2)),
      ((localScale k)⁻¹ * (if a = 0 then 1 else 0)
        + (localScale k)⁻¹ * (if a = 0 then 1 else 0) - ((localScale k) ^ 2)⁻¹))
      = ((k : ℂ) + 1) * (-((localScale k) ^ 2)⁻¹) := by
    rw [← sum_erase_const k (-((localScale k) ^ 2)⁻¹)]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [if_neg (Finset.ne_of_mem_erase ha)]
    ring
  have hk : ((k : ℂ) + 1) = localScale k - 1 := (localScale_sub_one k).symm
  have hPinv : localScale k * (localScale k)⁻¹ = 1 := mul_inv_cancel₀ hP
  rw [hrest, if_pos rfl, hk, ← inv_pow]
  linear_combination (-(localScale k)⁻¹) * hPinv

/-- `(CJ5)`: the density block annihilates the local root-avoidance space. -/
theorem localDensityBlock_mulVec_eq_zero (k : ℕ) (v : Fin (k + 2) → ℂ)
    (h0 : v 0 = 0) (hsum : ∑ a, v a = 0) : localDensityBlock k *ᵥ v = 0 := by
  funext a
  rw [Matrix.mulVec, dotProduct]
  simp only [localDensityBlock_apply, Pi.zero_apply]
  have hexpand : ∀ b : Fin (k + 2),
      ((localScale k)⁻¹ * (if a = 0 then 1 else 0)
          + (localScale k)⁻¹ * (if b = 0 then 1 else 0) - ((localScale k) ^ 2)⁻¹) * v b
        = ((localScale k)⁻¹ * (if a = 0 then 1 else 0) - ((localScale k) ^ 2)⁻¹) * v b
          + (localScale k)⁻¹ * ((if b = 0 then 1 else 0) * v b) := by
    intro b
    ring
  rw [Finset.sum_congr rfl fun b _ => hexpand b, Finset.sum_add_distrib, ← Finset.mul_sum,
    hsum, mul_zero, ← Finset.mul_sum]
  have hdelta : (∑ b : Fin (k + 2), (if b = 0 then (1 : ℂ) else 0) * v b) = v 0 := by
    rw [Finset.sum_eq_single (0 : Fin (k + 2))]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hdelta, h0, mul_zero, zero_add]

/-- `(CJ5)`: the occupancy block is the scalar `−P⁻²` on the local root-avoidance space. -/
theorem localOccupancyBlock_mulVec (k : ℕ) (v : Fin (k + 2) → ℂ) (h0 : v 0 = 0) :
    localOccupancyBlock k *ᵥ v = (-((localScale k) ^ 2)⁻¹) • v := by
  funext a
  rw [localOccupancyBlock, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl, h0, mul_zero, mul_zero]
  · rw [if_neg ha]

end

end RHTower
