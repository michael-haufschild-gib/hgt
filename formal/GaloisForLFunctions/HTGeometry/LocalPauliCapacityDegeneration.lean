import GaloisForLFunctions.HTGeometry.PencilCapacityCertificate

/-!
# Coercive frames with Hall do not control capacity

For `0 < ε ≤ 1` the two real symmetric matrices

`A₁ = !![ε,0,1; 0,0,0; 1,0,0]`,  `A₂ = !![0,0,0; 0,ε,1; 0,1,0]`

have invertible sum, so the tuple is rank nondecreasing, and their quadratic frame operator
`K = A₁² + A₂²` is squeezed between `½` and `4`.  Nevertheless the square capacity of
`X ↦ A₁XA₁ + A₂XA₂` lies between `ε²/2` and `2ε²`, so it degenerates as `ε → 0` while the frame
bounds stay fixed.

The lower bound is the pencil certificate at `c = (1,1)`, whose pencil `A₁ + A₂` has determinant
`-2ε`.  The upper bound is the explicit family `Xₜ = diag(t,t,t⁻²)`, at which the Kraus determinant
is exactly `2(ε² + t⁻³)`.
-/

open Finset Matrix
open scoped MatrixOrder ComplexOrder

namespace GaloisForLFunctions.HTGeometry

/-! ## Rank-one certificates for arrow matrices -/

/-- The `1 × n` matrix of a vector. -/
def rowVec {n : Type*} (v : n → ℂ) : Matrix (Fin 1) n ℂ := Matrix.of fun _ j => v j

/-- The outer product of a vector with itself. -/
def outerSelf {n : Type*} (v : n → ℂ) : Matrix n n ℂ := (rowVec v)ᴴ * rowVec v

theorem outerSelf_posSemidef {n : Type*} [Fintype n] (v : n → ℂ) : (outerSelf v).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

theorem outerSelf_apply {n : Type*} (v : n → ℂ) (i j : n) :
    outerSelf v i j = (starRingEnd ℂ) (v i) * v j := by
  simp [outerSelf, rowVec, Matrix.mul_apply]

/-- **A symmetric arrow matrix with dominated corner is positive semidefinite.**  Its rank-one
decomposition uses only the two arrow rows and the corner remainder, so no square root appears. -/
theorem posSemidef_arrow3 {a b c : ℝ} (ha : 0 < a) (hd : 0 ≤ c * a - 2 * b ^ 2) :
    (!![(a : ℂ), 0, (b : ℂ); 0, (a : ℂ), (b : ℂ); (b : ℂ), (b : ℂ), (c : ℂ)]).PosSemidef := by
  have hane : (a : ℝ) ≠ 0 := ne_of_gt ha
  set v₁ : Fin 3 → ℂ := ![(a : ℂ), 0, (b : ℂ)] with hv₁
  set v₂ : Fin 3 → ℂ := ![0, (a : ℂ), (b : ℂ)] with hv₂
  set v₃ : Fin 3 → ℂ := ![0, 0, 1] with hv₃
  have hdecomp : !![(a : ℂ), 0, (b : ℂ); 0, (a : ℂ), (b : ℂ); (b : ℂ), (b : ℂ), (c : ℂ)]
      = ((a⁻¹ : ℝ) : ℂ) • outerSelf v₁ + ((a⁻¹ : ℝ) : ℂ) • outerSelf v₂
        + (((c * a - 2 * b ^ 2) / a : ℝ) : ℂ) • outerSelf v₃ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [outerSelf_apply, hv₁, hv₂, hv₃, Complex.conj_ofReal] <;>
      (field_simp; ring)
  rw [hdecomp]
  refine Matrix.PosSemidef.add (Matrix.PosSemidef.add ?_ ?_) ?_
  · exact posSemidef_real_smul (outerSelf_posSemidef v₁) (by positivity)
  · exact posSemidef_real_smul (outerSelf_posSemidef v₂) (by positivity)
  · exact posSemidef_real_smul (outerSelf_posSemidef v₃) (by positivity)

/-! ## The seed pair -/

/-- The first seed matrix. -/
def hallSeedA₁ (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(ε : ℂ), 0, 1; 0, 0, 0; 1, 0, 0]

/-- The second seed matrix. -/
def hallSeedA₂ (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, (ε : ℂ), 1; 0, 1, 0]

theorem hallSeedA₁_conjTranspose (ε : ℝ) : (hallSeedA₁ ε)ᴴ = hallSeedA₁ ε := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hallSeedA₁, Matrix.conjTranspose_apply]

theorem hallSeedA₂_conjTranspose (ε : ℝ) : (hallSeedA₂ ε)ᴴ = hallSeedA₂ ε := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hallSeedA₂, Matrix.conjTranspose_apply]

/-- **The seed sum has determinant `-2ε`**, so the tuple is rank nondecreasing. -/
theorem hallSeedSum_det (ε : ℝ) : (hallSeedA₁ ε + hallSeedA₂ ε).det = -2 * (ε : ℂ) := by
  have hsum : hallSeedA₁ ε + hallSeedA₂ ε
      = !![(ε : ℂ), 0, 1; 0, (ε : ℂ), 1; 1, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hallSeedA₁, hallSeedA₂]
  rw [hsum, Matrix.det_fin_three]
  simp
  ring

/-! ## The frame operator -/

/-- The quadratic frame operator of the seed pair. -/
def hallSeedFrame (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  hallSeedA₁ ε * hallSeedA₁ ε + hallSeedA₂ ε * hallSeedA₂ ε

/-- The frame operator in closed form. -/
theorem hallSeedFrame_eq (ε : ℝ) :
    hallSeedFrame ε
      = !![1 + (ε : ℂ) ^ 2, 0, (ε : ℂ); 0, 1 + (ε : ℂ) ^ 2, (ε : ℂ); (ε : ℂ), (ε : ℂ), 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hallSeedFrame, hallSeedA₁, hallSeedA₂] <;> ring

/-- **The lower Casimir bound `½ ≤ K`.** -/
theorem hallSeedFrame_lower {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (hallSeedFrame ε - ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  have hshift : hallSeedFrame ε - ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)
      = !![((1 / 2 + ε ^ 2 : ℝ) : ℂ), 0, ((ε : ℝ) : ℂ);
           0, ((1 / 2 + ε ^ 2 : ℝ) : ℂ), ((ε : ℝ) : ℂ);
           ((ε : ℝ) : ℂ), ((ε : ℝ) : ℂ), ((3 / 2 : ℝ) : ℂ)] := by
    rw [hallSeedFrame_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> push_cast <;> ring
  rw [hshift]
  refine posSemidef_arrow3 (by positivity) ?_
  nlinarith [hε0, hε1, sq_nonneg ε, sq_nonneg (ε - 1)]

/-- **The upper Casimir bound `K ≤ 4`.** -/
theorem hallSeedFrame_upper {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (((4 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) - hallSeedFrame ε).PosSemidef := by
  have hshift : ((4 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) - hallSeedFrame ε
      = !![((3 - ε ^ 2 : ℝ) : ℂ), 0, ((-ε : ℝ) : ℂ);
           0, ((3 - ε ^ 2 : ℝ) : ℂ), ((-ε : ℝ) : ℂ);
           ((-ε : ℝ) : ℂ), ((-ε : ℝ) : ℂ), ((2 : ℝ) : ℂ)] := by
    rw [hallSeedFrame_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> push_cast <;> ring
  rw [hshift]
  refine posSemidef_arrow3 (by nlinarith [hε0, hε1]) ?_
  nlinarith [hε0, hε1, sq_nonneg ε]

/-! ## The capacity map -/

/-- The seed Kraus tuple. -/
def hallSeedTuple (ε : ℝ) : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ := ![hallSeedA₁ ε, hallSeedA₂ ε]

/-- The seed coefficient vector. -/
def hallSeedCoeff : Fin 2 → ℂ := ![1, 1]

theorem hallSeedTuple_pencil (ε : ℝ) :
    (∑ i, hallSeedCoeff i • hallSeedTuple ε i) = hallSeedA₁ ε + hallSeedA₂ ε := by
  simp [Fin.sum_univ_two, hallSeedCoeff, hallSeedTuple]

theorem hallSeedCoeff_normSq : (∑ i, ‖hallSeedCoeff i‖ ^ 2) = 2 := by
  simp [Fin.sum_univ_two, hallSeedCoeff]
  norm_num

theorem hallSeedKraus_eq (ε : ℝ) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    (∑ i, hallSeedTuple ε i * X * (hallSeedTuple ε i)ᴴ)
      = hallSeedA₁ ε * X * hallSeedA₁ ε + hallSeedA₂ ε * X * hallSeedA₂ ε := by
  rw [Fin.sum_univ_two]
  simp only [hallSeedTuple, Matrix.cons_val_zero, Matrix.cons_val_one,
    hallSeedA₁_conjTranspose, hallSeedA₂_conjTranspose]

/-- **The capacity lower bound `ε²/2 ≤ cap`.** -/
theorem hallSeedCapacity_lower {ε : ℝ} (hε0 : 0 < ε) {X : Matrix (Fin 3) (Fin 3) ℂ}
    (hX : X.PosDef) (hXdet : X.det = 1) :
    ((ε ^ 2 / 2 : ℝ) : ℂ)
      ≤ (hallSeedA₁ ε * X * hallSeedA₁ ε + hallSeedA₂ ε * X * hallSeedA₂ ε).det := by
  have hc : 0 < ∑ i, ‖hallSeedCoeff i‖ ^ 2 := by rw [hallSeedCoeff_normSq]; norm_num
  have hbound := pencil_capacity_bound hX hXdet hallSeedCoeff (hallSeedTuple ε) hc
  rw [hallSeedKraus_eq] at hbound
  rw [hallSeedTuple_pencil, hallSeedSum_det, hallSeedCoeff_normSq] at hbound
  have hnorm : ‖(-2 * (ε : ℂ))‖ ^ 2 = 4 * ε ^ 2 := by
    rw [norm_mul]
    simp [Complex.norm_real, abs_of_pos hε0]
    ring
  rw [hnorm] at hbound
  have hcard : Fintype.card (Fin 3) = 3 := by simp
  rw [hcard] at hbound
  have hval : (4 * ε ^ 2 / (2 : ℝ) ^ 3 : ℝ) = ε ^ 2 / 2 := by ring
  rwa [hval] at hbound

/-! ## The degenerating family -/

/-- The competitor states `diag(t, t, t⁻²)`. -/
noncomputable def hallSeedState (t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![((t : ℝ) : ℂ), 0, 0; 0, ((t : ℝ) : ℂ), 0; 0, 0, ((t⁻¹ ^ 2 : ℝ) : ℂ)]

theorem hallSeedState_eq_diagonal (t : ℝ) :
    hallSeedState t = Matrix.diagonal ![((t : ℝ) : ℂ), ((t : ℝ) : ℂ), ((t⁻¹ ^ 2 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hallSeedState, Matrix.diagonal_apply]

theorem hallSeedState_posDef {t : ℝ} (ht : 0 < t) : (hallSeedState t).PosDef := by
  rw [hallSeedState_eq_diagonal]
  refine Matrix.PosDef.diagonal fun i => ?_
  fin_cases i <;> (rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from by norm_num]) <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] <;>
    exact Complex.real_lt_real.mpr (by positivity)

theorem hallSeedState_det {t : ℝ} (ht : 0 < t) : (hallSeedState t).det = 1 := by
  have htne : (t : ℝ) ≠ 0 := ne_of_gt ht
  rw [hallSeedState, Matrix.det_fin_three]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_val']
  push_cast
  field_simp

/-- **The Kraus determinant along the family is exactly `2(ε² + t⁻³)`.** -/
theorem hallSeedKraus_det {ε t : ℝ} (ht : 0 < t) :
    (hallSeedA₁ ε * hallSeedState t * hallSeedA₁ ε
      + hallSeedA₂ ε * hallSeedState t * hallSeedA₂ ε).det
      = ((2 * (ε ^ 2 + t⁻¹ ^ 3) : ℝ) : ℂ) := by
  have htne : (t : ℝ) ≠ 0 := ne_of_gt ht
  have hmat : hallSeedA₁ ε * hallSeedState t * hallSeedA₁ ε
      + hallSeedA₂ ε * hallSeedState t * hallSeedA₂ ε
      = !![((ε ^ 2 * t + t⁻¹ ^ 2 : ℝ) : ℂ), 0, ((ε * t : ℝ) : ℂ);
           0, ((ε ^ 2 * t + t⁻¹ ^ 2 : ℝ) : ℂ), ((ε * t : ℝ) : ℂ);
           ((ε * t : ℝ) : ℂ), ((ε * t : ℝ) : ℂ), ((2 * t : ℝ) : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hallSeedA₁, hallSeedA₂, hallSeedState] <;> push_cast <;> ring
  rw [hmat, Matrix.det_fin_three]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_val']
  push_cast
  field_simp
  ring

/-- **The capacity upper bound `cap ≤ 2ε²`.**  Every neighbourhood of `2ε²` from above contains a
competitor value, so the infimum is at most `2ε²`. -/
theorem hallSeedCapacity_upper (ε : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ X : Matrix (Fin 3) (Fin 3) ℂ, X.PosDef ∧ X.det = 1 ∧
      ∃ s : ℝ, 0 < s ∧ s < δ ∧
        (hallSeedA₁ ε * X * hallSeedA₁ ε + hallSeedA₂ ε * X * hallSeedA₂ ε).det
          = ((2 * ε ^ 2 + s : ℝ) : ℂ) := by
  set t : ℝ := max 1 (3 / δ) with hT
  have ht1 : (1 : ℝ) ≤ t := le_max_left _ _
  have ht : 0 < t := lt_of_lt_of_le one_pos ht1
  have htδ : 3 / δ ≤ t := le_max_right _ _
  have hinv0 : 0 < t⁻¹ := by positivity
  have hinv1 : t⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr ht1
  have hinvδ : t⁻¹ ≤ δ / 3 := by
    have hd3 : (0 : ℝ) < 3 / δ := by positivity
    have h := one_div_le_one_div_of_le hd3 htδ
    rw [one_div, one_div] at h
    calc t⁻¹ ≤ (3 / δ)⁻¹ := h
      _ = δ / 3 := by field_simp
  refine ⟨hallSeedState t, hallSeedState_posDef ht, hallSeedState_det ht,
    2 * t⁻¹ ^ 3, by positivity, ?_, ?_⟩
  · have hcube : t⁻¹ ^ 3 ≤ t⁻¹ := by nlinarith [hinv0, hinv1]
    nlinarith [hcube, hinvδ, hδ]
  · rw [hallSeedKraus_det ht]
    push_cast
    ring

end GaloisForLFunctions.HTGeometry
