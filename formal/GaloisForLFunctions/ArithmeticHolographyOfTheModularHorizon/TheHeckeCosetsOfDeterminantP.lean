import Mathlib

/-!
# The Hecke cosets of determinant `p`

Let `p` be prime and `M` an integer `2 × 2` matrix with `det M = p`. Modulo `p` the matrix has rank one, so its
columns are proportional and so are its rows. This gives the two coset decompositions of
`M_p = {M ∈ M₂(ℤ) : det M = p}` behind the self-adjointness of the Hecke operator `T_p`:

* **left cosets** `M_p = ⊔_k SL₂(ℤ) α_k` with `α_∞ = (p 0; 0 1)`, `α_b = (1 b; 0 p)`: `k = ∞` iff the first column
  vanishes mod `p`, otherwise `k = b` with second column `≡ b ·` first column (`leftQuot_mul`, `leftIndex_mul`,
  `leftQuot_mul_A`);
* **right cosets** `M_p = ⊔_i α_i^* SL₂(ℤ)` with the adjugates `α_∞^* = (1 0; 0 p)`, `α_b^* = (p −b; 0 1)`: `i = ∞`
  iff the second row vanishes mod `p`, otherwise the first row is `≡ −b ·` the second (`Astar_mul_rightQuot`,
  `rightIndex_Astar_mul`, `rightQuot_Astar_mul`).

Matching the two gives a bijection `P¹(𝔽_p) × SL₂(ℤ) ≃ SL₂(ℤ) × P¹(𝔽_p)`, `(i, γ) ↦ (γ', k)` with
`α_i^* γ = γ' α_k` (`heckeEquiv`, `heckeEquiv_spec`), compatible with `γ ↦ −γ` (`heckeEquiv_neg`).
-/

open Matrix
open scoped MatrixGroups

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.HeckeCoset

variable (p : ℕ) [hp : Fact p.Prime]

/-- The Hecke representatives `α_∞ = (p 0; 0 1)`, `α_b = (1 b; 0 p)`. -/
def A : Option (ZMod p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(p : ℤ), 0; 0, 1]
  | some b => !![1, (b.val : ℤ); 0, (p : ℤ)]

/-- Their adjugates `α_∞^* = (1 0; 0 p)`, `α_b^* = (p −b; 0 1)`. -/
def Astar : Option (ZMod p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![1, 0; 0, (p : ℤ)]
  | some b => !![(p : ℤ), -(b.val : ℤ); 0, 1]

theorem det_A (k : Option (ZMod p)) : (A p k).det = p := by
  cases k <;> simp [A, det_fin_two_of]

theorem det_Astar (i : Option (ZMod p)) : (Astar p i).det = p := by
  cases i <;> simp [Astar, det_fin_two_of]

/-! ### Rank one modulo `p` -/

theorem dvd_iff_cast (x : ℤ) : (p : ℤ) ∣ x ↔ (x : ZMod p) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd x p).symm

/-- In a field, a rank-one `2 × 2` matrix with nonzero first column has second column `b ·` first. -/
theorem col_prop {F : Type*} [Field F] [DecidableEq F] {x00 x01 x10 x11 : F} (hdet : x00 * x11 - x01 * x10 = 0)
    (hne : ¬(x00 = 0 ∧ x10 = 0)) :
    x01 = (if x00 ≠ 0 then x01 / x00 else x11 / x10) * x00 ∧
      x11 = (if x00 ≠ 0 then x01 / x00 else x11 / x10) * x10 := by
  by_cases h0 : x00 = 0
  · have h1 : x10 ≠ 0 := fun h => hne ⟨h0, h⟩
    simp only [h0, ne_eq, not_true_eq_false, if_false, mul_zero]
    have : x01 * x10 = 0 := by rw [h0] at hdet; linear_combination -hdet
    refine ⟨(mul_eq_zero.1 this).resolve_right h1, ?_⟩
    field_simp
  · simp only [ne_eq, h0, not_false_eq_true, if_true]
    refine ⟨by field_simp, ?_⟩
    field_simp
    linear_combination hdet

theorem det_cast {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = p) :
    ((M 0 0 : ℤ) : ZMod p) * (M 1 1 : ZMod p) - (M 0 1 : ZMod p) * (M 1 0 : ZMod p) = 0 := by
  rw [det_fin_two] at hM
  have := congrArg (fun t : ℤ => (t : ZMod p)) hM
  push_cast at this
  rw [this, ZMod.natCast_self]

/-! ### Left cosets `SL₂(ℤ) α_k` -/

/-- The column class of `M` modulo `p`. -/
def leftIndex (M : Matrix (Fin 2) (Fin 2) ℤ) : Option (ZMod p) :=
  if ((M 0 0 : ZMod p) = 0 ∧ (M 1 0 : ZMod p) = 0) then none
  else some (if (M 0 0 : ZMod p) ≠ 0 then (M 0 1 : ZMod p) / (M 0 0) else (M 1 1 : ZMod p) / (M 1 0))

/-- The quotient `M α_k^{−1}`. -/
def leftQuot (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  match leftIndex p M with
  | none => !![M 0 0 / p, M 0 1; M 1 0 / p, M 1 1]
  | some b => !![M 0 0, (M 0 1 - b.val * M 0 0) / p; M 1 0, (M 1 1 - b.val * M 1 0) / p]

theorem leftIndex_none {M : Matrix (Fin 2) (Fin 2) ℤ} (h : leftIndex p M = none) :
    (p : ℤ) ∣ M 0 0 ∧ (p : ℤ) ∣ M 1 0 := by
  unfold leftIndex at h
  split_ifs at h with hc
  exact ⟨(dvd_iff_cast p _).2 hc.1, (dvd_iff_cast p _).2 hc.2⟩

theorem leftIndex_some {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = p) {b : ZMod p}
    (h : leftIndex p M = some b) :
    (p : ℤ) ∣ M 0 1 - b.val * M 0 0 ∧ (p : ℤ) ∣ M 1 1 - b.val * M 1 0 := by
  unfold leftIndex at h
  by_cases hc : ((M 0 0 : ZMod p) = 0 ∧ (M 1 0 : ZMod p) = 0)
  · rw [if_pos hc] at h; exact absurd h (by simp)
  rw [if_neg hc, Option.some_inj] at h
  obtain ⟨e1, e2⟩ := col_prop (det_cast p hM) hc
  rw [h] at e1 e2
  refine ⟨(dvd_iff_cast p _).2 ?_, (dvd_iff_cast p _).2 ?_⟩
  · push_cast; rw [ZMod.natCast_zmod_val]; linear_combination e1
  · push_cast; rw [ZMod.natCast_zmod_val]; linear_combination e2

theorem leftQuot_mul {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = p) :
    leftQuot p M * A p (leftIndex p M) = M := by
  rcases h : leftIndex p M with _ | b
  · obtain ⟨h1, h2⟩ := leftIndex_none p h
    rw [leftQuot, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, mul_apply, Fin.sum_univ_two, Int.ediv_mul_cancel h1,
      Int.ediv_mul_cancel h2]
  · obtain ⟨h1, h2⟩ := leftIndex_some p hM h
    rw [leftQuot, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, mul_apply, Fin.sum_univ_two, -ZMod.natCast_val]
    · rw [Int.ediv_mul_cancel h1]; ring
    · rw [Int.ediv_mul_cancel h2]; ring

theorem det_leftQuot {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = p) : (leftQuot p M).det = 1 := by
  have h := congrArg Matrix.det (leftQuot_mul p hM)
  rw [det_mul, det_A, hM] at h
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : ((leftQuot p M).det - 1) * p = 0 := by linear_combination h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hp0)

theorem not_dvd_col (γ : SL(2, ℤ)) : ¬((γ 0 0 : ZMod p) = 0 ∧ (γ 1 0 : ZMod p) = 0) := by
  rintro ⟨h0, h1⟩
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [det_fin_two] at hdet
  have := congrArg (fun t : ℤ => (t : ZMod p)) hdet
  push_cast at this
  rw [h0, h1] at this
  simp at this

theorem not_dvd_row (γ : SL(2, ℤ)) : ¬((γ 1 0 : ZMod p) = 0 ∧ (γ 1 1 : ZMod p) = 0) := by
  rintro ⟨h0, h1⟩
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [det_fin_two] at hdet
  have := congrArg (fun t : ℤ => (t : ZMod p)) hdet
  push_cast at this
  rw [h0, h1] at this
  simp at this

omit hp in
theorem mul_A_apply (γ : SL(2, ℤ)) (k : Option (ZMod p)) :
    ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A p k) = match k with
      | none => !![γ 0 0 * p, γ 0 1; γ 1 0 * p, γ 1 1]
      | some b => !![γ 0 0, γ 0 0 * b.val + γ 0 1 * p; γ 1 0, γ 1 0 * b.val + γ 1 1 * p] := by
  cases k <;> (ext i j; fin_cases i <;> fin_cases j <;> simp [A, mul_apply, Fin.sum_univ_two, -ZMod.natCast_val])

/-- **Uniqueness of the left coset.** -/
theorem leftIndex_mul (γ : SL(2, ℤ)) (k : Option (ZMod p)) :
    leftIndex p ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A p k) = k := by
  rw [mul_A_apply]
  rcases k with _ | b
  · simp [leftIndex]
  · have hne := not_dvd_col p γ
    simp only [leftIndex, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    rw [if_neg hne]
    congr 1
    push_cast
    rw [ZMod.natCast_self, mul_zero, add_zero, mul_zero, add_zero, ZMod.natCast_zmod_val]
    split_ifs with h0
    · field_simp
    · have h1 : (γ 1 0 : ZMod p) ≠ 0 := fun h => hne ⟨not_not.1 h0, h⟩
      field_simp

theorem leftQuot_mul_A (γ : SL(2, ℤ)) (k : Option (ZMod p)) :
    leftQuot p ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A p k) = γ := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [leftQuot, leftIndex_mul, mul_A_apply]
  rcases k with _ | b
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Int.mul_ediv_cancel _ hp0]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [-ZMod.natCast_val] <;>
      exact Int.ediv_eq_of_eq_mul_left hp0 (by ring)

/-! ### Right cosets `α_i^* SL₂(ℤ)` -/

/-- The row class of `M` modulo `p`. -/
def rightIndex (M : Matrix (Fin 2) (Fin 2) ℤ) : Option (ZMod p) :=
  if ((M 1 0 : ZMod p) = 0 ∧ (M 1 1 : ZMod p) = 0) then none
  else some (-(if (M 1 0 : ZMod p) ≠ 0 then (M 0 0 : ZMod p) / (M 1 0) else (M 0 1 : ZMod p) / (M 1 1)))

/-- The quotient `(α_i^*)^{−1} M`. -/
def rightQuot (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  match rightIndex p M with
  | none => !![M 0 0, M 0 1; M 1 0 / p, M 1 1 / p]
  | some b => !![(M 0 0 + b.val * M 1 0) / p, (M 0 1 + b.val * M 1 1) / p; M 1 0, M 1 1]

/-- In a field, a rank-one `2 × 2` matrix with nonzero second row has first row `c ·` second. -/
theorem row_prop {F : Type*} [Field F] [DecidableEq F] {x00 x01 x10 x11 : F} (hdet : x00 * x11 - x01 * x10 = 0)
    (hne : ¬(x10 = 0 ∧ x11 = 0)) :
    x00 = (if x10 ≠ 0 then x00 / x10 else x01 / x11) * x10 ∧
      x01 = (if x10 ≠ 0 then x00 / x10 else x01 / x11) * x11 := by
  by_cases h0 : x10 = 0
  · have h1 : x11 ≠ 0 := fun h => hne ⟨h0, h⟩
    simp only [h0, ne_eq, not_true_eq_false, if_false, mul_zero]
    have : x00 * x11 = 0 := by rw [h0] at hdet; linear_combination hdet
    refine ⟨(mul_eq_zero.1 this).resolve_right h1, ?_⟩
    field_simp
  · simp only [ne_eq, h0, not_false_eq_true, if_true]
    refine ⟨by field_simp, ?_⟩
    field_simp
    linear_combination -hdet

theorem rightIndex_none {M : Matrix (Fin 2) (Fin 2) ℤ} (h : rightIndex p M = none) :
    (p : ℤ) ∣ M 1 0 ∧ (p : ℤ) ∣ M 1 1 := by
  unfold rightIndex at h
  split_ifs at h with hc
  exact ⟨(dvd_iff_cast p _).2 hc.1, (dvd_iff_cast p _).2 hc.2⟩

theorem rightIndex_some {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = p) {b : ZMod p}
    (h : rightIndex p M = some b) :
    (p : ℤ) ∣ M 0 0 + b.val * M 1 0 ∧ (p : ℤ) ∣ M 0 1 + b.val * M 1 1 := by
  unfold rightIndex at h
  by_cases hc : ((M 1 0 : ZMod p) = 0 ∧ (M 1 1 : ZMod p) = 0)
  · rw [if_pos hc] at h; exact absurd h (by simp)
  rw [if_neg hc, Option.some_inj] at h
  obtain ⟨e1, e2⟩ := row_prop (det_cast p hM) hc
  generalize (if (M 1 0 : ZMod p) ≠ 0 then (M 0 0 : ZMod p) / (M 1 0) else (M 0 1 : ZMod p) / (M 1 1)) = c
    at h e1 e2
  refine ⟨(dvd_iff_cast p _).2 ?_, (dvd_iff_cast p _).2 ?_⟩
  · push_cast; rw [ZMod.natCast_zmod_val]; linear_combination e1 - ((M 1 0 : ℤ) : ZMod p) * h
  · push_cast; rw [ZMod.natCast_zmod_val]; linear_combination e2 - ((M 1 1 : ℤ) : ZMod p) * h

theorem Astar_mul_rightQuot {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = p) :
    Astar p (rightIndex p M) * rightQuot p M = M := by
  rcases h : rightIndex p M with _ | b
  · obtain ⟨h1, h2⟩ := rightIndex_none p h
    rw [rightQuot, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Astar, mul_apply, Fin.sum_univ_two, Int.mul_ediv_cancel' h1,
      Int.mul_ediv_cancel' h2]
  · obtain ⟨h1, h2⟩ := rightIndex_some p hM h
    rw [rightQuot, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Astar, mul_apply, Fin.sum_univ_two, -ZMod.natCast_val]
    · rw [Int.mul_ediv_cancel' h1]; ring
    · rw [Int.mul_ediv_cancel' h2]; ring

theorem det_rightQuot {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = p) : (rightQuot p M).det = 1 := by
  have h := congrArg Matrix.det (Astar_mul_rightQuot p hM)
  rw [det_mul, det_Astar, hM] at h
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : ((rightQuot p M).det - 1) * p = 0 := by linear_combination h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hp0)

omit hp in
theorem Astar_mul_apply (γ : SL(2, ℤ)) (i : Option (ZMod p)) :
    (Astar p i * (γ : Matrix (Fin 2) (Fin 2) ℤ)) = match i with
      | none => !![γ 0 0, γ 0 1; p * γ 1 0, p * γ 1 1]
      | some b => !![p * γ 0 0 - b.val * γ 1 0, p * γ 0 1 - b.val * γ 1 1; γ 1 0, γ 1 1] := by
  cases i <;> (ext i j; fin_cases i <;> fin_cases j <;> simp [Astar, mul_apply, Fin.sum_univ_two,
    -ZMod.natCast_val]) <;> ring

/-- **Uniqueness of the right coset.** -/
theorem rightIndex_Astar_mul (γ : SL(2, ℤ)) (i : Option (ZMod p)) :
    rightIndex p (Astar p i * (γ : Matrix (Fin 2) (Fin 2) ℤ)) = i := by
  rw [Astar_mul_apply]
  rcases i with _ | b
  · simp [rightIndex]
  · have hne := not_dvd_row p γ
    simp only [rightIndex, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    rw [if_neg hne]
    congr 1
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_sub, zero_mul, zero_sub, ZMod.natCast_zmod_val]
    split_ifs with h0
    · field_simp
    · have h1 : (γ 1 1 : ZMod p) ≠ 0 := fun h => hne ⟨not_not.1 h0, h⟩
      field_simp

theorem rightQuot_Astar_mul (γ : SL(2, ℤ)) (i : Option (ZMod p)) :
    rightQuot p (Astar p i * (γ : Matrix (Fin 2) (Fin 2) ℤ)) = γ := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [rightQuot, rightIndex_Astar_mul, Astar_mul_apply]
  rcases i with _ | b
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Int.mul_ediv_cancel_left _ hp0]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [-ZMod.natCast_val] <;>
      exact Int.ediv_eq_of_eq_mul_left hp0 (by ring)

/-! ### The Hecke bijection -/

theorem det_Astar_mul (i : Option (ZMod p)) (γ : SL(2, ℤ)) :
    (Astar p i * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det = p := by
  rw [det_mul, det_Astar, Matrix.SpecialLinearGroup.det_coe, mul_one]

theorem det_mul_A (γ : SL(2, ℤ)) (k : Option (ZMod p)) :
    ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A p k).det = p := by
  rw [det_mul, det_A, Matrix.SpecialLinearGroup.det_coe, one_mul]

/-- The `SL₂(ℤ)` factor of a left coset. -/
def leftSL (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = p) : SL(2, ℤ) := ⟨leftQuot p M, det_leftQuot p hM⟩

/-- The `SL₂(ℤ)` factor of a right coset. -/
def rightSL (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = p) : SL(2, ℤ) := ⟨rightQuot p M, det_rightQuot p hM⟩

/-- **The Hecke bijection** `(i, γ) ↦ (γ', k)` with `α_i^* γ = γ' α_k`. -/
def heckeEquiv : Option (ZMod p) × SL(2, ℤ) ≃ SL(2, ℤ) × Option (ZMod p) where
  toFun q := (leftSL p _ (det_Astar_mul p q.1 q.2), leftIndex p (Astar p q.1 * (q.2 : Matrix (Fin 2) (Fin 2) ℤ)))
  invFun q := (rightIndex p ((q.1 : Matrix (Fin 2) (Fin 2) ℤ) * A p q.2), rightSL p _ (det_mul_A p q.1 q.2))
  left_inv q := by
    obtain ⟨i, γ⟩ := q
    have h := leftQuot_mul p (det_Astar_mul p i γ)
    have e : ((leftSL p _ (det_Astar_mul p i γ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        A p (leftIndex p (Astar p i * (γ : Matrix (Fin 2) (Fin 2) ℤ))) =
        Astar p i * (γ : Matrix (Fin 2) (Fin 2) ℤ) := h
    simp only
    rw [Prod.mk.injEq]
    constructor
    · rw [e, rightIndex_Astar_mul]
    · apply Subtype.ext
      show rightQuot p _ = _
      rw [e, rightQuot_Astar_mul]
  right_inv q := by
    obtain ⟨γ, k⟩ := q
    have h := Astar_mul_rightQuot p (det_mul_A p γ k)
    have e : Astar p (rightIndex p ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A p k)) *
        ((rightSL p _ (det_mul_A p γ k) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        (γ : Matrix (Fin 2) (Fin 2) ℤ) * A p k := h
    simp only
    rw [Prod.mk.injEq]
    constructor
    · apply Subtype.ext
      show leftQuot p _ = _
      rw [e, leftQuot_mul_A]
    · rw [e, leftIndex_mul]

/-- `α_i^* γ = γ' α_k` for `(γ', k) = heckeEquiv (i, γ)`. -/
theorem heckeEquiv_spec (q : Option (ZMod p) × SL(2, ℤ)) :
    Astar p q.1 * (q.2 : Matrix (Fin 2) (Fin 2) ℤ) =
      ((heckeEquiv p q).1 : Matrix (Fin 2) (Fin 2) ℤ) * A p (heckeEquiv p q).2 :=
  (leftQuot_mul p (det_Astar_mul p q.1 q.2)).symm

/-- The bijection commutes with `γ ↦ −γ`. -/
theorem heckeEquiv_neg (i : Option (ZMod p)) (γ : SL(2, ℤ)) :
    heckeEquiv p (i, -γ) = (-(heckeEquiv p (i, γ)).1, (heckeEquiv p (i, γ)).2) := by
  have h := heckeEquiv_spec p (i, γ)
  have hneg : Astar p i * ((-γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((-(heckeEquiv p (i, γ)).1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * A p (heckeEquiv p (i, γ)).2 := by
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_neg, mul_neg, neg_mul, ← h]
  rw [Prod.mk.injEq]
  constructor
  · apply Subtype.ext
    show leftQuot p _ = _
    rw [hneg, leftQuot_mul_A]
  · show leftIndex p _ = _
    rw [hneg, leftIndex_mul]

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.HeckeCoset
