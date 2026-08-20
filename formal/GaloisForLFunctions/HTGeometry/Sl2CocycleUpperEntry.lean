import GaloisForLFunctions.HTGeometry.Sl2ElementaryFactorization

/-!
# Cocycles on the determinant-one matrices: the lower entry on the upper subgroup

A derivation-like cocycle `F(MN) = F(M)N + M F(N)` on the determinant-one two-by-two matrices
restricts to the upper elementary subgroup as a family whose lower-left entry is *additive*, and
conjugation by the diagonal torus scales that entry by the inverse square of the torus parameter.

Over an algebraically closed field of characteristic zero every element is a square, so the two
properties together force the lower-left entry to vanish identically on the upper elementary
subgroup — the first step of the vanishing of the rational first cohomology of `SL₂` with values in
the adjoint representation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C : Type*} [Field C]

/-- A **derivation-like cocycle** on the determinant-one matrices. -/
def IsSl2Derivation (F : Matrix (Fin 2) (Fin 2) C → Matrix (Fin 2) (Fin 2) C) : Prop :=
  ∀ M N : Matrix (Fin 2) (Fin 2) C, M.det = 1 → N.det = 1 →
    F (M * N) = F M * N + M * F N

variable {F : Matrix (Fin 2) (Fin 2) C → Matrix (Fin 2) (Fin 2) C}

theorem IsSl2Derivation.map_one (hF : IsSl2Derivation F) : F 1 = 0 := by
  have h := hF 1 1 Matrix.det_one Matrix.det_one
  rw [mul_one] at h
  rw [one_mul, mul_one] at h
  exact by linear_combination (norm := module) -h

@[simp] theorem sl2UPlus_apply_00 (x : C) : sl2UPlus x 0 0 = 1 := by simp [sl2UPlus]
@[simp] theorem sl2UPlus_apply_01 (x : C) : sl2UPlus x 0 1 = x := by simp [sl2UPlus]
@[simp] theorem sl2UPlus_apply_10 (x : C) : sl2UPlus x 1 0 = 0 := by simp [sl2UPlus]
@[simp] theorem sl2UPlus_apply_11 (x : C) : sl2UPlus x 1 1 = 1 := by simp [sl2UPlus]

@[simp] theorem sl2UMinus_apply_00 (y : C) : sl2UMinus y 0 0 = 1 := by simp [sl2UMinus]
@[simp] theorem sl2UMinus_apply_01 (y : C) : sl2UMinus y 0 1 = 0 := by simp [sl2UMinus]
@[simp] theorem sl2UMinus_apply_10 (y : C) : sl2UMinus y 1 0 = y := by simp [sl2UMinus]
@[simp] theorem sl2UMinus_apply_11 (y : C) : sl2UMinus y 1 1 = 1 := by simp [sl2UMinus]

/-- The diagonal torus element. -/
def sl2Torus (t : C) : Matrix (Fin 2) (Fin 2) C := !![t, 0; 0, t⁻¹]

@[simp] theorem sl2Torus_apply_00 (t : C) : sl2Torus t 0 0 = t := by simp [sl2Torus]
@[simp] theorem sl2Torus_apply_01 (t : C) : sl2Torus t 0 1 = 0 := by simp [sl2Torus]
@[simp] theorem sl2Torus_apply_10 (t : C) : sl2Torus t 1 0 = 0 := by simp [sl2Torus]
@[simp] theorem sl2Torus_apply_11 (t : C) : sl2Torus t 1 1 = t⁻¹ := by simp [sl2Torus]

theorem det_sl2Torus {t : C} (ht : t ≠ 0) : (sl2Torus t).det = 1 := by
  unfold sl2Torus
  rw [Matrix.det_fin_two_of]
  field_simp
  norm_num

theorem sl2Torus_mul_uPlus {t : C} (ht : t ≠ 0) (x : C) :
    sl2Torus t * sl2UPlus x = sl2UPlus (t * t * x) * sl2Torus t := by
  unfold sl2Torus sl2UPlus
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num
  field_simp

variable (hF : IsSl2Derivation F)
include hF

theorem uPlus_add (x y : C) :
    F (sl2UPlus (x + y))
      = F (sl2UPlus x) * sl2UPlus y + sl2UPlus x * F (sl2UPlus y) := by
  rw [← uPlus_mul_uPlus]
  exact hF _ _ (det_uPlus x) (det_uPlus y)

theorem uPlus_lower_add (x y : C) :
    F (sl2UPlus (x + y)) 1 0 = F (sl2UPlus x) 1 0 + F (sl2UPlus y) 1 0 := by
  have h := congrFun (congrFun (uPlus_add hF x y) 1) 0
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two] at h
  simp only [sl2UPlus_apply_00, sl2UPlus_apply_10, sl2UPlus_apply_11,
    mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add] at h
  exact h

theorem uPlus_lower_scale {t : C} (ht : t ≠ 0) (x : C) :
    F (sl2UPlus (t * t * x)) 1 0 = t⁻¹ * (t⁻¹ * F (sl2UPlus x) 1 0) := by
  have hcomm := sl2Torus_mul_uPlus ht x
  have hleft := hF (sl2Torus t) (sl2UPlus x) (det_sl2Torus ht) (det_uPlus x)
  have hright := hF (sl2UPlus (t * t * x)) (sl2Torus t) (det_uPlus _) (det_sl2Torus ht)
  rw [hcomm] at hleft
  rw [hleft] at hright
  have h := congrFun (congrFun hright 1) 0
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two] at h
  simp only [sl2UPlus_apply_00, sl2UPlus_apply_10, sl2UPlus_apply_11,
    sl2Torus_apply_00, sl2Torus_apply_10, sl2Torus_apply_11,
    mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add] at h
  field_simp at h ⊢
  linear_combination -h

/-- **The lower-left entry of the cocycle vanishes on the upper elementary subgroup.**  It is
additive, and conjugation by the torus scales it by the inverse square, which for an additive
function forces it to vanish. -/
theorem uPlus_lower_eq_zero [IsAlgClosed C] [CharZero C] (x : C) :
    F (sl2UPlus x) 1 0 = 0 := by
  have hzero : F (sl2UPlus (0 : C)) 1 0 = 0 := by
    rw [uPlus_zero, hF.map_one]
    rfl
  have hscale : ∀ z : C, z ≠ 0 → F (sl2UPlus z) 1 0 * z = F (sl2UPlus 1) 1 0 := by
    intro z hz
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (k := C) z (n := 2) (by norm_num)
    have htne : t ≠ 0 := by
      intro h0
      rw [h0] at ht
      simp at ht
      exact hz ht.symm
    have hsq : t * t = z := by
      rw [← ht]; ring
    have hs := uPlus_lower_scale hF htne 1
    rw [mul_one, hsq] at hs
    rw [hs, ← hsq]
    field_simp
  have h2 : F (sl2UPlus (1 + 1 : C)) 1 0 = F (sl2UPlus 1) 1 0 + F (sl2UPlus 1) 1 0 :=
    uPlus_lower_add hF 1 1
  have h2' : F (sl2UPlus (1 + 1 : C)) 1 0 * (1 + 1) = F (sl2UPlus 1) 1 0 := by
    refine hscale (1 + 1) ?_
    intro h0
    have : (2 : C) = 0 := by linear_combination h0
    exact two_ne_zero this
  have hc : F (sl2UPlus (1 : C)) 1 0 = 0 := by
    rw [h2] at h2'
    have h3 : F (sl2UPlus (1 : C)) 1 0 * 3 = 0 := by linear_combination h2'
    have h3' : (3 : C) ≠ 0 := three_ne_zero
    exact (mul_eq_zero.mp h3).resolve_right h3'
  by_cases hx : x = 0
  · rw [hx]; exact hzero
  · have := hscale x hx
    rw [hc] at this
    exact (mul_eq_zero.mp this).resolve_right hx

end

end GaloisForLFunctions.HTGeometry
