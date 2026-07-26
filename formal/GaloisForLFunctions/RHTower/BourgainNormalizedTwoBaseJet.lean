/-
# Uniform two-base nondegeneracy of Bourgain's normalized curve

This module computes the determinant of the literal first/half-second-jet
coordinate matrix at two base points.  For Bourgain's normalized phases the
apparent powers of the normalization parameter cancel exactly.  Consequently
the determinant has a fixed positive lower bound on two arcs separated by
at least `1/4`, uniformly for `0 < q ≤ 1/2`.
-/
import GaloisForLFunctions.RHTower.BourgainNormalizedTaylorJets

namespace RHTower

noncomputable section

/-- Algebraic determinant of the generic two-base phase-coordinate matrix. -/
theorem det_bourgainGenericPhaseCoordinateMatrix
    (φ₃ φ₄ : ℝ → ℝ) (a b : ℝ) :
    (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b).det =
      ((iteratedDeriv 1 φ₃ b - iteratedDeriv 1 φ₃ a) *
          (iteratedDeriv 2 φ₄ b - iteratedDeriv 2 φ₄ a) -
        (iteratedDeriv 1 φ₄ b - iteratedDeriv 1 φ₄ a) *
          (iteratedDeriv 2 φ₃ b - iteratedDeriv 2 φ₃ a)) / 2 -
      (b - a) * iteratedDeriv 2 φ₃ a *
        (iteratedDeriv 2 φ₄ b - iteratedDeriv 2 φ₄ a) / 2 +
      (b - a) * iteratedDeriv 2 φ₄ a *
        (iteratedDeriv 2 φ₃ b - iteratedDeriv 2 φ₃ a) / 2 := by
  have h21 : (2 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h12 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h31 : (3 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h32 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := by decide
  rw [Matrix.det_succ_row_zero]
  simp [bourgainGenericPhaseCoordinateMatrix, Matrix.det_fin_three,
    Fin.sum_univ_four, h21, h22, h12, h31, h32]
  ring

/-- Exact determinant before cancellation of the affine square-root
difference. -/
theorem det_bourgainGenericPhaseCoordinateMatrix_normalized
    {q a b : ℝ} (hq : q ≠ 0)
    (habase : 0 < 1 + q * a) (hbbase : 0 < 1 + q * b) :
    (bourgainGenericPhaseCoordinateMatrix
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q) a b).det =
      96 *
        ((1 + q * b) ^ (1 / 2 : ℝ) -
          (1 + q * a) ^ (1 / 2 : ℝ)) ^ (4 : ℕ) /
        (q ^ (4 : ℕ) *
          ((1 + q * a) ^ (1 / 2 : ℝ)) ^ (3 : ℕ) *
          ((1 + q * b) ^ (1 / 2 : ℝ)) ^ (3 : ℕ)) := by
  rw [det_bourgainGenericPhaseCoordinateMatrix]
  rw [iteratedDeriv_bourgainNormalizedCubicRemainder_one hq habase,
    iteratedDeriv_bourgainNormalizedCubicRemainder_one hq hbbase,
    iteratedDeriv_bourgainNormalizedCubicRemainder_two hq habase,
    iteratedDeriv_bourgainNormalizedCubicRemainder_two hq hbbase,
    iteratedDeriv_bourgainNormalizedQuarticRemainder_one hq habase,
    iteratedDeriv_bourgainNormalizedQuarticRemainder_one hq hbbase,
    iteratedDeriv_bourgainNormalizedQuarticRemainder_two hq habase,
    iteratedDeriv_bourgainNormalizedQuarticRemainder_two hq hbbase]
  let u : ℝ := (1 + q * a) ^ (1 / 2 : ℝ)
  let v : ℝ := (1 + q * b) ^ (1 / 2 : ℝ)
  have hu0 : 0 < u := Real.rpow_pos_of_pos habase _
  have hv0 : 0 < v := Real.rpow_pos_of_pos hbbase _
  have hu2 : u ^ (2 : ℕ) = 1 + q * a := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul habase.le]
    norm_num
  have hv2 : v ^ (2 : ℕ) = 1 + q * b := by
    dsimp [v]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbbase.le]
    norm_num
  have haeq : a = (u ^ (2 : ℕ) - 1) / q := by
    field_simp
    nlinarith
  have hbeq : b = (v ^ (2 : ℕ) - 1) / q := by
    field_simp
    nlinarith
  have haneghalf :
      (1 + q * a) ^ (-(1 / 2 : ℝ)) = u⁻¹ := by
    rw [Real.rpow_neg habase.le]
  have hbneghalf :
      (1 + q * b) ^ (-(1 / 2 : ℝ)) = v⁻¹ := by
    rw [Real.rpow_neg hbbase.le]
  have hanegthreehalf :
      (1 + q * a) ^ (-(3 / 2 : ℝ)) = u⁻¹ ^ (3 : ℕ) := by
    rw [show (-(3 / 2 : ℝ)) = -(1 / 2 : ℝ) * 3 by ring,
      Real.rpow_mul habase.le, Real.rpow_neg habase.le]
    simp only [u]
    exact Real.rpow_natCast _ 3
  have hbnegthreehalf :
      (1 + q * b) ^ (-(3 / 2 : ℝ)) = v⁻¹ ^ (3 : ℕ) := by
    rw [show (-(3 / 2 : ℝ)) = -(1 / 2 : ℝ) * 3 by ring,
      Real.rpow_mul hbbase.le, Real.rpow_neg hbbase.le]
    simp only [v]
    exact Real.rpow_natCast _ 3
  rw [show (1 + q * a) ^ (1 / 2 : ℝ) = u by rfl,
    show (1 + q * b) ^ (1 / 2 : ℝ) = v by rfl,
    haneghalf, hbneghalf, hanegthreehalf, hbnegthreehalf,
    haeq, hbeq]
  field_simp [hq, hu0.ne', hv0.ne']
  ring

/-- Cancellation form of the determinant.  This identity makes uniformity
as `q → 0` explicit. -/
theorem det_bourgainGenericPhaseCoordinateMatrix_normalized_cancelled
    {q a b : ℝ} (hq : q ≠ 0)
    (habase : 0 < 1 + q * a) (hbbase : 0 < 1 + q * b) :
    (bourgainGenericPhaseCoordinateMatrix
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q) a b).det =
      96 * (b - a) ^ (4 : ℕ) /
        ((((1 + q * a) ^ (1 / 2 : ℝ) +
              (1 + q * b) ^ (1 / 2 : ℝ)) ^ (4 : ℕ)) *
          ((1 + q * a) ^ (1 / 2 : ℝ)) ^ (3 : ℕ) *
          ((1 + q * b) ^ (1 / 2 : ℝ)) ^ (3 : ℕ)) := by
  rw [det_bourgainGenericPhaseCoordinateMatrix_normalized
    hq habase hbbase]
  let u : ℝ := (1 + q * a) ^ (1 / 2 : ℝ)
  let v : ℝ := (1 + q * b) ^ (1 / 2 : ℝ)
  have hu0 : 0 < u := Real.rpow_pos_of_pos habase _
  have hv0 : 0 < v := Real.rpow_pos_of_pos hbbase _
  have hu2 : u ^ (2 : ℕ) = 1 + q * a := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul habase.le]
    norm_num
  have hv2 : v ^ (2 : ℕ) = 1 + q * b := by
    dsimp [v]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbbase.le]
    norm_num
  have hprod : (v - u) * (u + v) = q * (b - a) := by
    nlinarith
  have hpow := congrArg (fun x : ℝ => x ^ (4 : ℕ)) hprod
  change ((v - u) * (u + v)) ^ (4 : ℕ) =
    (q * (b - a)) ^ (4 : ℕ) at hpow
  rw [mul_pow, mul_pow] at hpow
  change
    96 * (v - u) ^ (4 : ℕ) /
        (q ^ (4 : ℕ) * u ^ (3 : ℕ) * v ^ (3 : ℕ)) =
      96 * (b - a) ^ (4 : ℕ) /
        ((u + v) ^ (4 : ℕ) * u ^ (3 : ℕ) * v ^ (3 : ℕ))
  field_simp [hq, hu0.ne', hv0.ne',
    ne_of_gt (add_pos hu0 hv0)]
  nlinarith

/-- Uniform determinant lower bound for two normalized arcs separated by
at least `1/4`. -/
theorem det_bourgainGenericPhaseCoordinateMatrix_normalized_ge
    {q a b : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hab : 1 / 4 ≤ b - a) :
    (3 / 131072 : ℝ) ≤
      (bourgainGenericPhaseCoordinateMatrix
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q) a b).det := by
  have hqa0 : 0 ≤ q * a := mul_nonneg hq0.le ha.1
  have hqb0 : 0 ≤ q * b := mul_nonneg hq0.le hb.1
  have habase : 0 < 1 + q * a := by linarith
  have hbbase : 0 < 1 + q * b := by linarith
  rw [det_bourgainGenericPhaseCoordinateMatrix_normalized_cancelled
    hq0.ne' habase hbbase]
  let u : ℝ := (1 + q * a) ^ (1 / 2 : ℝ)
  let v : ℝ := (1 + q * b) ^ (1 / 2 : ℝ)
  have hu0 : 0 < u := Real.rpow_pos_of_pos habase _
  have hv0 : 0 < v := Real.rpow_pos_of_pos hbbase _
  have hu2 : u ^ (2 : ℕ) = 1 + q * a := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul habase.le]
    norm_num
  have hv2 : v ^ (2 : ℕ) = 1 + q * b := by
    dsimp [v]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbbase.le]
    norm_num
  have hqa1 : q * a ≤ 1 / 2 := by
    calc
      q * a ≤ q * 1 := mul_le_mul_of_nonneg_left ha.2 hq0.le
      _ ≤ 1 / 2 := by simpa using hq1
  have hqb1 : q * b ≤ 1 / 2 := by
    calc
      q * b ≤ q * 1 := mul_le_mul_of_nonneg_left hb.2 hq0.le
      _ ≤ 1 / 2 := by simpa using hq1
  have hu1 : 1 ≤ u := by nlinarith [sq_nonneg (u - 1)]
  have hv1 : 1 ≤ v := by nlinarith [sq_nonneg (v - 1)]
  have hu2' : u ≤ 2 := by nlinarith [sq_nonneg (u - 2)]
  have hv2' : v ≤ 2 := by nlinarith [sq_nonneg (v - 2)]
  have hsum4 : (u + v) ^ (4 : ℕ) ≤ 256 := by
    have hsum : u + v ≤ 4 := by linarith
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ u + v) hsum 4
    norm_num at hpow ⊢
    exact hpow
  have hu3 : u ^ (3 : ℕ) ≤ 8 := by
    have hpow := pow_le_pow_left₀ hu0.le hu2' 3
    norm_num at hpow ⊢
    exact hpow
  have hv3 : v ^ (3 : ℕ) ≤ 8 := by
    have hpow := pow_le_pow_left₀ hv0.le hv2' 3
    norm_num at hpow ⊢
    exact hpow
  have hden0 :
      0 < (u + v) ^ (4 : ℕ) * u ^ (3 : ℕ) * v ^ (3 : ℕ) := by
    positivity
  have hden :
      (u + v) ^ (4 : ℕ) * u ^ (3 : ℕ) * v ^ (3 : ℕ) ≤
        16384 := by
    have huv3 : u ^ (3 : ℕ) * v ^ (3 : ℕ) ≤ 64 := by
      calc
        u ^ (3 : ℕ) * v ^ (3 : ℕ) ≤
            8 * v ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_right hu3 (pow_nonneg hv0.le 3)
        _ ≤ 8 * 8 := mul_le_mul_of_nonneg_left hv3 (by norm_num)
        _ = 64 := by norm_num
    calc
      (u + v) ^ (4 : ℕ) * u ^ (3 : ℕ) * v ^ (3 : ℕ) =
          (u + v) ^ (4 : ℕ) *
            (u ^ (3 : ℕ) * v ^ (3 : ℕ)) := by ring
      _ ≤ 256 * 64 := mul_le_mul hsum4 huv3
        (mul_nonneg (pow_nonneg hu0.le 3) (pow_nonneg hv0.le 3))
        (by norm_num)
      _ = 16384 := by norm_num
  have hab4 : (1 / 256 : ℝ) ≤ (b - a) ^ (4 : ℕ) := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4)
      hab 4
    norm_num at hpow ⊢
    exact hpow
  change
    (3 / 131072 : ℝ) ≤
      96 * (b - a) ^ (4 : ℕ) /
        ((u + v) ^ (4 : ℕ) * u ^ (3 : ℕ) * v ^ (3 : ℕ))
  rw [le_div_iff₀ hden0]
  nlinarith

/-- Separated normalized two-base phase coordinates are unconditionally
invertible. -/
theorem isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
    {q a b : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hab : 1 / 4 ≤ b - a) :
    IsUnit
      (bourgainGenericPhaseCoordinateMatrix
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q) a b) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hdet :=
    det_bourgainGenericPhaseCoordinateMatrix_normalized_ge
      hq0 hq1 ha hb hab
  exact ne_of_gt (lt_of_lt_of_le (by norm_num) hdet)

end

end RHTower
