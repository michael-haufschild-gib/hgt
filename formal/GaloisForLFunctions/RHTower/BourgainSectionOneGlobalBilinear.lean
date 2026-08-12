/-
# Global Section-1 bilinear aggregation

This file closes the quantitative phase-space cover behind Bourgain
(1.23)--(1.26).  A physical sup-norm ball of radius `D²`, after the scaled
two-base jet map for an `H`-sample block, fits in an explicit anisotropic
period grid with only `O(D²)` cells.  The two linear phase coordinates cost
`O(D)` periods each; both quadratic coordinates cost only an absolute
number.  This is the exact geometric reason the cell Jacobian `D⁶` and the
cover cardinality `D²` recover four-dimensional volume `D⁸`.
-/
import GaloisForLFunctions.RHTower.BourgainSectionOneBlockPair
import GaloisForLFunctions.RHTower.BourgainNormalizedCoordinateDistortion
import GaloisForLFunctions.RHTower.BourgainAnisotropicCellGrid
import GaloisForLFunctions.RHTower.BourgainNormalizedBlockPartition

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Physical four-dimensional sup-norm ball at Section-1 radius `D²`. -/
def bourgainSectionOnePhaseBall (D : ℝ) : Set BourgainPhaseSpace :=
  {x | ‖x‖ ≤ D ^ (2 : ℕ)}

/-- Explicit period-grid multiplicities for a length-`H` block inside a
length-`4JH` sampled curve.  Only the two linear coordinates grow with the
ambient scale. -/
def bourgainSectionOneGridMultiplicity
    (J H : ℕ) : Fin 4 → ℕ :=
  ![320 * J * H, 80, 320 * J * H, 80]

theorem abs_bourgainPhaseSpace_apply_le_norm
    (x : BourgainPhaseSpace) (j : Fin 4) :
    |x j| ≤ ‖x‖ := by
  rw [Pi.norm_def]
  have h := Finset.le_sup
    (f := fun k : Fin 4 => ‖x k‖₊) (Finset.mem_univ j)
  exact_mod_cast h

/-- Finite planar-refinement Hölder cost for one length-`H` block. -/
theorem sum_norm_sq_pow_three_le_card_sq_sum_norm_pow_six
    (H : ℕ) (c : Fin H → ℂ) :
    (∑ n : Fin H, ‖c n‖ ^ (2 : ℕ)) ^ (3 : ℕ) ≤
      (H : ℝ) ^ (2 : ℕ) *
        ∑ n : Fin H, ‖c n‖ ^ (6 : ℕ) := by
  let mass : Fin H → ℝ := fun n => ‖c n‖ ^ (2 : ℕ)
  have hmass (n : Fin H) : 0 ≤ mass n := by
    dsimp [mass]
    positivity
  have hpower :=
    pow_sum_le_card_mul_sum_pow
      (s := (Finset.univ : Finset (Fin H)))
      (f := mass) (fun n hn => hmass n) 2
  calc
    (∑ n : Fin H, ‖c n‖ ^ (2 : ℕ)) ^ (3 : ℕ) ≤
        (H : ℝ) ^ (2 : ℕ) *
          ∑ n : Fin H, (‖c n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
      simpa [mass] using hpower
    _ = (H : ℝ) ^ (2 : ℕ) *
        ∑ n : Fin H, ‖c n‖ ^ (6 : ℕ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- Sixth-power coefficient mass partitions exactly over consecutive
`J × H` blocks. -/
theorem sum_sum_norm_pow_six_bourgainGenericCurveBlockCoefficients
    (J H : ℕ) (c : Fin (J * H) → ℂ) :
    (∑ i : Fin J,
      ∑ n : Fin H,
        ‖bourgainGenericCurveBlockCoefficients J H c i n‖ ^
          (6 : ℕ)) =
      ∑ n : Fin (J * H), ‖c n‖ ^ (6 : ℕ) := by
  rw [← (finProdFinEquiv : Fin J × Fin H ≃ Fin (J * H)).sum_comp]
  rw [Fintype.sum_prod_type]
  rfl

/-- Summing cubic `ℓ²` masses over all coarse blocks costs exactly `H²`,
independent of block count `J`. -/
theorem sum_blockMassCube_le_card_sq_sum_norm_pow_six
    (J H : ℕ) (c : Fin (J * H) → ℂ) :
    (∑ i : Fin J,
      (∑ n : Fin H,
        ‖bourgainGenericCurveBlockCoefficients J H c i n‖ ^
          (2 : ℕ)) ^ (3 : ℕ)) ≤
      (H : ℝ) ^ (2 : ℕ) *
        ∑ n : Fin (J * H), ‖c n‖ ^ (6 : ℕ) := by
  calc
    (∑ i : Fin J,
      (∑ n : Fin H,
        ‖bourgainGenericCurveBlockCoefficients J H c i n‖ ^
          (2 : ℕ)) ^ (3 : ℕ)) ≤
        ∑ i : Fin J,
          (H : ℝ) ^ (2 : ℕ) *
            ∑ n : Fin H,
              ‖bourgainGenericCurveBlockCoefficients J H c i n‖ ^
                (6 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact sum_norm_sq_pow_three_le_card_sq_sum_norm_pow_six
        H (bourgainGenericCurveBlockCoefficients J H c i)
    _ = (H : ℝ) ^ (2 : ℕ) *
        ∑ i : Fin J,
          ∑ n : Fin H,
            ‖bourgainGenericCurveBlockCoefficients J H c i n‖ ^
              (6 : ℕ) := by rw [Finset.mul_sum]
    _ = (H : ℝ) ^ (2 : ℕ) *
        ∑ n : Fin (J * H), ‖c n‖ ^ (6 : ℕ) := by
      rw [sum_sum_norm_pow_six_bourgainGenericCurveBlockCoefficients]

/-- **Exact two-arc planar refinement exponent.**

The product of block cubic masses costs `H⁴`, precisely the
`(N/K)^(d/2)` factor in Bourgain (1.25) for `d=4`. -/
theorem mul_sum_blockMassCube_le_card_four_sum_norm_pow_six
    (J H : ℕ) (c₁ c₂ : Fin (J * H) → ℂ) :
    (∑ i : Fin J,
      (∑ n : Fin H,
        ‖bourgainGenericCurveBlockCoefficients J H c₁ i n‖ ^
          (2 : ℕ)) ^ (3 : ℕ)) *
      (∑ i : Fin J,
        (∑ n : Fin H,
          ‖bourgainGenericCurveBlockCoefficients J H c₂ i n‖ ^
            (2 : ℕ)) ^ (3 : ℕ)) ≤
      (H : ℝ) ^ (4 : ℕ) *
        (∑ n : Fin (J * H), ‖c₁ n‖ ^ (6 : ℕ)) *
        (∑ n : Fin (J * H), ‖c₂ n‖ ^ (6 : ℕ)) := by
  have h₁ := sum_blockMassCube_le_card_sq_sum_norm_pow_six J H c₁
  have h₂ := sum_blockMassCube_le_card_sq_sum_norm_pow_six J H c₂
  have hleft0 :
      0 ≤ ∑ i : Fin J,
        (∑ n : Fin H,
          ‖bourgainGenericCurveBlockCoefficients J H c₁ i n‖ ^
            (2 : ℕ)) ^ (3 : ℕ) := by positivity
  have hright0 :
      0 ≤ ∑ i : Fin J,
        (∑ n : Fin H,
          ‖bourgainGenericCurveBlockCoefficients J H c₂ i n‖ ^
            (2 : ℕ)) ^ (3 : ℕ) := by positivity
  calc
    (∑ i : Fin J,
      (∑ n : Fin H,
        ‖bourgainGenericCurveBlockCoefficients J H c₁ i n‖ ^
          (2 : ℕ)) ^ (3 : ℕ)) *
      (∑ i : Fin J,
        (∑ n : Fin H,
          ‖bourgainGenericCurveBlockCoefficients J H c₂ i n‖ ^
            (2 : ℕ)) ^ (3 : ℕ)) ≤
        ((H : ℝ) ^ (2 : ℕ) *
          ∑ n : Fin (J * H), ‖c₁ n‖ ^ (6 : ℕ)) *
        ((H : ℝ) ^ (2 : ℕ) *
          ∑ n : Fin (J * H), ‖c₂ n‖ ^ (6 : ℕ)) := by
      exact mul_le_mul h₁ h₂ hright0
        (by positivity)
    _ = _ := by ring

/-- The normalized two-base jet matrix has forward sup-norm at most `40`.
This complements the inverse bound already used for Taylor perturbations. -/
theorem abs_bourgainNormalizedPhaseCoordinates_apply_le_forty
    {q a b : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 2)
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (x : BourgainPhaseSpace) (i : Fin 4) :
    |bourgainGenericPhaseCoordinates
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q) a b x i| ≤
      40 * ‖x‖ := by
  let A :=
    bourgainGenericPhaseCoordinateMatrix
      (bourgainNormalizedCubicRemainder q)
      (bourgainNormalizedQuarticRemainder q) a b
  have hentry (j : Fin 4) : |A i j| ≤ 10 :=
    abs_bourgainNormalizedPhaseCoordinateMatrix_apply_le_ten
      hq hq1 ha hb i j
  have hx (j : Fin 4) : |x j| ≤ ‖x‖ :=
    abs_bourgainPhaseSpace_apply_le_norm x j
  change |∑ j : Fin 4, A i j * x j| ≤ 40 * ‖x‖
  rw [← Real.norm_eq_abs]
  calc
    ‖∑ j : Fin 4, A i j * x j‖ ≤
        ∑ j : Fin 4, ‖A i j * x j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin 4, 10 * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hentry j) (hx j) (abs_nonneg _) (by norm_num)
    _ = 40 * ‖x‖ := by simp; ring

/-- Forward scaled-coordinate image of the ambient `D²` ball.  Linear
coordinates have radius `40HD`; quadratic coordinates have radius `40H²`. -/
theorem abs_bourgainNormalizedScaledPhaseCoordinates_apply_le
    {J H : ℕ} (hJ : 0 < J) (hH : 0 < H)
    {q a b : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 2)
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    {x : BourgainPhaseSpace}
    (hx : x ∈ bourgainSectionOnePhaseBall
      (bourgainSectionOneBlockDenominator J H))
    (i : Fin 4) :
    |bourgainGenericScaledPhaseCoordinates
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        ((H : ℝ) / bourgainSectionOneBlockDenominator J H) a b x i| ≤
      ![40 * (H : ℝ) * bourgainSectionOneBlockDenominator J H,
        40 * (H : ℝ) ^ (2 : ℕ),
        40 * (H : ℝ) * bourgainSectionOneBlockDenominator J H,
        40 * (H : ℝ) ^ (2 : ℕ)] i := by
  let D := bourgainSectionOneBlockDenominator J H
  have hD : 0 < D := bourgainSectionOneBlockDenominator_pos hJ hH
  have hbase (k : Fin 4) :
      |bourgainGenericPhaseCoordinates
          (bourgainNormalizedCubicRemainder q)
          (bourgainNormalizedQuarticRemainder q) a b x k| ≤
        40 * D ^ (2 : ℕ) := by
    exact (abs_bourgainNormalizedPhaseCoordinates_apply_le_forty
      hq hq1 ha hb x k).trans
        (mul_le_mul_of_nonneg_left hx (by norm_num))
  fin_cases i
  · simp [bourgainGenericScaledPhaseCoordinates,
      bourgainParabolaPhaseScale]
    rw [abs_of_pos (div_pos (by exact_mod_cast hH) hD)]
    have hcoord :
        |bourgainGenericLinearPhaseCoordinate
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q) a x| ≤
          40 * D ^ (2 : ℕ) := by
      simpa using hbase 0
    calc
      (H : ℝ) / D *
          |bourgainGenericLinearPhaseCoordinate
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q) a x| ≤
          (H : ℝ) / D * (40 * D ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hcoord (by positivity)
      _ = 40 * (H : ℝ) * D := by field_simp
  · simp [bourgainGenericScaledPhaseCoordinates,
      bourgainParabolaPhaseScale]
    have hcoord :
        |bourgainGenericQuadraticPhaseCoordinate
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q) a x| ≤
          40 * D ^ (2 : ℕ) := by
      simpa using hbase 1
    calc
      ((H : ℝ) / D) ^ (2 : ℕ) *
          |bourgainGenericQuadraticPhaseCoordinate
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q) a x| ≤
          ((H : ℝ) / D) ^ (2 : ℕ) * (40 * D ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hcoord (sq_nonneg _)
      _ = 40 * (H : ℝ) ^ (2 : ℕ) := by field_simp
  · simp [bourgainGenericScaledPhaseCoordinates,
      bourgainParabolaPhaseScale]
    rw [abs_of_pos (div_pos (by exact_mod_cast hH) hD)]
    have hcoord :
        |bourgainGenericLinearPhaseCoordinate
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q) b x| ≤
          40 * D ^ (2 : ℕ) := by
      simpa using hbase 2
    calc
      (H : ℝ) / D *
          |bourgainGenericLinearPhaseCoordinate
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q) b x| ≤
          (H : ℝ) / D * (40 * D ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hcoord (by positivity)
      _ = 40 * (H : ℝ) * D := by field_simp
  · simp [bourgainGenericScaledPhaseCoordinates,
      bourgainParabolaPhaseScale]
    have hcoord :
        |bourgainGenericQuadraticPhaseCoordinate
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q) b x| ≤
          40 * D ^ (2 : ℕ) := by
      simpa using hbase 3
    calc
      ((H : ℝ) / D) ^ (2 : ℕ) *
          |bourgainGenericQuadraticPhaseCoordinate
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q) b x| ≤
          ((H : ℝ) / D) ^ (2 : ℕ) * (40 * D ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hcoord (sq_nonneg _)
      _ = 40 * (H : ℝ) ^ (2 : ℕ) := by field_simp

/-- **Sharp `O(D²)` period-box containment.**

The scaled image of the full physical `D²` ball lies strictly inside the
explicit product grid. -/
theorem bourgainSectionOnePhaseBall_subset_scaledPhaseGrid
    {J H : ℕ} (hJ : 0 < J) (hH : 0 < H)
    {q a b : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 2)
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    bourgainSectionOnePhaseBall
        (bourgainSectionOneBlockDenominator J H) ⊆
      bourgainGenericScaledPhaseCoordinates
          (bourgainNormalizedCubicRemainder q)
          (bourgainNormalizedQuarticRemainder q)
          ((H : ℝ) / bourgainSectionOneBlockDenominator J H) a b ⁻¹'
        bourgainAnisotropicBox
          (bourgainAnisotropicGridRadius H
            (bourgainSectionOneGridMultiplicity J H)) := by
  intro x hx
  change
    bourgainGenericScaledPhaseCoordinates
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        ((H : ℝ) / bourgainSectionOneBlockDenominator J H) a b x ∈
      bourgainAnisotropicBox
        (bourgainAnisotropicGridRadius H
          (bourgainSectionOneGridMultiplicity J H))
  rw [bourgainAnisotropicBox]
  intro i hi
  have hbound :=
    abs_bourgainNormalizedScaledPhaseCoordinates_apply_le
      hJ hH hq hq1 ha hb hx i
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  fin_cases i
  all_goals
    simp [bourgainAnisotropicGridRadius,
      bourgainSectionOneGridMultiplicity,
      bourgainParabolaFundamentalHalfWidth,
      Set.mem_Ioc] at hbound ⊢
  · have hstrict :
        40 * (H : ℝ) * bourgainSectionOneBlockDenominator J H <
          ((320 * J * H + 1 : ℕ) : ℝ) * ((H : ℝ) / 2) := by
      unfold bourgainSectionOneBlockDenominator
      push_cast
      nlinarith
    push_cast at hstrict
    constructor <;> nlinarith [neg_le_of_abs_le hbound, le_of_abs_le hbound]
  · have hstrict :
        40 * (H : ℝ) ^ (2 : ℕ) <
          ((80 + 1 : ℕ) : ℝ) * ((H : ℝ) ^ (2 : ℕ) / 2) := by
      push_cast
      nlinarith [sq_pos_of_pos hHr]
    push_cast at hstrict
    constructor <;> nlinarith [neg_le_of_abs_le hbound, le_of_abs_le hbound]
  · have hstrict :
        40 * (H : ℝ) * bourgainSectionOneBlockDenominator J H <
          ((320 * J * H + 1 : ℕ) : ℝ) * ((H : ℝ) / 2) := by
      unfold bourgainSectionOneBlockDenominator
      push_cast
      nlinarith
    push_cast at hstrict
    constructor <;> nlinarith [neg_le_of_abs_le hbound, le_of_abs_le hbound]
  · have hstrict :
        40 * (H : ℝ) ^ (2 : ℕ) <
          ((80 + 1 : ℕ) : ℝ) * ((H : ℝ) ^ (2 : ℕ) / 2) := by
      push_cast
      nlinarith [sq_pos_of_pos hHr]
    push_cast at hstrict
    constructor <;> nlinarith [neg_le_of_abs_le hbound, le_of_abs_le hbound]

/-- Exact product cardinality of the Section-1 period grid. -/
theorem card_bourgainSectionOneGridMultiplicity
    (J H : ℕ) :
    (∏ i : Fin 4, (bourgainSectionOneGridMultiplicity J H i + 1)) =
      (320 * J * H + 1) ^ (2 : ℕ) * 81 ^ (2 : ℕ) := by
  simp [bourgainSectionOneGridMultiplicity, Fin.prod_univ_four]
  ring

/-- Quantitative `O(D²)` cardinality bound.  Constant is deliberately
coarse; scale exponent is exact. -/
theorem card_bourgainSectionOneGridMultiplicity_le
    {J H : ℕ} (hJ : 0 < J) (hH : 0 < H) :
    ((∏ i : Fin 4,
        (bourgainSectionOneGridMultiplicity J H i + 1) : ℕ) : ℝ) ≤
      26001 ^ (2 : ℕ) *
        bourgainSectionOneBlockDenominator J H ^ (2 : ℕ) := by
  rw [card_bourgainSectionOneGridMultiplicity]
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  push_cast
  let X : ℝ := (J : ℝ) * (H : ℝ)
  have hX : 1 ≤ X := by
    dsimp [X]
    nlinarith [mul_nonneg (le_trans (by norm_num) hJr)
      (le_trans (by norm_num) hHr),
      mul_nonneg (sub_nonneg.mpr hJr) (sub_nonneg.mpr hHr)]
  have hlin : 320 * X + 1 ≤ 321 * X := by linarith
  have hsquare :
      (320 * X + 1) ^ (2 : ℕ) ≤ (321 * X) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hlin 2
  have hden :
      bourgainSectionOneBlockDenominator J H = 4 * X := by
    unfold bourgainSectionOneBlockDenominator
    dsimp [X]
    ring
  have hlinear :
      320 * (J : ℝ) * (H : ℝ) = 320 * X := by
    dsimp [X]
    ring
  rw [hden, hlinear]
  change
    (320 * X + 1) ^ (2 : ℕ) * 6561 ≤
      26001 ^ (2 : ℕ) * (4 * X) ^ (2 : ℕ)
  calc
    (320 * X + 1) ^ (2 : ℕ) * 6561 ≤
        (321 * X) ^ (2 : ℕ) * 6561 := by
      gcongr
    _ = 26001 ^ (2 : ℕ) * X ^ (2 : ℕ) := by ring
    _ ≤ 26001 ^ (2 : ℕ) * (4 * X) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg X]

/-- Exact cancellation of block scale in one cell: the reciprocal scaled
Jacobian times natural cell volume is at most an absolute constant times
`D⁶`, with no residual `H` power. -/
theorem bourgainSectionOneCellJacobianScale_le
    {H : ℕ} (hH : 0 < H) {D q a b : ℝ}
    (hD : 0 < D) (hq : 0 < q) (hq1 : q ≤ 1 / 2)
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hab : 1 / 4 ≤ b - a) :
    |((((H : ℝ) / D) ^ (6 : ℕ)) *
        (bourgainGenericPhaseCoordinateMatrix
          (bourgainNormalizedCubicRemainder q)
          (bourgainNormalizedQuarticRemainder q) a b).det)⁻¹| *
        (H : ℝ) ^ (6 : ℕ) ≤
      (131072 / 3 : ℝ) * D ^ (6 : ℕ) := by
  let A :=
    bourgainGenericPhaseCoordinateMatrix
      (bourgainNormalizedCubicRemainder q)
      (bourgainNormalizedQuarticRemainder q) a b
  have hdetLower : (3 / 131072 : ℝ) ≤ A.det :=
    det_bourgainGenericPhaseCoordinateMatrix_normalized_ge
      hq hq1 ha hb hab
  have hdet : 0 < A.det := lt_of_lt_of_le (by norm_num) hdetLower
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hscale : 0 < (H : ℝ) / D := div_pos hHr hD
  change
    |((((H : ℝ) / D) ^ (6 : ℕ)) * A.det)⁻¹| *
        (H : ℝ) ^ (6 : ℕ) ≤
      (131072 / 3 : ℝ) * D ^ (6 : ℕ)
  rw [abs_inv, abs_mul, abs_of_pos (pow_pos hscale 6), abs_of_pos hdet]
  have hcancel :
      ((((H : ℝ) / D) ^ (6 : ℕ) * A.det)⁻¹) *
          (H : ℝ) ^ (6 : ℕ) =
        D ^ (6 : ℕ) * A.det⁻¹ := by
    field_simp
  rw [hcancel]
  have hinv : A.det⁻¹ ≤ (131072 / 3 : ℝ) := by
    apply (inv_le_comm₀ hdet (by norm_num)).2
    norm_num
    exact hdetLower
  calc
    D ^ (6 : ℕ) * A.det⁻¹ ≤
        D ^ (6 : ℕ) * (131072 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hinv (pow_nonneg hD.le 6)
    _ = (131072 / 3 : ℝ) * D ^ (6 : ℕ) := by ring

/-- **Exact Section-1 scale conservation.**

Period multiplicity `D²` times normalized-cell Jacobian scale `D⁶` is
bounded by an absolute constant times physical four-volume `D⁸`.  Fine
block length `H` disappears completely. -/
theorem bourgainSectionOne_gridCard_mul_cellJacobianScale_le
    {J H : ℕ} (hJ : 0 < J) (hH : 0 < H)
    {q a b : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 2)
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hab : 1 / 4 ≤ b - a) :
    ((∏ i : Fin 4,
        (bourgainSectionOneGridMultiplicity J H i + 1) : ℕ) : ℝ) *
      (|((((H : ℝ) /
          bourgainSectionOneBlockDenominator J H) ^ (6 : ℕ)) *
          (bourgainGenericPhaseCoordinateMatrix
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q) a b).det)⁻¹| *
        (H : ℝ) ^ (6 : ℕ)) ≤
      (26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
        bourgainSectionOneBlockDenominator J H ^ (8 : ℕ) := by
  let D := bourgainSectionOneBlockDenominator J H
  let card : ℝ :=
    ((∏ i : Fin 4,
      (bourgainSectionOneGridMultiplicity J H i + 1) : ℕ) : ℝ)
  let cell : ℝ :=
    |((((H : ℝ) / D) ^ (6 : ℕ)) *
        (bourgainGenericPhaseCoordinateMatrix
          (bourgainNormalizedCubicRemainder q)
          (bourgainNormalizedQuarticRemainder q) a b).det)⁻¹| *
      (H : ℝ) ^ (6 : ℕ)
  have hD : 0 < D := bourgainSectionOneBlockDenominator_pos hJ hH
  have hcard : card ≤ 26001 ^ (2 : ℕ) * D ^ (2 : ℕ) := by
    simpa [card, D] using
      card_bourgainSectionOneGridMultiplicity_le hJ hH
  have hcell : cell ≤ (131072 / 3 : ℝ) * D ^ (6 : ℕ) := by
    simpa [cell, D] using
      bourgainSectionOneCellJacobianScale_le
        hH hD hq hq1 ha hb hab
  have hcard0 : 0 ≤ card := by
    dsimp [card]
    positivity
  have hcell0 : 0 ≤ cell := by
    dsimp [cell]
    positivity
  change card * cell ≤ _
  calc
    card * cell ≤
        (26001 ^ (2 : ℕ) * D ^ (2 : ℕ)) *
          ((131072 / 3 : ℝ) * D ^ (6 : ℕ)) :=
      mul_le_mul hcard hcell hcell0 (by positivity)
    _ = (26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
        D ^ (8 : ℕ) := by ring

/-- `ENNReal` form of Section-1 scale conservation, ready for set-integral
aggregation. -/
theorem bourgainSectionOne_gridCard_mul_cellJacobianScale_ennreal_le
    {J H : ℕ} (hJ : 0 < J) (hH : 0 < H)
    {q a b : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 2)
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hab : 1 / 4 ≤ b - a) :
    ((∏ i : Fin 4,
        (bourgainSectionOneGridMultiplicity J H i + 1) : ℕ) : ENNReal) *
      (ENNReal.ofReal
          |((((H : ℝ) /
            bourgainSectionOneBlockDenominator J H) ^ (6 : ℕ)) *
            (bourgainGenericPhaseCoordinateMatrix
              (bourgainNormalizedCubicRemainder q)
              (bourgainNormalizedQuarticRemainder q) a b).det)⁻¹| *
        ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ))) ≤
      ENNReal.ofReal
        ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
          bourgainSectionOneBlockDenominator J H ^ (8 : ℕ)) := by
  let card : ℝ :=
    ((∏ i : Fin 4,
      (bourgainSectionOneGridMultiplicity J H i + 1) : ℕ) : ℝ)
  let jac : ℝ :=
    |((((H : ℝ) /
      bourgainSectionOneBlockDenominator J H) ^ (6 : ℕ)) *
      (bourgainGenericPhaseCoordinateMatrix
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q) a b).det)⁻¹|
  have hreal :=
    bourgainSectionOne_gridCard_mul_cellJacobianScale_le
      hJ hH hq hq1 ha hb hab
  have hof := ENNReal.ofReal_le_ofReal hreal
  have hcard0 : 0 ≤ card := by
    dsimp [card]
    positivity
  have hjac0 : 0 ≤ jac := by
    dsimp [jac]
    positivity
  rw [ENNReal.ofReal_mul hcard0,
    ENNReal.ofReal_mul hjac0,
    ENNReal.ofReal_natCast] at hof
  simpa [card, jac, mul_assoc] using hof

/-- Translate one generic pulled-back period cell in physical phase space. -/
def bourgainTranslatedGenericOsculatingFundamentalCell
    (H : ℕ) (φ₃ φ₄ : ℝ → ℝ) (scale a b : ℝ)
    (y : BourgainPhaseSpace) : Set BourgainPhaseSpace :=
  (fun x => x + y) ''
    bourgainGenericOsculatingFundamentalCell H φ₃ φ₄ scale a b

theorem setLIntegral_bourgainTranslatedGenericOsculatingFundamentalCell
    (H : ℕ) (φ₃ φ₄ : ℝ → ℝ) (scale a b : ℝ)
    (y : BourgainPhaseSpace) (f : BourgainPhaseSpace → ENNReal) :
    (∫⁻ z in bourgainTranslatedGenericOsculatingFundamentalCell
        H φ₃ φ₄ scale a b y, f z) =
      ∫⁻ x in bourgainGenericOsculatingFundamentalCell
          H φ₃ φ₄ scale a b,
        f (x + y) := by
  symm
  exact
    (measurePreserving_add_right volume y).setLIntegral_comp_emb
      (Homeomorph.addRight y).isClosedEmbedding.measurableEmbedding
      f (bourgainGenericOsculatingFundamentalCell
        H φ₃ φ₄ scale a b)

/-- Pullback of one explicit anisotropic grid center through generic scaled
jet coordinates. -/
def bourgainGenericOsculatingGridCenter
    (φ₃ φ₄ : ℝ → ℝ) {scale a b : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit
      (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (H : ℕ) (m : Fin 4 → ℕ)
    (k : BourgainAnisotropicGridIndex m) : BourgainPhaseSpace :=
  (bourgainGenericScaledPhaseContinuousLinearEquiv
    φ₃ φ₄ hscale hunit).symm
      (bourgainAnisotropicPhaseGridCenter H m k)

/-- Generic counterpart of the explicit pulled-back period-grid cover. -/
theorem
    preimage_bourgainAnisotropicBox_subset_genericOsculatingGridCover
    (H : ℕ) (m : Fin 4 → ℕ) (φ₃ φ₄ : ℝ → ℝ)
    {scale a b : ℝ} (hscale : scale ≠ 0)
    (hunit : IsUnit
      (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b)) :
    bourgainGenericScaledPhaseCoordinates φ₃ φ₄ scale a b ⁻¹'
        bourgainAnisotropicBox
          (bourgainAnisotropicGridRadius H m) ⊆
      ⋃ k : BourgainAnisotropicGridIndex m,
        bourgainTranslatedGenericOsculatingFundamentalCell
          H φ₃ φ₄ scale a b
          (bourgainGenericOsculatingGridCenter
            φ₃ φ₄ hscale hunit H m k) := by
  intro x hx
  have hphase :=
    bourgainAnisotropicBox_subset_phaseGridCover H m hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hphase
  apply Set.mem_iUnion.2
  refine ⟨k, ?_⟩
  obtain ⟨w, hw, hwy⟩ := hk
  let E :=
    bourgainGenericScaledPhaseContinuousLinearEquiv
      φ₃ φ₄ hscale hunit
  let c := bourgainAnisotropicPhaseGridCenter H m k
  let y :=
    bourgainGenericOsculatingGridCenter
      φ₃ φ₄ hscale hunit H m k
  refine ⟨x - y, ?_, sub_add_cancel x y⟩
  change
    bourgainGenericScaledPhaseCoordinates φ₃ φ₄ scale a b (x - y) ∈
      bourgainParabolaFundamentalCell H
  have hEy : E y = c := by
    dsimp [E, y, c, bourgainGenericOsculatingGridCenter]
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hEx :
      E x = bourgainGenericScaledPhaseCoordinates
        φ₃ φ₄ scale a b x :=
    bourgainGenericScaledPhaseContinuousLinearEquiv_apply
      φ₃ φ₄ hscale hunit x
  have hwy' : w + c = E x := by
    simpa [c, hEx] using hwy
  have hdiff : E (x - y) = w := by
    rw [map_sub, hEy]
    exact sub_eq_of_eq_add hwy'.symm
  rw [← bourgainGenericScaledPhaseContinuousLinearEquiv_apply
    φ₃ φ₄ hscale hunit, hdiff]
  exact hw

/-- Finite aggregation over the generic pulled-back period grid. -/
theorem
    setLIntegral_preimage_bourgainAnisotropicBox_le_genericGridCard_mul
    (H : ℕ) (m : Fin 4 → ℕ) (φ₃ φ₄ : ℝ → ℝ)
    {scale a b : ℝ} (hscale : scale ≠ 0)
    (hunit : IsUnit
      (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (f : BourgainPhaseSpace → ENNReal) {B : ENNReal}
    (hlocal :
      ∀ k : BourgainAnisotropicGridIndex m,
        (∫⁻ x in bourgainTranslatedGenericOsculatingFundamentalCell
            H φ₃ φ₄ scale a b
            (bourgainGenericOsculatingGridCenter
              φ₃ φ₄ hscale hunit H m k),
          f x) ≤ B) :
    (∫⁻ x in
      bourgainGenericScaledPhaseCoordinates φ₃ φ₄ scale a b ⁻¹'
        bourgainAnisotropicBox
          (bourgainAnisotropicGridRadius H m),
      f x) ≤
        ((∏ j : Fin 4, (m j + 1) : ℕ) : ENNReal) * B := by
  have hcover :=
    preimage_bourgainAnisotropicBox_subset_genericOsculatingGridCover
      H m φ₃ φ₄ hscale hunit
  have hbound :=
    setLIntegral_le_card_mul_of_finite_cover
      (bourgainGenericScaledPhaseCoordinates φ₃ φ₄ scale a b ⁻¹'
        bourgainAnisotropicBox
          (bourgainAnisotropicGridRadius H m))
      (fun k : BourgainAnisotropicGridIndex m =>
        bourgainTranslatedGenericOsculatingFundamentalCell
          H φ₃ φ₄ scale a b
          (bourgainGenericOsculatingGridCenter
            φ₃ φ₄ hscale hunit H m k))
      f hcover hlocal
  simpa [card_bourgainAnisotropicGridIndex] using hbound

/-- Translation-uniform sharp normalized exact-curve cell estimate. -/
theorem
    setLIntegral_bourgainNormalizedExactLocalSum_translatedCell_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (_hH : 0 < H)
        {q D a b : ℝ}
        (_hq : 0 < q) (_hq1 : q ≤ 1 / 2)
        (_hD : 0 < D) (_hHD : (H : ℝ) ≤ D)
        (_ha0 : 0 ≤ a) (_ha1 : a + (H : ℝ) / D ≤ 1)
        (_hb0 : 0 ≤ b) (_hb1 : b + (H : ℝ) / D ≤ 1)
        (_hab : 1 / 4 ≤ b - a)
        (_hsmall :
          50331648000 * (H : ℝ) ^ (3 : ℕ) / D ≤ 1 / 24)
        (c₁ c₂ : Fin H → ℂ) (y : BourgainPhaseSpace),
        let φ₃ := bourgainNormalizedCubicRemainder q
        let φ₄ := bourgainNormalizedQuarticRemainder q
        (∫⁻ x in bourgainTranslatedGenericOsculatingFundamentalCell
            H φ₃ φ₄ ((H : ℝ) / D) a b y,
          ENNReal.ofReal
            (‖bourgainGenericFourCurveExactLocalSum
                H φ₃ φ₄ D a c₁ x‖ ^ (6 : ℕ) *
              ‖bourgainGenericFourCurveExactLocalSum
                H φ₃ φ₄ D b c₂ x‖ ^ (6 : ℕ))) ≤
          ENNReal.ofReal
              |((((H : ℝ) / D) ^ (6 : ℕ)) *
                (bourgainGenericPhaseCoordinateMatrix
                  φ₃ φ₄ a b).det)⁻¹| *
            ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
            ENNReal.ofReal
              (C * (H : ℝ) ^ ε *
                (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hcell⟩ :=
    setLIntegral_bourgainNormalizedExactLocalSum_fundamentalCell_subpower
      hε
  refine ⟨C, hC, ?_⟩
  intro H hH q D a b hq hq1 hD hHD
    ha0 ha1 hb0 hb1 hab hsmall c₁ c₂ y
  dsimp only
  let φ₃ := bourgainNormalizedCubicRemainder q
  let φ₄ := bourgainNormalizedQuarticRemainder q
  let c₁' :=
    bourgainGenericExactLocalTranslateCoefficients
      H φ₃ φ₄ D a c₁ y
  let c₂' :=
    bourgainGenericExactLocalTranslateCoefficients
      H φ₃ φ₄ D b c₂ y
  have hbound :=
    hcell H hH hq hq1 hD hHD ha0 ha1 hb0 hb1 hab hsmall c₁' c₂'
  rw [setLIntegral_bourgainTranslatedGenericOsculatingFundamentalCell]
  calc
    (∫⁻ x in bourgainGenericOsculatingFundamentalCell
        H φ₃ φ₄ ((H : ℝ) / D) a b,
      ENNReal.ofReal
        (‖bourgainGenericFourCurveExactLocalSum
            H φ₃ φ₄ D a c₁ (x + y)‖ ^ (6 : ℕ) *
          ‖bourgainGenericFourCurveExactLocalSum
            H φ₃ φ₄ D b c₂ (x + y)‖ ^ (6 : ℕ))) =
      ∫⁻ x in bourgainGenericOsculatingFundamentalCell
        H φ₃ φ₄ ((H : ℝ) / D) a b,
      ENNReal.ofReal
        (‖bourgainGenericFourCurveExactLocalSum
            H φ₃ φ₄ D a c₁' x‖ ^ (6 : ℕ) *
          ‖bourgainGenericFourCurveExactLocalSum
            H φ₃ φ₄ D b c₂' x‖ ^ (6 : ℕ)) := by
        apply lintegral_congr
        intro x
        rw [bourgainGenericFourCurveExactLocalSum_add,
          bourgainGenericFourCurveExactLocalSum_add]
    _ ≤ _ := by
      simpa [c₁', c₂',
        sum_norm_sq_bourgainGenericExactLocalTranslateCoefficients]
        using hbound

/-- **Global sharp Section-1 block-pair estimate with exact cover factor.**

The local perturbation-stable cell theorem is summed over the full physical
`D²` ball.  Its only multiplicity is the explicit `O(D²)` period count
proved above. -/
theorem setLIntegral_bourgainSectionOneBlockPair_phaseBall_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J H : ℕ) (_hJ : 0 < J) (_hH : 0 < H)
        (_hscale :
          6 * bourgainSectionOneTaylorConstant *
              (H : ℝ) ^ (2 : ℕ) ≤ J)
        {q : ℝ} (_hq : 0 < q) (_hq1 : q ≤ 1 / 2)
        (i j : Fin J) (c₁ c₂ : Fin H → ℂ),
        let D := bourgainSectionOneBlockDenominator J H
        let a := bourgainSectionOneLeftBlockBase J i
        let b := bourgainSectionOneRightBlockBase J j
        let φ₃ := bourgainNormalizedCubicRemainder q
        let φ₄ := bourgainNormalizedQuarticRemainder q
        (∫⁻ x in bourgainSectionOnePhaseBall D,
          ENNReal.ofReal
            (‖bourgainGenericFourCurveExactLocalSum
                H φ₃ φ₄ D a c₁ x‖ ^ (6 : ℕ) *
              ‖bourgainGenericFourCurveExactLocalSum
                H φ₃ φ₄ D b c₂ x‖ ^ (6 : ℕ))) ≤
          ((∏ r : Fin 4,
              (bourgainSectionOneGridMultiplicity J H r + 1) : ℕ) :
              ENNReal) *
            (ENNReal.ofReal
                |((((H : ℝ) / D) ^ (6 : ℕ)) *
                  (bourgainGenericPhaseCoordinateMatrix
                    φ₃ φ₄ a b).det)⁻¹| *
              ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
              ENNReal.ofReal
                (C * (H : ℝ) ^ ε *
                  (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                  (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) := by
  obtain ⟨C, hC, htranslated⟩ :=
    setLIntegral_bourgainNormalizedExactLocalSum_translatedCell_subpower
      hε
  refine ⟨C, hC, ?_⟩
  intro J H hJ hH hscale q hq hq1 i j c₁ c₂
  dsimp only
  let D := bourgainSectionOneBlockDenominator J H
  let a := bourgainSectionOneLeftBlockBase J i
  let b := bourgainSectionOneRightBlockBase J j
  let φ₃ := bourgainNormalizedCubicRemainder q
  let φ₄ := bourgainNormalizedQuarticRemainder q
  let m := bourgainSectionOneGridMultiplicity J H
  let f : BourgainPhaseSpace → ENNReal := fun x =>
    ENNReal.ofReal
      (‖bourgainGenericFourCurveExactLocalSum
          H φ₃ φ₄ D a c₁ x‖ ^ (6 : ℕ) *
        ‖bourgainGenericFourCurveExactLocalSum
          H φ₃ φ₄ D b c₂ x‖ ^ (6 : ℕ))
  let B : ENNReal :=
    ENNReal.ofReal
        |((((H : ℝ) / D) ^ (6 : ℕ)) *
          (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b).det)⁻¹| *
      ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
      ENNReal.ofReal
        (C * (H : ℝ) ^ ε *
          (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
          (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))
  have hD : 0 < D := bourgainSectionOneBlockDenominator_pos hJ hH
  have hHD : (H : ℝ) ≤ D := by
    unfold D bourgainSectionOneBlockDenominator
    have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have hHr : (0 : ℝ) ≤ H := by positivity
    nlinarith
  have ha0 : 0 ≤ a := bourgainSectionOneLeftBlockBase_nonneg hJ i
  have ha1 : a + (H : ℝ) / D ≤ 1 :=
    (bourgainSectionOneLeftBlock_end_le_quarter hJ hH i).trans
      (by norm_num)
  have hb0 : 0 ≤ b := bourgainSectionOneRightBlockBase_nonneg hJ j
  have hb1 : b + (H : ℝ) / D ≤ 1 :=
    (bourgainSectionOneRightBlock_end_le_threeQuarter hJ hH j).trans
      (by norm_num)
  have hab : 1 / 4 ≤ b - a :=
    bourgainSectionOneBlockBases_separated hJ i j
  have hsmall :
      bourgainSectionOneTaylorConstant * (H : ℝ) ^ (3 : ℕ) / D ≤
        1 / 24 :=
    bourgainSectionOneBlock_taylor_small hJ hH hscale
  have ha : a ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact ha0
    · have : 0 ≤ (H : ℝ) / D := by positivity
      linarith
  have hb : b ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact hb0
    · have : 0 ≤ (H : ℝ) / D := by positivity
      linarith
  let hunit :=
    isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
      hq hq1 ha hb hab
  let hcoordScale : (H : ℝ) / D ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  have hsubset :
      bourgainSectionOnePhaseBall D ⊆
        bourgainGenericScaledPhaseCoordinates
            φ₃ φ₄ ((H : ℝ) / D) a b ⁻¹'
          bourgainAnisotropicBox
            (bourgainAnisotropicGridRadius H m) := by
    simpa [D, a, b, φ₃, φ₄, m] using
      (bourgainSectionOnePhaseBall_subset_scaledPhaseGrid
        hJ hH hq hq1 ha hb)
  have hlocal :
      ∀ k : BourgainAnisotropicGridIndex m,
        (∫⁻ x in bourgainTranslatedGenericOsculatingFundamentalCell
            H φ₃ φ₄ ((H : ℝ) / D) a b
            (bourgainGenericOsculatingGridCenter
              φ₃ φ₄ hcoordScale hunit H m k),
          f x) ≤ B := by
    intro k
    simpa [D, a, b, φ₃, φ₄, f, B] using
      (htranslated H hH hq hq1 hD hHD
        ha0 ha1 hb0 hb1 hab hsmall c₁ c₂
        (bourgainGenericOsculatingGridCenter
          φ₃ φ₄ hcoordScale hunit H m k))
  have hgrid :=
    setLIntegral_preimage_bourgainAnisotropicBox_le_genericGridCard_mul
      H m φ₃ φ₄ hcoordScale hunit f hlocal
  calc
    (∫⁻ x in bourgainSectionOnePhaseBall D, f x) ≤
        ∫⁻ x in
          bourgainGenericScaledPhaseCoordinates
              φ₃ φ₄ ((H : ℝ) / D) a b ⁻¹'
            bourgainAnisotropicBox
              (bourgainAnisotropicGridRadius H m),
          f x := lintegral_mono_set hsubset
    _ ≤ ((∏ r : Fin 4, (m r + 1) : ℕ) : ENNReal) * B := hgrid
    _ = _ := by rfl

/-- **Volume-scale global Section-1 bilinear estimate.**

After exact cell aggregation, all geometric factors collapse to ambient
four-volume `D⁸`.  Thus normalized global bilinear moment has only the
subpower loss inherited from sharp planar arithmetic, uniformly in fine
block scale. -/
theorem setLIntegral_bourgainSectionOneBlockPair_phaseBall_volumeScale_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J H : ℕ) (_hJ : 0 < J) (_hH : 0 < H)
        (_hscale :
          6 * bourgainSectionOneTaylorConstant *
              (H : ℝ) ^ (2 : ℕ) ≤ J)
        {q : ℝ} (_hq : 0 < q) (_hq1 : q ≤ 1 / 2)
        (i j : Fin J) (c₁ c₂ : Fin H → ℂ),
        let D := bourgainSectionOneBlockDenominator J H
        let a := bourgainSectionOneLeftBlockBase J i
        let b := bourgainSectionOneRightBlockBase J j
        let φ₃ := bourgainNormalizedCubicRemainder q
        let φ₄ := bourgainNormalizedQuarticRemainder q
        (∫⁻ x in bourgainSectionOnePhaseBall D,
          ENNReal.ofReal
            (‖bourgainGenericFourCurveExactLocalSum
                H φ₃ φ₄ D a c₁ x‖ ^ (6 : ℕ) *
              ‖bourgainGenericFourCurveExactLocalSum
                H φ₃ φ₄ D b c₂ x‖ ^ (6 : ℕ))) ≤
          ENNReal.ofReal
              ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
                D ^ (8 : ℕ)) *
            ENNReal.ofReal
              (C * (H : ℝ) ^ ε *
                (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hraw⟩ :=
    setLIntegral_bourgainSectionOneBlockPair_phaseBall_subpower hε
  refine ⟨C, hC, ?_⟩
  intro J H hJ hH hscale q hq hq1 i j c₁ c₂
  dsimp only
  let D := bourgainSectionOneBlockDenominator J H
  let a := bourgainSectionOneLeftBlockBase J i
  let b := bourgainSectionOneRightBlockBase J j
  let φ₃ := bourgainNormalizedCubicRemainder q
  let φ₄ := bourgainNormalizedQuarticRemainder q
  let A : ENNReal :=
    ((∏ r : Fin 4,
      (bourgainSectionOneGridMultiplicity J H r + 1) : ℕ) : ENNReal)
  let cell : ENNReal :=
    ENNReal.ofReal
        |((((H : ℝ) / D) ^ (6 : ℕ)) *
          (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b).det)⁻¹| *
      ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ))
  let analytic : ENNReal :=
    ENNReal.ofReal
      (C * (H : ℝ) ^ ε *
        (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
        (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))
  have ha0 : 0 ≤ a := bourgainSectionOneLeftBlockBase_nonneg hJ i
  have ha1 : a + (H : ℝ) / D ≤ 1 :=
    (bourgainSectionOneLeftBlock_end_le_quarter hJ hH i).trans
      (by norm_num)
  have hb0 : 0 ≤ b := bourgainSectionOneRightBlockBase_nonneg hJ j
  have hb1 : b + (H : ℝ) / D ≤ 1 :=
    (bourgainSectionOneRightBlock_end_le_threeQuarter hJ hH j).trans
      (by norm_num)
  have ha : a ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact ha0
    · have hD := bourgainSectionOneBlockDenominator_pos hJ hH
      have : 0 ≤ (H : ℝ) / D := by positivity
      linarith
  have hb : b ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact hb0
    · have hD := bourgainSectionOneBlockDenominator_pos hJ hH
      have : 0 ≤ (H : ℝ) / D := by positivity
      linarith
  have hab : 1 / 4 ≤ b - a :=
    bourgainSectionOneBlockBases_separated hJ i j
  have hscaleENN :
      A * cell ≤
        ENNReal.ofReal
          ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) * D ^ (8 : ℕ)) := by
    simpa [A, cell, D, a, b, φ₃, φ₄] using
      (bourgainSectionOne_gridCard_mul_cellJacobianScale_ennreal_le
        hJ hH hq hq1 ha hb hab)
  have hraw' := hraw J H hJ hH hscale hq hq1 i j c₁ c₂
  change
    (∫⁻ x in bourgainSectionOnePhaseBall D,
      ENNReal.ofReal
        (‖bourgainGenericFourCurveExactLocalSum
            H φ₃ φ₄ D a c₁ x‖ ^ (6 : ℕ) *
          ‖bourgainGenericFourCurveExactLocalSum
            H φ₃ φ₄ D b c₂ x‖ ^ (6 : ℕ))) ≤ _
  calc
    (∫⁻ x in bourgainSectionOnePhaseBall D,
      ENNReal.ofReal
        (‖bourgainGenericFourCurveExactLocalSum
            H φ₃ φ₄ D a c₁ x‖ ^ (6 : ℕ) *
          ‖bourgainGenericFourCurveExactLocalSum
            H φ₃ φ₄ D b c₂ x‖ ^ (6 : ℕ))) ≤
        A * (cell * analytic) := by
      simpa [A, cell, analytic, D, a, b, φ₃, φ₄] using hraw'
    _ = (A * cell) * analytic := by ring
    _ ≤ ENNReal.ofReal
          ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) * D ^ (8 : ℕ)) *
        analytic := by
      simpa [mul_comm] using mul_le_mul_right hscaleENN analytic
    _ = _ := by rfl

/-- Sum of all separated left/right coarse-block moments in one Section-1
refinement step. -/
def bourgainSectionOneBlockPairFamilyMoment
    (J H : ℕ) (q : ℝ)
    (c₁ c₂ : Fin (J * H) → ℂ) : ENNReal :=
  let D := bourgainSectionOneBlockDenominator J H
  let φ₃ := bourgainNormalizedCubicRemainder q
  let φ₄ := bourgainNormalizedQuarticRemainder q
  ∑ i : Fin J, ∑ j : Fin J,
    ∫⁻ x in bourgainSectionOnePhaseBall D,
      ENNReal.ofReal
        (‖bourgainGenericFourCurveExactLocalSum
            H φ₃ φ₄ D
            (bourgainSectionOneLeftBlockBase J i)
            (bourgainGenericCurveBlockCoefficients J H c₁ i) x‖ ^
              (6 : ℕ) *
          ‖bourgainGenericFourCurveExactLocalSum
            H φ₃ φ₄ D
            (bourgainSectionOneRightBlockBase J j)
            (bourgainGenericCurveBlockCoefficients J H c₂ j) x‖ ^
              (6 : ℕ))

/-- **Recurrence-ready planar refinement before finite Hölder.**

Summing all block-pair estimates introduces no block-count entropy: the
right side is exactly product of sums of cubic block `ℓ²` masses. -/
theorem bourgainSectionOneBlockPairFamilyMoment_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J H : ℕ) (_hJ : 0 < J) (_hH : 0 < H)
        (_hscale :
          6 * bourgainSectionOneTaylorConstant *
              (H : ℝ) ^ (2 : ℕ) ≤ J)
        {q : ℝ} (_hq : 0 < q) (_hq1 : q ≤ 1 / 2)
        (c₁ c₂ : Fin (J * H) → ℂ),
        bourgainSectionOneBlockPairFamilyMoment J H q c₁ c₂ ≤
          ENNReal.ofReal
              ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
                bourgainSectionOneBlockDenominator J H ^ (8 : ℕ)) *
            ENNReal.ofReal
              (C * (H : ℝ) ^ ε *
                (∑ i : Fin J,
                  (∑ n : Fin H,
                    ‖bourgainGenericCurveBlockCoefficients
                      J H c₁ i n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) *
                (∑ j : Fin J,
                  (∑ n : Fin H,
                    ‖bourgainGenericCurveBlockCoefficients
                      J H c₂ j n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) := by
  obtain ⟨C, hC, hpair⟩ :=
    setLIntegral_bourgainSectionOneBlockPair_phaseBall_volumeScale_subpower
      hε
  refine ⟨C, hC, ?_⟩
  intro J H hJ hH hscale q hq hq1 c₁ c₂
  let V : ENNReal :=
    ENNReal.ofReal
      ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
        bourgainSectionOneBlockDenominator J H ^ (8 : ℕ))
  let A : ℝ := C * (H : ℝ) ^ ε
  let M₁ : Fin J → ℝ := fun i =>
    (∑ n : Fin H,
      ‖bourgainGenericCurveBlockCoefficients J H c₁ i n‖ ^
        (2 : ℕ)) ^ (3 : ℕ)
  let M₂ : Fin J → ℝ := fun j =>
    (∑ n : Fin H,
      ‖bourgainGenericCurveBlockCoefficients J H c₂ j n‖ ^
        (2 : ℕ)) ^ (3 : ℕ)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hM₁ (i : Fin J) : 0 ≤ M₁ i := by
    dsimp [M₁]
    positivity
  have hM₂ (j : Fin J) : 0 ≤ M₂ j := by
    dsimp [M₂]
    positivity
  have hterm (i j : Fin J) : 0 ≤ A * M₁ i * M₂ j := by
    positivity
  have hsumOfReal :
      (∑ i : Fin J, ∑ j : Fin J,
        ENNReal.ofReal (A * M₁ i * M₂ j)) =
      ENNReal.ofReal
        (∑ i : Fin J, ∑ j : Fin J, A * M₁ i * M₂ j) := by
    calc
      (∑ i : Fin J, ∑ j : Fin J,
          ENNReal.ofReal (A * M₁ i * M₂ j)) =
        ∑ i : Fin J,
          ENNReal.ofReal (∑ j : Fin J, A * M₁ i * M₂ j) := by
            apply Finset.sum_congr rfl
            intro i hi
            symm
            exact ENNReal.ofReal_sum_of_nonneg
              (fun j hj => hterm i j)
      _ = ENNReal.ofReal
          (∑ i : Fin J, ∑ j : Fin J, A * M₁ i * M₂ j) := by
            symm
            exact ENNReal.ofReal_sum_of_nonneg
              (fun i hi => Finset.sum_nonneg fun j hj => hterm i j)
  have hfactor :
      (∑ i : Fin J, ∑ j : Fin J, A * M₁ i * M₂ j) =
        A * (∑ i : Fin J, M₁ i) * (∑ j : Fin J, M₂ j) := by
    calc
      (∑ i : Fin J, ∑ j : Fin J, A * M₁ i * M₂ j) =
          ∑ i : Fin J, (A * M₁ i) * ∑ j : Fin J, M₂ j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = (∑ i : Fin J, A * M₁ i) *
          (∑ j : Fin J, M₂ j) := by
        rw [Finset.sum_mul]
      _ = A * (∑ i : Fin J, M₁ i) * (∑ j : Fin J, M₂ j) := by
        congr 1
        rw [Finset.mul_sum]
  have hpairwise (i j : Fin J) :=
    hpair J H hJ hH hscale hq hq1 i j
      (bourgainGenericCurveBlockCoefficients J H c₁ i)
      (bourgainGenericCurveBlockCoefficients J H c₂ j)
  unfold bourgainSectionOneBlockPairFamilyMoment
  dsimp only
  calc
    (∑ i : Fin J, ∑ j : Fin J,
      ∫⁻ x in bourgainSectionOnePhaseBall
          (bourgainSectionOneBlockDenominator J H),
        ENNReal.ofReal
          (‖bourgainGenericFourCurveExactLocalSum
              H (bourgainNormalizedCubicRemainder q)
              (bourgainNormalizedQuarticRemainder q)
              (bourgainSectionOneBlockDenominator J H)
              (bourgainSectionOneLeftBlockBase J i)
              (bourgainGenericCurveBlockCoefficients J H c₁ i) x‖ ^
                (6 : ℕ) *
            ‖bourgainGenericFourCurveExactLocalSum
              H (bourgainNormalizedCubicRemainder q)
              (bourgainNormalizedQuarticRemainder q)
              (bourgainSectionOneBlockDenominator J H)
              (bourgainSectionOneRightBlockBase J j)
              (bourgainGenericCurveBlockCoefficients J H c₂ j) x‖ ^
                (6 : ℕ))) ≤
        ∑ i : Fin J, ∑ j : Fin J,
          V * ENNReal.ofReal (A * M₁ i * M₂ j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simpa [V, A, M₁, M₂] using hpairwise i j
    _ = V *
        (∑ i : Fin J, ∑ j : Fin J,
          ENNReal.ofReal (A * M₁ i * M₂ j)) := by
      simp_rw [Finset.mul_sum]
    _ = V * ENNReal.ofReal
        (A * (∑ i : Fin J, M₁ i) * (∑ j : Fin J, M₂ j)) := by
      rw [hsumOfReal, hfactor]
    _ = _ := by rfl

/-- **Bourgain (1.25), discrete recurrence-ready exponent form.**

The entire separated block-pair family has physical volume `D⁸`, planar
subpower loss `H^ε`, and exactly the sharp refinement cost `H⁴` against
the two global coefficient sixth masses. -/
theorem bourgainSectionOneBlockPairFamilyMoment_refinement_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J H : ℕ) (_hJ : 0 < J) (_hH : 0 < H)
        (_hscale :
          6 * bourgainSectionOneTaylorConstant *
              (H : ℝ) ^ (2 : ℕ) ≤ J)
        {q : ℝ} (_hq : 0 < q) (_hq1 : q ≤ 1 / 2)
        (c₁ c₂ : Fin (J * H) → ℂ),
        bourgainSectionOneBlockPairFamilyMoment J H q c₁ c₂ ≤
          ENNReal.ofReal
              ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
                bourgainSectionOneBlockDenominator J H ^ (8 : ℕ)) *
            ENNReal.ofReal
              (C * (H : ℝ) ^ ε * (H : ℝ) ^ (4 : ℕ) *
                (∑ n : Fin (J * H), ‖c₁ n‖ ^ (6 : ℕ)) *
                (∑ n : Fin (J * H), ‖c₂ n‖ ^ (6 : ℕ))) := by
  obtain ⟨C, hC, hfamily⟩ :=
    bourgainSectionOneBlockPairFamilyMoment_subpower hε
  refine ⟨C, hC, ?_⟩
  intro J H hJ hH hscale q hq hq1 c₁ c₂
  let V : ENNReal :=
    ENNReal.ofReal
      ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
        bourgainSectionOneBlockDenominator J H ^ (8 : ℕ))
  let M₁ : ℝ :=
    ∑ i : Fin J,
      (∑ n : Fin H,
        ‖bourgainGenericCurveBlockCoefficients J H c₁ i n‖ ^
          (2 : ℕ)) ^ (3 : ℕ)
  let M₂ : ℝ :=
    ∑ j : Fin J,
      (∑ n : Fin H,
        ‖bourgainGenericCurveBlockCoefficients J H c₂ j n‖ ^
          (2 : ℕ)) ^ (3 : ℕ)
  let S₁ : ℝ :=
    ∑ n : Fin (J * H), ‖c₁ n‖ ^ (6 : ℕ)
  let S₂ : ℝ :=
    ∑ n : Fin (J * H), ‖c₂ n‖ ^ (6 : ℕ)
  have hmass : M₁ * M₂ ≤ (H : ℝ) ^ (4 : ℕ) * S₁ * S₂ := by
    simpa [M₁, M₂, S₁, S₂] using
      mul_sum_blockMassCube_le_card_four_sum_norm_pow_six
        J H c₁ c₂
  have hfactor0 : 0 ≤ C * (H : ℝ) ^ ε := by positivity
  have hreal :
      C * (H : ℝ) ^ ε * M₁ * M₂ ≤
        C * (H : ℝ) ^ ε * (H : ℝ) ^ (4 : ℕ) * S₁ * S₂ := by
    calc
      C * (H : ℝ) ^ ε * M₁ * M₂ =
          (C * (H : ℝ) ^ ε) * (M₁ * M₂) := by ring
      _ ≤ (C * (H : ℝ) ^ ε) *
          ((H : ℝ) ^ (4 : ℕ) * S₁ * S₂) :=
        mul_le_mul_of_nonneg_left hmass hfactor0
      _ = _ := by ring
  have hENN := ENNReal.ofReal_le_ofReal hreal
  have hraw := hfamily J H hJ hH hscale hq hq1 c₁ c₂
  calc
    bourgainSectionOneBlockPairFamilyMoment J H q c₁ c₂ ≤
        V * ENNReal.ofReal
          (C * (H : ℝ) ^ ε * M₁ * M₂) := by
      simpa [V, M₁, M₂] using hraw
    _ ≤ V * ENNReal.ofReal
        (C * (H : ℝ) ^ ε * (H : ℝ) ^ (4 : ℕ) * S₁ * S₂) := by
      simpa [mul_comm] using mul_le_mul_right hENN V
    _ = _ := by rfl

end

end RHTower
