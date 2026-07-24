import GaloisForLFunctions.RHTower.CCMBlockFockCommonCarrierSquareObstruction

/-!
# Square saturation and cubic escape for the CCM block--Fock carrier

The odd block--Fock resolvent has sharply different common-carrier behavior under the first two
nontrivial power dilations.  At `q,q²`, the natural carrier is indefinite and the canonical
von-Mangoldt square innovations repair it only to rank one.  At `q,q³`, the same natural
normalizations already form a positive-definite carrier, with an explicit strictly positive
determinant.

Cubing, like squaring, preserves the von Mangoldt mark. This is a local source-marked
normalization audit, not a new positivity mechanism: underlying inequality is specialization of
general nonnegative graded-partition multiplicative log-convexity
`HilbertMetric.gradedPartition_mul_sq_le`. It is not an RH predecessor. Cubing remains inside one
prime-power tower and supplies neither exponent-one prime atoms, hard aperture transport, nor
first-clock sine sign. Everything is unconditional; no RH assertion is made.
-/

open scoped Matrix

namespace RHTower

noncomputable section

/-- Universal radial carrier at dilation exponent three. -/
def ccmBlockFockCubeCarrierMatrix (r : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![oddBlockFockRadialSum r, oddBlockFockRadialSum (r ^ 2);
     oddBlockFockRadialSum (r ^ 2), oddBlockFockRadialSum (r ^ 3)]

/-- Exact cubic determinant: its numerator is the surviving four-grade radial innovation. -/
theorem ccmBlockFockCubeCarrierMatrix_det
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (ccmBlockFockCubeCarrierMatrix r).det =
      r ^ 8 * (1 - r ^ 4) /
        ((1 - r ^ 8) ^ 2 * (1 - r ^ 12)) := by
  have hr2pos : 0 < r ^ 2 := pow_pos hr0 2
  have hr3pos : 0 < r ^ 3 := pow_pos hr0 3
  have hr2lt : r ^ 2 < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have hr3lt : r ^ 3 < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  rw [ccmBlockFockCubeCarrierMatrix, Matrix.det_fin_two]
  rw [oddBlockFockRadialSum_eq hr0.le hr1,
    oddBlockFockRadialSum_eq hr2pos.le hr2lt,
    oddBlockFockRadialSum_eq hr3pos.le hr3lt]
  norm_num [pow_mul]
  have h4 : r ^ 4 < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have h8 : r ^ 8 < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have h12 : r ^ 12 < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have hd4 : 1 - r ^ 4 ≠ 0 := ne_of_gt (sub_pos.mpr h4)
  have hd8 : 1 - r ^ 8 ≠ 0 := ne_of_gt (sub_pos.mpr h8)
  have hd12 : 1 - r ^ 12 ≠ 0 := ne_of_gt (sub_pos.mpr h12)
  rw [show (r ^ 2) ^ 4 = r ^ 8 by ring,
    show (r ^ 3) ^ 4 = r ^ 12 by ring]
  field_simp [hd4, hd8, hd12]
  ring

theorem ccmBlockFockCubeCarrierMatrix_det_pos
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < (ccmBlockFockCubeCarrierMatrix r).det := by
  rw [ccmBlockFockCubeCarrierMatrix_det hr0 hr1]
  have h4 : r ^ 4 < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have h8 : r ^ 8 < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have h12 : r ^ 12 < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  positivity

theorem ccmBlockFockCubeCarrierMatrix_posSemidef
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (ccmBlockFockCubeCarrierMatrix r).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ccmBlockFockCubeCarrierMatrix]
  · intro x
    have ha : 0 < oddBlockFockRadialSum r := by
      rw [oddBlockFockRadialSum_eq hr0.le hr1]
      exact div_pos hr0
        (sub_pos.mpr (pow_lt_one₀ hr0.le hr1 (by omega)))
    have hdet := ccmBlockFockCubeCarrierMatrix_det_pos hr0 hr1
    simp [ccmBlockFockCubeCarrierMatrix, Matrix.det_fin_two] at hdet ⊢
    have hsquare := sq_nonneg
      (oddBlockFockRadialSum r * Matrix.vecHead x +
        oddBlockFockRadialSum (r ^ 2) *
          Matrix.vecHead (Matrix.vecTail x))
    have hdetTerm := mul_nonneg (sub_nonneg.mpr hdet.le)
      (sq_nonneg (Matrix.vecHead (Matrix.vecTail x)))
    nlinarith

/-- Cubic dilation escapes local square threshold: natural radial carrier has full rank. -/
theorem ccmBlockFockCubeCarrierMatrix_posDef
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (ccmBlockFockCubeCarrierMatrix r).PosDef := by
  apply
    (ccmBlockFockCubeCarrierMatrix_posSemidef hr0 hr1).posDef_iff_det_ne_zero.mpr
  exact ne_of_gt (ccmBlockFockCubeCarrierMatrix_det_pos hr0 hr1)

/-- Cubing a block scale cubes its critical radial coordinate. -/
theorem ccmNaturalBlockScaleRadius_cube (q : ℕ) :
    ccmNaturalBlockScaleRadius (q ^ 3) =
      ccmNaturalBlockScaleRadius q ^ 3 := by
  rw [ccmNaturalBlockScaleRadius, ccmNaturalBlockScaleRadius, Nat.cast_pow]
  exact (Real.rpow_pow_comm (Nat.cast_nonneg q) (-1 / 2 : ℝ) 3).symm

/-- The aligned seed overlap at `q,q³` is the square of the critical radius. -/
theorem criticalBlockSeedGram_cube
    {q : ℕ} (hq : 2 ≤ q) :
    criticalBlockSeedGram q (q ^ 3) =
      ccmNaturalBlockScaleRadius q ^ 2 := by
  have hqposN : 0 < q := by omega
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqposN
  have hqle : q ≤ q ^ 3 := by
    calc
      q ≤ q ^ 2 := by
        rw [pow_two]
        simpa using Nat.mul_le_mul_left q (show 1 ≤ q by omega)
      _ ≤ q ^ 3 := by
        rw [pow_succ]
        exact Nat.le_mul_of_pos_right _ hqposN
  have hqleR : (q : ℝ) ≤ (q ^ 3 : ℕ) := by exact_mod_cast hqle
  rw [criticalBlockSeedGram_eq, min_eq_left hqleR,
    ccmNaturalBlockScaleRadius, Nat.cast_pow]
  rw [← Real.rpow_pow_comm hqpos.le]
  have hr_sq :
      ((q : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 = (q : ℝ)⁻¹ := by
    rw [← Real.rpow_mul_natCast hqpos.le]
    norm_num [Real.rpow_neg_one]
  have hmul :
      (q : ℝ) * ((q : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 = 1 := by
    rw [hr_sq]
    exact mul_inv_cancel₀ hqpos.ne'
  calc
    (q : ℝ) * (q : ℝ) ^ (-1 / 2 : ℝ) *
        ((q : ℝ) ^ (-1 / 2 : ℝ)) ^ 3 =
      ((q : ℝ) * ((q : ℝ) ^ (-1 / 2 : ℝ)) ^ 2) *
        ((q : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 := by ring
    _ = ((q : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 := by rw [hmul, one_mul]

/-- Literal common carrier using the natural radial diagonals at `q,q³`. -/
def ccmBlockFockCommonCarrierCubeMatrix (q : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![ccmNaturalBlockRadialEnergy q,
      oddBlockFockRadialSum (criticalBlockSeedGram q (q ^ 3));
     oddBlockFockRadialSum (criticalBlockSeedGram q (q ^ 3)),
      ccmNaturalBlockRadialEnergy (q ^ 3)]

theorem ccmBlockFockCommonCarrierCubeMatrix_eq
    {q : ℕ} (hq : 2 ≤ q) :
    ccmBlockFockCommonCarrierCubeMatrix q =
      ccmBlockFockCubeCarrierMatrix (ccmNaturalBlockScaleRadius q) := by
  rw [ccmBlockFockCommonCarrierCubeMatrix,
    ccmBlockFockCubeCarrierMatrix,
    criticalBlockSeedGram_cube hq,
    ccmNaturalBlockRadialEnergy,
    ccmNaturalBlockRadialEnergy,
    ccmNaturalBlockScaleRadius_cube]

/-- Every natural integer cubic pair is a strict positive common carrier. -/
theorem ccmBlockFockCommonCarrierCubeMatrix_posDef
    {q : ℕ} (hq : 2 ≤ q) :
    (ccmBlockFockCommonCarrierCubeMatrix q).PosDef := by
  have hqoneN : 1 < q := by omega
  have hqone : (1 : ℝ) < q := by exact_mod_cast hqoneN
  have hr0 : 0 < ccmNaturalBlockScaleRadius q :=
    Real.rpow_pos_of_pos (by positivity) _
  have hr1 : ccmNaturalBlockScaleRadius q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hqone (by norm_num)
  rw [ccmBlockFockCommonCarrierCubeMatrix_eq hq]
  exact ccmBlockFockCubeCarrierMatrix_posDef hr0 hr1

/-- Cubing preserves the von Mangoldt mark, just as squaring does. -/
theorem vonMangoldt_cube (q : ℕ) :
    ArithmeticFunction.vonMangoldt (q ^ 3) =
      ArithmeticFunction.vonMangoldt q := by
  simpa using
    ArithmeticFunction.vonMangoldt_apply_pow (n := q) (by omega : 3 ≠ 0)

/-- **Local source-marked square/cube capacity audit.** With same nonzero von Mangoldt mark,
canonical square innovations reach exactly rank-one PSD carrier, whereas natural cubic carrier is
positive definite. This does not assemble complete first-clock source. -/
theorem ccmBlockFock_sourceMarked_squareSaturation_cubeEscape
    {q : ℕ} (hq : 2 ≤ q)
    (hΛ : ArithmeticFunction.vonMangoldt q ≠ 0) :
    ArithmeticFunction.vonMangoldt (q ^ 3) =
        ArithmeticFunction.vonMangoldt q ∧
      (ccmBlockFockCommonCarrierSquareCountertermMatrix q
        ((ccmCriticalMellinSquareInnovation q +
            ccmBlockFockTailSquareInnovation q) /
          ArithmeticFunction.vonMangoldt q)).PosSemidef ∧
      (ccmBlockFockCommonCarrierSquareCountertermMatrix q
        ((ccmCriticalMellinSquareInnovation q +
            ccmBlockFockTailSquareInnovation q) /
          ArithmeticFunction.vonMangoldt q)).det = 0 ∧
      (ccmBlockFockCommonCarrierCubeMatrix q).PosDef := by
  refine ⟨vonMangoldt_cube q, ?_, ?_,
    ccmBlockFockCommonCarrierCubeMatrix_posDef hq⟩
  · rw [ccmBlockFock_normalizedSquareInnovations_eq_capacityDebt hΛ]
    exact ccmBlockFockCommonCarrierSquare_minimalRepair_posSemidef hq
  · exact ccmBlockFock_normalizedSquareInnovations_repair_det hq hΛ

end

end RHTower
