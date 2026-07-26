/-
# Uniform coordinate distortion for Bourgain's normalized curve

The first two normalized jets contain apparent negative powers of `q`.
Factoring the affine square-root difference cancels them exactly.  This
module proves uniform jet-entry bounds and combines them with the determinant
lower bound and the `Fin 4` adjugate estimate.  On two arcs separated by
`1/4`, the inverse osculating coordinate map has operator norm at most
`1048576000`, uniformly for `0 < q ≤ 1/2`.
-/
import GaloisForLFunctions.RHTower.BourgainFinFourInverseBound

namespace RHTower

noncomputable section

theorem iteratedDeriv_bourgainNormalizedCubicRemainder_one_cancelled
    {q t : ℝ} (hq : 0 < q) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    iteratedDeriv 1 (bourgainNormalizedCubicRemainder q) t =
      12 * t ^ (2 : ℕ) /
        ((1 + q * t) ^ (1 / 2 : ℝ) + 1) ^ (2 : ℕ) := by
  have hqt : 0 ≤ q * t := mul_nonneg hq.le ht.1
  have hbase : 0 < 1 + q * t := by linarith
  rw [iteratedDeriv_bourgainNormalizedCubicRemainder_one hq.ne' hbase]
  let u : ℝ := (1 + q * t) ^ (1 / 2 : ℝ)
  have hu0 : 0 < u := Real.rpow_pos_of_pos hbase _
  have hu2 : u ^ (2 : ℕ) = 1 + q * t := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    norm_num
  have hprod : (u - 1) * (u + 1) = q * t := by nlinarith
  have hpow := congrArg (fun x : ℝ => x ^ (2 : ℕ)) hprod
  change ((u - 1) * (u + 1)) ^ (2 : ℕ) =
    (q * t) ^ (2 : ℕ) at hpow
  rw [mul_pow, mul_pow] at hpow
  change
    12 / q ^ (2 : ℕ) * (u - 1) ^ (2 : ℕ) =
      12 * t ^ (2 : ℕ) / (u + 1) ^ (2 : ℕ)
  field_simp [hq.ne', ne_of_gt (by positivity : 0 < u + 1)]
  nlinarith

theorem iteratedDeriv_bourgainNormalizedCubicRemainder_two_cancelled
    {q t : ℝ} (hq : 0 < q) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    iteratedDeriv 2 (bourgainNormalizedCubicRemainder q) t =
      12 * t /
        ((1 + q * t) ^ (1 / 2 : ℝ) *
          ((1 + q * t) ^ (1 / 2 : ℝ) + 1)) := by
  have hqt : 0 ≤ q * t := mul_nonneg hq.le ht.1
  have hbase : 0 < 1 + q * t := by linarith
  rw [iteratedDeriv_bourgainNormalizedCubicRemainder_two hq.ne' hbase]
  let u : ℝ := (1 + q * t) ^ (1 / 2 : ℝ)
  have hu0 : 0 < u := Real.rpow_pos_of_pos hbase _
  have hu2 : u ^ (2 : ℕ) = 1 + q * t := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    norm_num
  have hprod : (u - 1) * (u + 1) = q * t := by nlinarith
  have hneg : (1 + q * t) ^ (-(1 / 2 : ℝ)) = u⁻¹ := by
    rw [Real.rpow_neg hbase.le]
  rw [hneg]
  change 12 / q * (1 - u⁻¹) = 12 * t / (u * (u + 1))
  field_simp [hq.ne', hu0.ne', ne_of_gt (by positivity : 0 < u + 1)]
  nlinarith

theorem iteratedDeriv_bourgainNormalizedQuarticRemainder_one_cancelled
    {q t : ℝ} (hq : 0 < q) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    iteratedDeriv 1 (bourgainNormalizedQuarticRemainder q) t =
      32 * t ^ (3 : ℕ) /
        ((1 + q * t) ^ (1 / 2 : ℝ) *
          ((1 + q * t) ^ (1 / 2 : ℝ) + 1) ^ (3 : ℕ)) := by
  have hqt : 0 ≤ q * t := mul_nonneg hq.le ht.1
  have hbase : 0 < 1 + q * t := by linarith
  rw [iteratedDeriv_bourgainNormalizedQuarticRemainder_one hq.ne' hbase]
  let u : ℝ := (1 + q * t) ^ (1 / 2 : ℝ)
  have hu0 : 0 < u := Real.rpow_pos_of_pos hbase _
  have hu2 : u ^ (2 : ℕ) = 1 + q * t := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    norm_num
  have hprod : (u - 1) * (u + 1) = q * t := by nlinarith
  have hpow := congrArg (fun x : ℝ => x ^ (3 : ℕ)) hprod
  change ((u - 1) * (u + 1)) ^ (3 : ℕ) =
    (q * t) ^ (3 : ℕ) at hpow
  rw [mul_pow, mul_pow] at hpow
  have hneg : (1 + q * t) ^ (-(1 / 2 : ℝ)) = u⁻¹ := by
    rw [Real.rpow_neg hbase.le]
  rw [show (1 + q * t) ^ (1 / 2 : ℝ) = u by rfl,
    hneg, ← hu2]
  change
    32 / q ^ (3 : ℕ) * (u ^ 2 - 3 * u + 3 - u⁻¹) =
      32 * t ^ (3 : ℕ) / (u * (u + 1) ^ (3 : ℕ))
  field_simp [hq.ne', hu0.ne', ne_of_gt (by positivity : 0 < u + 1)]
  nlinarith

theorem iteratedDeriv_bourgainNormalizedQuarticRemainder_two_cancelled
    {q t : ℝ} (hq : 0 < q) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    iteratedDeriv 2 (bourgainNormalizedQuarticRemainder q) t =
      16 * t ^ (2 : ℕ) *
          (2 * (1 + q * t) ^ (1 / 2 : ℝ) + 1) /
        (((1 + q * t) ^ (1 / 2 : ℝ)) ^ (3 : ℕ) *
          ((1 + q * t) ^ (1 / 2 : ℝ) + 1) ^ (2 : ℕ)) := by
  have hqt : 0 ≤ q * t := mul_nonneg hq.le ht.1
  have hbase : 0 < 1 + q * t := by linarith
  rw [iteratedDeriv_bourgainNormalizedQuarticRemainder_two hq.ne' hbase]
  let u : ℝ := (1 + q * t) ^ (1 / 2 : ℝ)
  have hu0 : 0 < u := Real.rpow_pos_of_pos hbase _
  have hu2 : u ^ (2 : ℕ) = 1 + q * t := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    norm_num
  have hprod : (u - 1) * (u + 1) = q * t := by nlinarith
  have hpow := congrArg (fun x : ℝ => x ^ (2 : ℕ)) hprod
  change ((u - 1) * (u + 1)) ^ (2 : ℕ) =
    (q * t) ^ (2 : ℕ) at hpow
  rw [mul_pow, mul_pow] at hpow
  have hneg : (1 + q * t) ^ (-(1 / 2 : ℝ)) = u⁻¹ := by
    rw [Real.rpow_neg hbase.le]
  have hneg3 : (1 + q * t) ^ (-(3 / 2 : ℝ)) = u⁻¹ ^ (3 : ℕ) := by
    rw [show (-(3 / 2 : ℝ)) = -(1 / 2 : ℝ) * 3 by ring,
      Real.rpow_mul hbase.le, Real.rpow_neg hbase.le]
    simp only [u]
    exact Real.rpow_natCast _ 3
  rw [hneg, hneg3]
  change
    16 / q ^ (2 : ℕ) * (2 - 3 * u⁻¹ + u⁻¹ ^ (3 : ℕ)) =
      16 * t ^ (2 : ℕ) * (2 * u + 1) /
        (u ^ (3 : ℕ) * (u + 1) ^ (2 : ℕ))
  field_simp [hq.ne', hu0.ne', ne_of_gt (by positivity : 0 < u + 1)]
  nlinarith

theorem abs_iteratedDeriv_bourgainNormalizedCubicRemainder_one_le_three
    {q t : ℝ} (hq : 0 < q) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |iteratedDeriv 1 (bourgainNormalizedCubicRemainder q) t| ≤ 3 := by
  rw [iteratedDeriv_bourgainNormalizedCubicRemainder_one_cancelled hq ht]
  let u : ℝ := (1 + q * t) ^ (1 / 2 : ℝ)
  have hqt : 0 ≤ q * t := mul_nonneg hq.le ht.1
  have hbase : 0 < 1 + q * t := by linarith
  have hu0 : 0 < u := Real.rpow_pos_of_pos hbase _
  have hu2 : u ^ (2 : ℕ) = 1 + q * t := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    norm_num
  have hu1 : 1 ≤ u := by nlinarith [sq_nonneg (u - 1)]
  have ht2 : t ^ (2 : ℕ) ≤ 1 := by
    have hpow := pow_le_pow_left₀ ht.1 ht.2 2
    norm_num at hpow ⊢
    exact hpow
  have hden0 : 0 < (u + 1) ^ (2 : ℕ) := by positivity
  have hden : 4 ≤ (u + 1) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (u - 1)]
  rw [abs_of_nonneg
    (div_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg ht.1 2)) hden0.le)]
  rw [div_le_iff₀ hden0]
  nlinarith [ht.2]

theorem abs_iteratedDeriv_bourgainNormalizedCubicRemainder_two_le_six
    {q t : ℝ} (hq : 0 < q) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |iteratedDeriv 2 (bourgainNormalizedCubicRemainder q) t| ≤ 6 := by
  rw [iteratedDeriv_bourgainNormalizedCubicRemainder_two_cancelled hq ht]
  let u : ℝ := (1 + q * t) ^ (1 / 2 : ℝ)
  have hqt : 0 ≤ q * t := mul_nonneg hq.le ht.1
  have hbase : 0 < 1 + q * t := by linarith
  have hu0 : 0 < u := Real.rpow_pos_of_pos hbase _
  have hu2 : u ^ (2 : ℕ) = 1 + q * t := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    norm_num
  have hu1 : 1 ≤ u := by nlinarith [sq_nonneg (u - 1)]
  have hden0 : 0 < u * (u + 1) := by positivity
  have hden : 2 ≤ u * (u + 1) := by nlinarith [sq_nonneg (u - 1)]
  rw [abs_of_nonneg
    (div_nonneg (mul_nonneg (by norm_num) ht.1) hden0.le)]
  rw [div_le_iff₀ hden0]
  nlinarith [ht.2]

theorem abs_iteratedDeriv_bourgainNormalizedQuarticRemainder_one_le_four
    {q t : ℝ} (hq : 0 < q) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |iteratedDeriv 1 (bourgainNormalizedQuarticRemainder q) t| ≤ 4 := by
  rw [iteratedDeriv_bourgainNormalizedQuarticRemainder_one_cancelled hq ht]
  let u : ℝ := (1 + q * t) ^ (1 / 2 : ℝ)
  have hqt : 0 ≤ q * t := mul_nonneg hq.le ht.1
  have hbase : 0 < 1 + q * t := by linarith
  have hu0 : 0 < u := Real.rpow_pos_of_pos hbase _
  have hu2 : u ^ (2 : ℕ) = 1 + q * t := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    norm_num
  have hu1 : 1 ≤ u := by nlinarith [sq_nonneg (u - 1)]
  have ht3 : t ^ (3 : ℕ) ≤ 1 := by
    have hpow := pow_le_pow_left₀ ht.1 ht.2 3
    norm_num at hpow ⊢
    exact hpow
  have hplus3 : 8 ≤ (u + 1) ^ (3 : ℕ) := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (by linarith : (2 : ℝ) ≤ u + 1) 3
    norm_num at hpow ⊢
    exact hpow
  have hden0 : 0 < u * (u + 1) ^ (3 : ℕ) := by positivity
  have hden : 8 ≤ u * (u + 1) ^ (3 : ℕ) := by
    calc
      (8 : ℝ) = 1 * 8 := by norm_num
      _ ≤ u * (u + 1) ^ (3 : ℕ) :=
        mul_le_mul hu1 hplus3 (by norm_num) hu0.le
  rw [abs_of_nonneg
    (div_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg ht.1 3)) hden0.le)]
  rw [div_le_iff₀ hden0]
  nlinarith

theorem abs_iteratedDeriv_bourgainNormalizedQuarticRemainder_two_le_twenty
    {q t : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 2)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |iteratedDeriv 2 (bourgainNormalizedQuarticRemainder q) t| ≤ 20 := by
  rw [iteratedDeriv_bourgainNormalizedQuarticRemainder_two_cancelled hq ht]
  let u : ℝ := (1 + q * t) ^ (1 / 2 : ℝ)
  have hqt : 0 ≤ q * t := mul_nonneg hq.le ht.1
  have hqt1 : q * t ≤ 1 / 2 := by
    calc
      q * t ≤ q * 1 := mul_le_mul_of_nonneg_left ht.2 hq.le
      _ ≤ 1 / 2 := by simpa using hq1
  have hbase : 0 < 1 + q * t := by linarith
  have hu0 : 0 < u := Real.rpow_pos_of_pos hbase _
  have hu2 : u ^ (2 : ℕ) = 1 + q * t := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    norm_num
  have hu1 : 1 ≤ u := by nlinarith [sq_nonneg (u - 1)]
  have hu2' : u ≤ 2 := by nlinarith [sq_nonneg (u - 2)]
  have ht2 : t ^ (2 : ℕ) ≤ 1 := by
    have hpow := pow_le_pow_left₀ ht.1 ht.2 2
    norm_num at hpow ⊢
    exact hpow
  have hu3 : 1 ≤ u ^ (3 : ℕ) := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hu1 3
    norm_num at hpow ⊢
    exact hpow
  have hplus2 : 4 ≤ (u + 1) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (u - 1)]
  have hden0 : 0 < u ^ (3 : ℕ) * (u + 1) ^ (2 : ℕ) := by
    positivity
  have hden : 4 ≤ u ^ (3 : ℕ) * (u + 1) ^ (2 : ℕ) := by
    calc
      (4 : ℝ) = 1 * 4 := by norm_num
      _ ≤ u ^ (3 : ℕ) * (u + 1) ^ (2 : ℕ) :=
        mul_le_mul hu3 hplus2 (by norm_num) (by positivity)
  have hnum :
      16 * t ^ (2 : ℕ) * (2 * u + 1) ≤ 80 := by
    have hfactor : 2 * u + 1 ≤ 5 := by linarith
    calc
      16 * t ^ (2 : ℕ) * (2 * u + 1) ≤
          16 * 1 * 5 := by
        gcongr
      _ = 80 := by norm_num
  rw [abs_of_nonneg
    (div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg ht.1 2))
        (by positivity)) hden0.le)]
  rw [div_le_iff₀ hden0]
  nlinarith

/-- Every entry of the normalized two-base jet matrix is bounded by ten on
the full parameter box. -/
theorem abs_bourgainNormalizedPhaseCoordinateMatrix_apply_le_ten
    {q a b : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 2)
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (i j : Fin 4) :
    |bourgainGenericPhaseCoordinateMatrix
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q) a b i j| ≤ 10 := by
  have hC1a :=
    abs_iteratedDeriv_bourgainNormalizedCubicRemainder_one_le_three hq ha
  have hC1b :=
    abs_iteratedDeriv_bourgainNormalizedCubicRemainder_one_le_three hq hb
  have hC2a :=
    abs_iteratedDeriv_bourgainNormalizedCubicRemainder_two_le_six hq ha
  have hC2b :=
    abs_iteratedDeriv_bourgainNormalizedCubicRemainder_two_le_six hq hb
  have hQ1a :=
    abs_iteratedDeriv_bourgainNormalizedQuarticRemainder_one_le_four hq ha
  have hQ1b :=
    abs_iteratedDeriv_bourgainNormalizedQuarticRemainder_one_le_four hq hb
  have hQ2a :=
    abs_iteratedDeriv_bourgainNormalizedQuarticRemainder_two_le_twenty
      hq hq1 ha
  have hQ2b :=
    abs_iteratedDeriv_bourgainNormalizedQuarticRemainder_two_le_twenty
      hq hq1 hb
  fin_cases i
  · fin_cases j
    · norm_num [bourgainGenericPhaseCoordinateMatrix]
    · simp [bourgainGenericPhaseCoordinateMatrix, abs_of_nonneg ha.1]
      nlinarith [ha.2]
    · simpa [bourgainGenericPhaseCoordinateMatrix] using hC1a.trans (by norm_num)
    · simpa [bourgainGenericPhaseCoordinateMatrix] using hQ1a.trans (by norm_num)
  · fin_cases j
    · norm_num [bourgainGenericPhaseCoordinateMatrix]
    · norm_num [bourgainGenericPhaseCoordinateMatrix]
    · simp [bourgainGenericPhaseCoordinateMatrix, abs_div]
      nlinarith
    · simp [bourgainGenericPhaseCoordinateMatrix, abs_div]
      nlinarith
  · fin_cases j
    · norm_num [bourgainGenericPhaseCoordinateMatrix]
    · simp [bourgainGenericPhaseCoordinateMatrix, abs_of_nonneg hb.1]
      nlinarith [hb.2]
    · simpa [bourgainGenericPhaseCoordinateMatrix] using hC1b.trans (by norm_num)
    · simpa [bourgainGenericPhaseCoordinateMatrix] using hQ1b.trans (by norm_num)
  · fin_cases j
    · norm_num [bourgainGenericPhaseCoordinateMatrix]
    · norm_num [bourgainGenericPhaseCoordinateMatrix]
    · simp [bourgainGenericPhaseCoordinateMatrix, abs_div]
      nlinarith
    · simp [bourgainGenericPhaseCoordinateMatrix, abs_div]
      nlinarith

/-- Uniform inverse operator bound for separated normalized osculating
coordinates. -/
theorem opNorm_bourgainNormalizedPhaseCoordinate_inverse_le
    {q a b : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 2)
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hab : 1 / 4 ≤ b - a) :
    let hunit :=
      isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
        hq hq1 ha hb hab
    ‖((bourgainGenericPhaseCoordinateContinuousLinearEquiv
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q) a b hunit).symm :
          BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ ≤
      1048576000 := by
  dsimp only
  let A :=
    bourgainGenericPhaseCoordinateMatrix
      (bourgainNormalizedCubicRemainder q)
      (bourgainNormalizedQuarticRemainder q) a b
  let hunit :=
    isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
      hq hq1 ha hb hab
  let E :=
    bourgainGenericPhaseCoordinateContinuousLinearEquiv
      (bourgainNormalizedCubicRemainder q)
      (bourgainNormalizedQuarticRemainder q) a b hunit
  have hentry : ∀ i j, |A i j| ≤ 10 := by
    intro i j
    exact abs_bourgainNormalizedPhaseCoordinateMatrix_apply_le_ten
      hq hq1 ha hb i j
  have hdet :
      (3 / 131072 : ℝ) ≤ |A.det| := by
    have hraw :=
      det_bourgainGenericPhaseCoordinateMatrix_normalized_ge
        hq hq1 ha hb hab
    have hpos : 0 < A.det :=
      lt_of_lt_of_le (by norm_num) hraw
    rw [abs_of_pos hpos]
    exact hraw
  have hpoint (x : BourgainPhaseSpace) :
      ‖E.symm x‖ ≤ (24 * 10 ^ (3 : ℕ) / (3 / 131072 : ℝ)) * ‖x‖ := by
    have heq : E.symm x = A⁻¹.mulVec x := by
      apply E.injective
      rw [E.apply_symm_apply]
      symm
      change A.mulVec (A⁻¹.mulVec x) = x
      rw [Matrix.mulVec_mulVec]
      rw [Matrix.mul_nonsing_inv]
      · exact Matrix.one_mulVec x
      · exact (Matrix.isUnit_iff_isUnit_det A).mp hunit
    rw [heq]
    exact norm_nonsing_inv_mulVec_le
      (by norm_num) (by norm_num) hentry hdet x
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hx := hpoint x
  norm_num at hx ⊢
  exact hx

end

end RHTower
