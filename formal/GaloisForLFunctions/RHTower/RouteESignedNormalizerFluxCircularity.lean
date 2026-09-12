import GaloisForLFunctions.RHTower.RouteEApproximateTransposeDivergence

/-!
# Route E signed normalizer-flux circularity

For arbitrary vertex weights, sign-reversing row transport identifies twice the signed source
with the signed incoming-weight defect.  On a symmetric raw incidence, this defect splits exactly
into signed reciprocal-row-mass flux and a signed co-moving weight term.  Constant weights kill
the co-moving term, leaving the original signed imbalance exactly equal to half the signed flux.

Thus retaining signs before taking absolute values is a valid exact interface, but naming the
resulting normalizer flux does not provide an independent cancellation estimate.  No arithmetic
estimate, Möbius cancellation premise, column-load premise, or RH premise is used.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Incoming transported vertex weight at one target. -/
def routeEWeightedIncomingMass
    (P : ι → ι → ℝ) (w : ι → ℝ) (j : ι) : ℝ :=
  ∑ i, w i * P i j

/-- Weighted parity-column identity before specializing the transport to a row-normalized
symmetric raw incidence. -/
theorem routeE_two_mul_signedWeightedSum_eq_signedWeightedIncomingDefect
    (P : ι → ι → ℝ) (sign weight : ι → ℝ)
    (hrow : ∀ i, routeERowMass P i = 1)
    (hflip : ∀ i j, P i j ≠ 0 → sign i + sign j = 0) :
    2 * ∑ i, sign i * weight i =
      ∑ j, sign j * (weight j - routeEWeightedIncomingMass P weight j) := by
  have hterm (i j : ι) :
      sign i * weight i * P i j = -sign j * weight i * P i j := by
    by_cases hzero : P i j = 0
    · simp [hzero]
    · have hsign : sign i = -sign j := by
        linarith [hflip i j hzero]
      rw [hsign]
  have htransport :
      (∑ i, sign i * weight i) =
        -∑ j, sign j * routeEWeightedIncomingMass P weight j := by
    calc
      (∑ i, sign i * weight i) =
          ∑ i, (sign i * weight i) * ∑ j, P i j := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [← routeERowMass, hrow i]
            ring
      _ = ∑ i, ∑ j, sign i * weight i * P i j := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, sign i * weight i * P i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -sign j * weight i * P i j := by
            apply Finset.sum_congr rfl
            intro j _hj
            apply Finset.sum_congr rfl
            intro i _hi
            exact hterm i j
      _ = -∑ j, sign j * routeEWeightedIncomingMass P weight j := by
            unfold routeEWeightedIncomingMass
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro j _hj
            calc
              (∑ i, -sign j * weight i * P i j) =
                  ∑ i, -(sign j * weight i * P i j) := by
                    apply Finset.sum_congr rfl
                    intro i _hi
                    ring
              _ = -∑ i, sign j * weight i * P i j := by
                    rw [Finset.sum_neg_distrib]
              _ = -(sign j * ∑ i, weight i * P i j) := by
                    congr 1
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro i _hi
                    ring
  have hright :
      (∑ j, sign j * (weight j - routeEWeightedIncomingMass P weight j)) =
        (∑ i, sign i * weight i) -
          ∑ j, sign j * routeEWeightedIncomingMass P weight j := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hright]
  linarith

/-- A symmetric row-normalized weighted incoming defect is exactly weighted normalizer flux plus
the change in vertex weight along transported edges. -/
theorem routeE_weightedIncomingDefect_eq_weightedNormalizerFlux_add_coMoving
    (U : ι → ι → ℝ) (weight : ι → ℝ)
    (hsym : ∀ i j, U i j = U j i)
    (hrow : ∀ i, routeERowMass U i ≠ 0) (i : ι) :
    weight i - routeEWeightedIncomingMass (routeERowNormalizedKernel U) weight i =
      weight i * routeESymmetricNormalizerFlux U i +
        ∑ j, U i j / routeERowMass U j * (weight i - weight j) := by
  have hunit : (∑ j, U i j / routeERowMass U i) = 1 := by
    exact routeE_rowMass_rowNormalizedKernel_eq_one U i (hrow i)
  unfold routeEWeightedIncomingMass routeERowNormalizedKernel
    routeESymmetricNormalizerFlux
  simp_rw [hsym _ i]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    weight i - ∑ x, weight x * (U i x / routeERowMass U x) =
        weight i * 1 - ∑ x, weight x * (U i x / routeERowMass U x) := by ring
    _ = ∑ x, weight i * (U i x / routeERowMass U i) -
          ∑ x, weight x * (U i x / routeERowMass U x) := by
            congr 1
            rw [← Finset.mul_sum, hunit]
    _ = ∑ x,
          (weight i * (U i x *
              (1 / routeERowMass U i - 1 / routeERowMass U x)) +
            U i x / routeERowMass U x * (weight i - weight x)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x _hx
          ring

/-- Exact weighted fracture of signed source mass into signed normalizer flux and signed
co-moving transport. -/
theorem routeE_two_mul_signedWeightedSum_eq_signedNormalizerFlux_add_coMoving
    (U : ι → ι → ℝ) (sign weight : ι → ℝ)
    (hsym : ∀ i j, U i j = U j i)
    (hrow : ∀ i, routeERowMass U i ≠ 0)
    (hflip : ∀ i j, U i j ≠ 0 → sign i + sign j = 0) :
    2 * ∑ i, sign i * weight i =
      (∑ i, sign i * weight i * routeESymmetricNormalizerFlux U i) +
        ∑ i, sign i *
          (∑ j, U i j / routeERowMass U j * (weight i - weight j)) := by
  have hnormalizedRow :
      ∀ i, routeERowMass (routeERowNormalizedKernel U) i = 1 :=
    fun i => routeE_rowMass_rowNormalizedKernel_eq_one U i (hrow i)
  have hnormalizedFlip :
      ∀ i j, routeERowNormalizedKernel U i j ≠ 0 → sign i + sign j = 0 := by
    intro i j hij
    apply hflip i j
    intro hzero
    simp [routeERowNormalizedKernel, hzero] at hij
  rw [routeE_two_mul_signedWeightedSum_eq_signedWeightedIncomingDefect
    (routeERowNormalizedKernel U) sign weight hnormalizedRow hnormalizedFlip]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [routeE_weightedIncomingDefect_eq_weightedNormalizerFlux_add_coMoving
    U weight hsym hrow i]
  ring

/-- Constant vertex weights make signed normalizer flux exactly twice the original signed sum. -/
theorem routeE_two_mul_signedSum_eq_signedNormalizerFlux
    (U : ι → ι → ℝ) (sign : ι → ℝ)
    (hsym : ∀ i j, U i j = U j i)
    (hrow : ∀ i, routeERowMass U i ≠ 0)
    (hflip : ∀ i j, U i j ≠ 0 → sign i + sign j = 0) :
    2 * ∑ i, sign i =
      ∑ i, sign i * routeESymmetricNormalizerFlux U i := by
  simpa using routeE_two_mul_signedWeightedSum_eq_signedNormalizerFlux_add_coMoving
    U sign (fun _ => 1) hsym hrow hflip

/-- Total absolute normalizer flux cannot be smaller than twice the original signed imbalance. -/
theorem routeE_two_mul_abs_signedSum_le_sum_abs_normalizerFlux
    (U : ι → ι → ℝ) (sign : ι → ℝ)
    (hsign : ∀ i, |sign i| ≤ 1)
    (hsym : ∀ i j, U i j = U j i)
    (hrow : ∀ i, routeERowMass U i ≠ 0)
    (hflip : ∀ i j, U i j ≠ 0 → sign i + sign j = 0) :
    2 * |∑ i, sign i| ≤
      ∑ i, |routeESymmetricNormalizerFlux U i| := by
  calc
    2 * |∑ i, sign i| = |2 * ∑ i, sign i| := by norm_num
    _ = |∑ i, sign i * routeESymmetricNormalizerFlux U i| := by
      rw [routeE_two_mul_signedSum_eq_signedNormalizerFlux U sign hsym hrow hflip]
    _ ≤ ∑ i, |sign i * routeESymmetricNormalizerFlux U i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |routeESymmetricNormalizerFlux U i| := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right (hsign i)
        (abs_nonneg (routeESymmetricNormalizerFlux U i))

/-- Symmetric sign-reversing incidence gives equal total raw degree to the two sign classes. -/
theorem routeE_sum_sign_mul_rowMass_eq_zero
    (U : ι → ι → ℝ) (sign : ι → ℝ)
    (hsym : ∀ i j, U i j = U j i)
    (hflip : ∀ i j, U i j ≠ 0 → sign i + sign j = 0) :
    ∑ i, sign i * routeERowMass U i = 0 := by
  have hterm (i j : ι) : sign i * U i j = -sign j * U i j := by
    by_cases hzero : U i j = 0
    · simp [hzero]
    · have hsign : sign i = -sign j := by
        linarith [hflip i j hzero]
      rw [hsign]
  have hcol (j : ι) : (∑ i, U i j) = routeERowMass U j := by
    unfold routeERowMass
    apply Finset.sum_congr rfl
    intro i _hi
    exact hsym i j
  have hneg :
      (∑ i, sign i * routeERowMass U i) =
        -(∑ i, sign i * routeERowMass U i) := by
    calc
      (∑ i, sign i * routeERowMass U i) =
          ∑ i, ∑ j, sign i * U i j := by
            unfold routeERowMass
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, sign i * U i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -sign j * U i j := by
            apply Finset.sum_congr rfl
            intro j _hj
            apply Finset.sum_congr rfl
            intro i _hi
            exact hterm i j
      _ = -(∑ j, sign j * routeERowMass U j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro j _hj
            rw [← hcol j]
            calc
              (∑ i, -sign j * U i j) = ∑ i, -(sign j * U i j) := by
                apply Finset.sum_congr rfl
                intro i _hi
                ring
              _ = -∑ i, sign j * U i j := by rw [Finset.sum_neg_distrib]
              _ = -(sign j * ∑ i, U i j) := by rw [Finset.mul_sum]
  linarith

/-- Signed vertex imbalance is exactly signed raw row-mass defect. -/
theorem routeE_signedSum_eq_signedRowMassDefect
    (U : ι → ι → ℝ) (sign : ι → ℝ)
    (hsym : ∀ i j, U i j = U j i)
    (hflip : ∀ i j, U i j ≠ 0 → sign i + sign j = 0) :
    ∑ i, sign i = ∑ i, sign i * (1 - routeERowMass U i) := by
  have hzero := routeE_sum_sign_mul_rowMass_eq_zero U sign hsym hflip
  simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  linarith

/-- Total absolute raw row-mass defect cannot be smaller than original signed imbalance. -/
theorem routeE_abs_signedSum_le_sum_abs_rowMassDefect
    (U : ι → ι → ℝ) (sign : ι → ℝ)
    (hsign : ∀ i, |sign i| ≤ 1)
    (hsym : ∀ i j, U i j = U j i)
    (hflip : ∀ i j, U i j ≠ 0 → sign i + sign j = 0) :
    |∑ i, sign i| ≤ ∑ i, |1 - routeERowMass U i| := by
  rw [routeE_signedSum_eq_signedRowMassDefect U sign hsym hflip]
  calc
    |∑ i, sign i * (1 - routeERowMass U i)| ≤
        ∑ i, |sign i * (1 - routeERowMass U i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |1 - routeERowMass U i| := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right (hsign i)
        (abs_nonneg (1 - routeERowMass U i))

end

end RHTower
