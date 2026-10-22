import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarAdjacentCodiagonal
import GaloisForLFunctions.RHTower.PrimeGammaCauchyCubicSignedEulerianCurvature

/-!
# The SP-E codiagonal cancels the leading Route-P cubic Cauchy mode

The finite matched-minus-quantile codiagonal is exactly mass neutral.  Pair it with the Route-P
zero-ordinate Cauchy-cubic edge `2 / (x + y)^(3 : ℕ)`.  Its constant base mode `2 / x^(3 : ℕ)` cancels
identically, leaving a kernel with an explicit factor of the literal polar coordinate `y`:

```text
  2/(x+y)^(3 : ℕ) - 2/x^(3 : ℕ) =
    -2y(3x^(2 : ℕ) + 3xy + y^(2 : ℕ)) / (x^(3 : ℕ) (x+y)^(3 : ℕ)).
```

This is a source-faithful finite P/SP-E bridge.  Its exact tangent--remainder ledger separates
the codiagonal probe into its completed-error first mode, its non-discardable upper-endpoint
channel, and a literal quadratic-coordinate remainder.  It does not bound either signed channel
or the remainder uniformly as the cutoff changes; that is the remaining cofinal problem.  In
particular, this file neither bounds the completed SP-E current nor constructs Route P's
non-Bessel transport.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Route P's cubic Cauchy probe of the finite literal SP-E adjacent codiagonal. -/
def ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicProbe
    (K : ℕ) (x : ℝ) : ℝ :=
  ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K
    (fun y => primeGammaCauchyCubicEdge x y)

/-- The cubic Cauchy edge minus its zero-coordinate base mode has one explicit source-coordinate
factor. -/
theorem primeGammaCauchyCubicEdge_sub_base_factor
    {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    primeGammaCauchyCubicEdge x y - primeGammaCauchyCubicEdge x 0 =
      -2 * y * (3 * x ^ (2 : ℕ) + 3 * x * y + y ^ (2 : ℕ)) /
        (x ^ (3 : ℕ) * (x + y) ^ (3 : ℕ)) := by
  unfold primeGammaCauchyCubicEdge
  have hxy : x + y ≠ 0 := (add_pos_of_pos_of_nonneg hx hy).ne'
  field_simp [hx.ne', hxy]
  ring

/-- On the positive polar ray, the base-subtracted cubic Cauchy edge has a fixed negative sign.
The signed codiagonal itself still has no prescribed orientation, so this pointwise sign is not a
bound for the probe. -/
theorem primeGammaCauchyCubicEdge_sub_base_nonpos
    {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    primeGammaCauchyCubicEdge x y - primeGammaCauchyCubicEdge x 0 ≤ 0 := by
  rw [primeGammaCauchyCubicEdge_sub_base_factor hx hy]
  have hpoly : 0 ≤ 3 * x ^ (2 : ℕ) + 3 * x * y + y ^ (2 : ℕ) := by positivity
  have hden : 0 < x ^ (3 : ℕ) * (x + y) ^ (3 : ℕ) := by positivity
  have hnum : -2 * y * (3 * x ^ (2 : ℕ) + 3 * x * y + y ^ (2 : ℕ)) ≤ 0 := by
    nlinarith [mul_nonneg hy hpoly]
  exact div_nonpos_of_nonpos_of_nonneg hnum hden.le

/-- **Base-mode cancellation.**  The exact zero-mass SP-E codiagonal annihilates the leading
`2/x^(3 : ℕ)` Route-P Cauchy mode. -/
theorem ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicProbe_base_cancel
    (K : ℕ) {x : ℝ} (hx : 0 < x) :
    ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicProbe K x =
      ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K
        (fun y => primeGammaCauchyCubicEdge x y -
          primeGammaCauchyCubicEdge x 0) := by
  unfold ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicProbe
  have hcont : ContinuousOn (fun y => primeGammaCauchyCubicEdge x y) (Set.Ioi 0) := by
    unfold primeGammaCauchyCubicEdge
    apply ContinuousOn.div continuousOn_const
      ((continuousOn_const.add continuousOn_id).pow 3)
    intro y hy
    exact pow_ne_zero _ (ne_of_gt (add_pos hx hy))
  have hinterval (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      IntervalIntegrable (fun y => primeGammaCauchyCubicEdge x y) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le hab]
      exact hcont.mono fun y hy => Set.mem_Ioi.mpr (lt_of_lt_of_le ha hy.1)
    · rw [Set.uIcc_comm, Set.uIcc_of_le hba]
      exact hcont.mono fun y hy => Set.mem_Ioi.mpr (lt_of_lt_of_le hb hy.1)
  have hsub (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      (∫ y in a..b, primeGammaCauchyCubicEdge x y -
        primeGammaCauchyCubicEdge x 0) =
        (∫ y in a..b, primeGammaCauchyCubicEdge x y) -
          ∫ _y in a..b, primeGammaCauchyCubicEdge x 0 :=
    intervalIntegral.integral_sub (hinterval a b ha hb) intervalIntegrable_const
  have hlower (n : ℕ) : 0 < ccmActualHeadMatchedPolarLowerCoordinate n := by
    unfold ccmActualHeadMatchedPolarLowerCoordinate
    positivity
  have hupper (n : ℕ) : 0 < ccmActualHeadMatchedPolarUpperCoordinate n := by
    unfold ccmActualHeadMatchedPolarUpperCoordinate
    positivity
  have hquantile (n : ℕ) : 0 < ccmActualHeadQuantilePolarCoordinate n := by
    unfold ccmActualHeadQuantilePolarCoordinate
    positivity
  have hprofile :
      ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K
          (fun y => primeGammaCauchyCubicEdge x y -
            primeGammaCauchyCubicEdge x 0) =
        ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K
          (fun y => primeGammaCauchyCubicEdge x y) -
          ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K
            (fun _y => primeGammaCauchyCubicEdge x 0) := by
    unfold ccmActualHeadMatchedPolarAdjacentCodiagonalProfile
    have hsum :
        (∑ n ∈ Finset.range K,
          ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
            ccmActualHeadMatchedPolarUpperCoordinate (n + 2),
              primeGammaCauchyCubicEdge x y - primeGammaCauchyCubicEdge x 0) =
          ∑ n ∈ Finset.range K,
            ((∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
              ccmActualHeadMatchedPolarUpperCoordinate (n + 2),
                primeGammaCauchyCubicEdge x y) -
              ∫ _y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
                ccmActualHeadMatchedPolarUpperCoordinate (n + 2),
                  primeGammaCauchyCubicEdge x 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hsub _ _ (hlower _) (hupper _)
    rw [hsum,
      hsub _ _ (hquantile _) (hupper _),
      hsub _ _ (hlower _) (hquantile _)]
    rw [Finset.sum_sub_distrib]
    ring
  have hconst :
      ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K
          (fun _y => primeGammaCauchyCubicEdge x 0) =
        primeGammaCauchyCubicEdge x 0 *
          ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K (fun _y : ℝ => 1) := by
    unfold ccmActualHeadMatchedPolarAdjacentCodiagonalProfile
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    simp only [mul_one]
    rw [← Finset.sum_mul]
    ring
  rw [hprofile, hconst, ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_one]
  ring

/-- **First-moment P/SP-E bridge.**  After exact codiagonal neutralization, the cubic Cauchy
probe is the literal codiagonal paired against a kernel carrying one polar-coordinate factor. -/
theorem ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicProbe_eq_firstMomentKernel
    (K : ℕ) {x : ℝ} (hx : 0 < x) :
    ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicProbe K x =
      ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K
        (fun y =>
          -2 * y * (3 * x ^ (2 : ℕ) + 3 * x * y + y ^ (2 : ℕ)) /
            (x ^ (3 : ℕ) * (x + y) ^ (3 : ℕ))) := by
  rw [ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicProbe_base_cancel K hx]
  have hlower (n : ℕ) : 0 < ccmActualHeadMatchedPolarLowerCoordinate n := by
    unfold ccmActualHeadMatchedPolarLowerCoordinate
    positivity
  have hupper (n : ℕ) : 0 < ccmActualHeadMatchedPolarUpperCoordinate n := by
    unfold ccmActualHeadMatchedPolarUpperCoordinate
    positivity
  have hquantile (n : ℕ) : 0 < ccmActualHeadQuantilePolarCoordinate n := by
    unfold ccmActualHeadQuantilePolarCoordinate
    positivity
  have hfactor (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      (∫ y in a..b, primeGammaCauchyCubicEdge x y -
        primeGammaCauchyCubicEdge x 0) =
        ∫ y in a..b,
          -2 * y * (3 * x ^ (2 : ℕ) + 3 * x * y + y ^ (2 : ℕ)) /
            (x ^ (3 : ℕ) * (x + y) ^ (3 : ℕ)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    apply primeGammaCauchyCubicEdge_sub_base_factor hx
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le hab] at hy
      exact (lt_of_lt_of_le ha hy.1).le
    · rw [Set.uIcc_comm, Set.uIcc_of_le hba] at hy
      exact (lt_of_lt_of_le hb hy.1).le
  unfold ccmActualHeadMatchedPolarAdjacentCodiagonalProfile
  have hsum :
      (∑ n ∈ Finset.range K,
        ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
          ccmActualHeadMatchedPolarUpperCoordinate (n + 2),
            primeGammaCauchyCubicEdge x y - primeGammaCauchyCubicEdge x 0) =
        ∑ n ∈ Finset.range K,
          ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
            ccmActualHeadMatchedPolarUpperCoordinate (n + 2),
              -2 * y * (3 * x ^ (2 : ℕ) + 3 * x * y + y ^ (2 : ℕ)) /
                (x ^ (3 : ℕ) * (x + y) ^ (3 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hfactor _ _ (hlower _) (hupper _)
  rw [hsum,
    hfactor _ _ (hquantile _) (hupper _),
    hfactor _ _ (hlower _) (hquantile _)]

/-- The exact quadratic-order remainder after subtracting the tangent of the cubic Cauchy edge
at its zero polar-coordinate basepoint. -/
def ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder
    (x y : ℝ) : ℝ :=
  2 * y ^ (2 : ℕ) * (6 * x ^ (2 : ℕ) + 8 * x * y + 3 * y ^ (2 : ℕ)) /
    (x ^ (4 : ℕ) * (x + y) ^ (3 : ℕ))

/-- **Exact cubic Cauchy tangent--remainder identity.**  The residual after the leading
first-coordinate term has an explicit quadratic-coordinate factor. -/
theorem primeGammaCauchyCubicEdge_sub_base_taylor
    {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    primeGammaCauchyCubicEdge x y - primeGammaCauchyCubicEdge x 0 =
      -6 * y / x ^ (4 : ℕ) +
        ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder x y := by
  unfold primeGammaCauchyCubicEdge
    ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder
  have hxy : x + y ≠ 0 := (add_pos_of_pos_of_nonneg hx hy).ne'
  field_simp [hx.ne', hxy]
  ring

/-- The Taylor remainder is pointwise nonnegative on the positive polar ray.  This does not
give a codiagonal sign bound: the literal matched-minus-quantile codiagonal remains signed. -/
theorem ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder_nonneg
    {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    0 ≤ ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder x y := by
  unfold ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder
  have hnum : 0 ≤ 2 * y ^ (2 : ℕ) * (6 * x ^ (2 : ℕ) + 8 * x * y + 3 * y ^ (2 : ℕ)) := by
    positivity
  have hden : 0 < x ^ (4 : ℕ) * (x + y) ^ (3 : ℕ) := by
    positivity
  exact div_nonneg hnum hden.le

private theorem ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_eq_of_forall_nonneg
    (K : ℕ) {F G : ℝ → ℝ}
    (hFG : ∀ y : ℝ, 0 ≤ y → F y = G y) :
    ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K F =
      ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K G := by
  have hlow (n : ℕ) : 0 < ccmActualHeadMatchedPolarLowerCoordinate n := by
    unfold ccmActualHeadMatchedPolarLowerCoordinate
    positivity
  have hupp (n : ℕ) : 0 < ccmActualHeadMatchedPolarUpperCoordinate n := by
    unfold ccmActualHeadMatchedPolarUpperCoordinate
    positivity
  have hquant (n : ℕ) : 0 < ccmActualHeadQuantilePolarCoordinate n := by
    unfold ccmActualHeadQuantilePolarCoordinate
    positivity
  have hinterval (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      (∫ y in a..b, F y) = ∫ y in a..b, G y := by
    apply intervalIntegral.integral_congr
    intro y hy
    apply hFG y
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le hab] at hy
      exact (lt_of_lt_of_le ha hy.1).le
    · rw [Set.uIcc_comm, Set.uIcc_of_le hba] at hy
      exact (lt_of_lt_of_le hb hy.1).le
  unfold ccmActualHeadMatchedPolarAdjacentCodiagonalProfile
  have hsum :
      (∑ n ∈ Finset.range K,
        ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
          ccmActualHeadMatchedPolarUpperCoordinate (n + 2), F y) =
      ∑ n ∈ Finset.range K,
        ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
          ccmActualHeadMatchedPolarUpperCoordinate (n + 2), G y := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hinterval _ _ (hlow _) (hupp _)
  rw [hsum, hinterval _ _ (hquant _) (hupp _), hinterval _ _ (hlow _) (hquant _)]

private theorem ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_add
    (K : ℕ) (F G : ℝ → ℝ)
    (hF : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable F MeasureTheory.volume a b)
    (hG : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable G MeasureTheory.volume a b) :
    ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K (fun y => F y + G y) =
      ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K F +
        ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K G := by
  have hlow (n : ℕ) : 0 < ccmActualHeadMatchedPolarLowerCoordinate n := by
    unfold ccmActualHeadMatchedPolarLowerCoordinate
    positivity
  have hupp (n : ℕ) : 0 < ccmActualHeadMatchedPolarUpperCoordinate n := by
    unfold ccmActualHeadMatchedPolarUpperCoordinate
    positivity
  have hquant (n : ℕ) : 0 < ccmActualHeadQuantilePolarCoordinate n := by
    unfold ccmActualHeadQuantilePolarCoordinate
    positivity
  have hinterval (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      (∫ y in a..b, F y + G y) =
        (∫ y in a..b, F y) + ∫ y in a..b, G y := by
    exact intervalIntegral.integral_add (hF a b ha hb) (hG a b ha hb)
  unfold ccmActualHeadMatchedPolarAdjacentCodiagonalProfile
  have hsum :
      (∑ n ∈ Finset.range K,
        ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
          ccmActualHeadMatchedPolarUpperCoordinate (n + 2), F y + G y) =
      (∑ n ∈ Finset.range K,
        ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
          ccmActualHeadMatchedPolarUpperCoordinate (n + 2), F y) +
      ∑ n ∈ Finset.range K,
        ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
          ccmActualHeadMatchedPolarUpperCoordinate (n + 2), G y := by
    calc
      (∑ n ∈ Finset.range K,
        ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
          ccmActualHeadMatchedPolarUpperCoordinate (n + 2), F y + G y) =
          ∑ n ∈ Finset.range K,
            ((∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
              ccmActualHeadMatchedPolarUpperCoordinate (n + 2), F y) +
              ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
                ccmActualHeadMatchedPolarUpperCoordinate (n + 2), G y) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hinterval _ _ (hlow _) (hupp _)
      _ = _ := Finset.sum_add_distrib
  rw [hsum, hinterval _ _ (hquant _) (hupp _), hinterval _ _ (hlow _) (hquant _)]
  ring

private theorem ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_const_mul
    (K : ℕ) (a : ℝ) (F : ℝ → ℝ) :
    ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K (fun y => a * F y) =
      a * ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K F := by
  unfold ccmActualHeadMatchedPolarAdjacentCodiagonalProfile
  simp_rw [intervalIntegral.integral_const_mul]
  rw [← Finset.mul_sum]
  ring

/-- **Exact P/SP-E tangent ledger.**  The finite Route-P cubic Cauchy probe splits into:

* its endpoint-renormalized first codiagonal mode (the signed completed-error readout),
* the separately retained raw-upper-endpoint channel, and
* a literal quadratic-coordinate Cauchy remainder.

No term is discarded and no cofinal bound is asserted. -/
theorem ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicProbe_taylor_ledger
    (K : ℕ) {x : ℝ} (hx : 0 < x) :
    ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicProbe K x =
      -6 / x ^ (4 : ℕ) *
          ccmActualHeadMatchedPolarAdjacentCodiagonalEndpointRenormalizedFirstMoment K -
        6 / x ^ (4 : ℕ) * ccmActualHeadMatchedPolarAdjacentCodiagonalEndpointCounterterm K +
        ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K
          (ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder x) := by
  have hrem_cont : ContinuousOn
      (ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder x) (Set.Ioi 0) := by
    unfold ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro y hy
      exact mul_ne_zero (pow_ne_zero _ hx.ne')
        (pow_ne_zero _ (ne_of_gt (add_pos hx hy)))
  have hrem (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      IntervalIntegrable
        (ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder x)
        MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le hab]
      exact hrem_cont.mono fun y hy => Set.mem_Ioi.mpr (lt_of_lt_of_le ha hy.1)
    · rw [Set.uIcc_comm, Set.uIcc_of_le hba]
      exact hrem_cont.mono fun y hy => Set.mem_Ioi.mpr (lt_of_lt_of_le hb hy.1)
  have hid (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      IntervalIntegrable (fun y : ℝ => y) MeasureTheory.volume a b :=
    continuous_id.intervalIntegrable _ _
  calc
    ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicProbe K x =
        ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K
          (fun y => primeGammaCauchyCubicEdge x y - primeGammaCauchyCubicEdge x 0) :=
      ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicProbe_base_cancel K hx
    _ = ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K
          (fun y => -6 / x ^ (4 : ℕ) * y +
            ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder x y) := by
      apply ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_eq_of_forall_nonneg
      intro y hy
      calc
        primeGammaCauchyCubicEdge x y - primeGammaCauchyCubicEdge x 0 =
            -6 * y / x ^ (4 : ℕ) +
              ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder x y :=
          primeGammaCauchyCubicEdge_sub_base_taylor hx hy
        _ = -6 / x ^ (4 : ℕ) * y +
            ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder x y := by
          ring
    _ = -6 / x ^ (4 : ℕ) *
          ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K (fun y : ℝ => y) +
        ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K
          (ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder x) := by
      rw [ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_add K
        (fun y : ℝ => -6 / x ^ (4 : ℕ) * y)
        (ccmActualHeadMatchedPolarAdjacentCodiagonalCauchyCubicTaylorRemainder x)
        (fun a b ha hb => (hid a b ha hb).const_mul _) hrem,
        ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_const_mul K (-6 / x ^ (4 : ℕ))
          (fun y : ℝ => y)]
    _ = _ := by
      unfold ccmActualHeadMatchedPolarAdjacentCodiagonalEndpointRenormalizedFirstMoment
      ring

end RHTower
