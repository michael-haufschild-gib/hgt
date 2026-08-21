import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockObservation

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- Raw Perron recutting to one observation cone fixed throughout a dyadic physical block. -/
theorem integral_windowRelevant_mul_scaled_routeTMellin_eq_dyadicBlockObserved
    (L X k : ℕ) (T t : ℝ) {x lambda N R W sigma : ℝ}
    (hx : 0 < x) (hlambda : lambda ∈ Set.Icc x (2 * x))
    (hN : 0 < N) (hR : 0 < R) (hW : 0 < W) (hWR : W ≤ R)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (lambda * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun z : ℝ =>
          ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
    ∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t
          (x * N) (maynardDyadicBlockObservationRadius x N R)
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun z : ℝ =>
          ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) := by
  have hlambdaPos : 0 < lambda := hx.trans_le hlambda.1
  have hbase : 0 < lambda * N := mul_pos hlambdaPos hN
  have hwidth : 0 < lambda * W := mul_pos hlambdaPos hW
  have hold := smul_tsum_mul_routeTSmoothWindowWeight_eq_integral_of_upperSupported
    (upperSupported_heathBrownWindowRelevantEligiblePacket
      L X k T t (lambda * N)) hbase hwidth hsigma
  have hnew := smul_tsum_mul_routeTSmoothWindowWeight_eq_integral_of_upperSupported
    (upperSupported_heathBrownObservedEligiblePacket L X k T t
      (x * N) (maynardDyadicBlockObservationRadius x N R)) hbase hwidth hsigma
  have hsum :
      (∑' n : ℕ,
        complexCoeff (heathBrownWindowRelevantEligiblePacket
            L X k T t (lambda * N)) n *
          ((routeTSmoothWindowWeight
            (lambda * N) (lambda * W) (n : ℝ) : ℝ) : ℂ)) =
      ∑' n : ℕ,
        complexCoeff (heathBrownObservedEligiblePacket L X k T t
            (x * N) (maynardDyadicBlockObservationRadius x N R)) n *
          ((routeTSmoothWindowWeight
            (lambda * N) (lambda * W) (n : ℝ) : ℝ) : ℂ) := by
    apply tsum_congr
    exact complexCoeff_windowRelevant_mul_scaled_routeWeight_eq_dyadicBlockObserved
      L X k T t hx hlambda hN hR hW hWR
  rw [hsum] at hold
  calc
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (lambda * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun z : ℝ =>
          ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
      ∫ y : ℝ,
        LSeries (complexCoeff
          (heathBrownWindowRelevantEligiblePacket L X k T t (lambda * N)))
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun z : ℝ =>
            ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [LSeries_heathBrownWindowRelevantEligiblePacket]
    _ = ∫ y : ℝ,
        LSeries (complexCoeff
          (heathBrownObservedEligiblePacket L X k T t
            (x * N) (maynardDyadicBlockObservationRadius x N R)))
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun z : ℝ =>
            ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := hold.symm.trans hnew
    _ = ∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t
          (x * N) (maynardDyadicBlockObservationRadius x N R)
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun z : ℝ =>
          ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [LSeries_heathBrownObservedEligiblePacket]

/-- Width-normalized Perron recutting to one cone fixed throughout a dyadic block. -/
theorem integral_windowRelevant_mul_scaled_routeTNormalizedMellin_eq_dyadicBlockObserved
    (L X k : ℕ) (T t : ℝ) {x lambda N R W sigma : ℝ}
    (hx : 0 < x) (hlambda : lambda ∈ Set.Icc x (2 * x))
    (hN : 0 < N) (hR : 0 < R) (hW : 0 < W) (hWR : W ≤ R)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (lambda * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * W)
          ((sigma : ℂ) + (y : ℝ) * I)) =
    ∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t
          (x * N) (maynardDyadicBlockObservationRadius x N R)
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * W)
          ((sigma : ℂ) + (y : ℝ) * I) := by
  have hraw := integral_windowRelevant_mul_scaled_routeTMellin_eq_dyadicBlockObserved
    L X k T t hx hlambda hN hR hW hWR hsigma
  calc
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (lambda * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * W)
          ((sigma : ℂ) + (y : ℝ) * I)) =
      ((lambda * W : ℝ) : ℂ)⁻¹ * ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (lambda * N)
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun z : ℝ =>
            ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        rw [routeTNormalizedSmoothWindowMellin]
        ring
    _ = ((lambda * W : ℝ) : ℂ)⁻¹ * ∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t
          (x * N) (maynardDyadicBlockObservationRadius x N R)
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun z : ℝ =>
          ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) := by rw [hraw]
    _ = ∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t
          (x * N) (maynardDyadicBlockObservationRadius x N R)
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * W)
          ((sigma : ℂ) + (y : ℝ) * I) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        rw [routeTNormalizedSmoothWindowMellin]
        ring

/-- The complete scaled adjacent normalized defect uses one fixed observation cone over the whole
dyadic physical block. -/
theorem integral_windowRelevant_mul_scaled_adjacentNormalizedMellin_eq_dyadicBlockObserved
    (L X k : ℕ) (T t : ℝ) {x lambda N R H sigma : ℝ}
    (hx : 0 < x) (hlambda : lambda ∈ Set.Icc x (2 * x))
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) (hHR : H ≤ R)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (lambda * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
            ((sigma : ℂ) + (y : ℝ) * I))) =
    ∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t
          (x * N) (maynardDyadicBlockObservationRadius x N R)
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
            ((sigma : ℂ) + (y : ℝ) * I)) := by
  have hlambdaPos : 0 < lambda := hx.trans_le hlambda.1
  have hbase : 0 < lambda * N := mul_pos hlambdaPos hN
  have hRscaled : 0 < lambda * R := mul_pos hlambdaPos hR
  have hHscaled : 0 < lambda * H := mul_pos hlambdaPos hH
  have hOldR := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
    L X k T t (lambda * N) hbase hRscaled hsigma
  have hOldH := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
    L X k T t (lambda * N) hbase hHscaled hsigma
  have hNewR := integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
    (upperSupported_heathBrownObservedEligiblePacket L X k T t
      (x * N) (maynardDyadicBlockObservationRadius x N R)) hbase hRscaled hsigma
  have hNewH := integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
    (upperSupported_heathBrownObservedEligiblePacket L X k T t
      (x * N) (maynardDyadicBlockObservationRadius x N R)) hbase hHscaled hsigma
  simp_rw [mul_sub]
  rw [integral_sub hOldR hOldH,
    integral_windowRelevant_mul_scaled_routeTNormalizedMellin_eq_dyadicBlockObserved
      L X k T t hx hlambda hN hR hR le_rfl hsigma,
    integral_windowRelevant_mul_scaled_routeTNormalizedMellin_eq_dyadicBlockObserved
      L X k T t hx hlambda hN hR hH hHR hsigma]
  have hNewR' : Integrable (fun y : ℝ =>
      heathBrownObservedEligibleDyadicAggregate L X k T t
          (x * N) (maynardDyadicBlockObservationRadius x N R)
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
          ((sigma : ℂ) + (y : ℝ) * I)) := by
    refine hNewR.congr (Eventually.of_forall fun y => ?_)
    exact congrArg
      (fun z : ℂ => z * routeTNormalizedSmoothWindowMellin
        (lambda * N) (lambda * R) ((sigma : ℂ) + (y : ℝ) * I))
      (LSeries_heathBrownObservedEligiblePacket L X k T t
        (x * N) (maynardDyadicBlockObservationRadius x N R)
        ((sigma : ℂ) + (y : ℝ) * I))
  have hNewH' : Integrable (fun y : ℝ =>
      heathBrownObservedEligibleDyadicAggregate L X k T t
          (x * N) (maynardDyadicBlockObservationRadius x N R)
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
          ((sigma : ℂ) + (y : ℝ) * I)) := by
    refine hNewH.congr (Eventually.of_forall fun y => ?_)
    exact congrArg
      (fun z : ℂ => z * routeTNormalizedSmoothWindowMellin
        (lambda * N) (lambda * H) ((sigma : ℂ) + (y : ℝ) * I))
      (LSeries_heathBrownObservedEligiblePacket L X k T t
        (x * N) (maynardDyadicBlockObservationRadius x N R)
        ((sigma : ℂ) + (y : ℝ) * I))
  exact (integral_sub hNewR' hNewH').symm

/-- Raw Perron recutting to the fixed left-base window-relevant packet throughout a dyadic
physical block.  No observation cone or enlarged radius is needed. -/
theorem integral_windowRelevant_mul_scaled_routeTMellin_eq_leftWindowRelevant
    (L X k : ℕ) (T t : ℝ) {x lambda N W sigma : ℝ}
    (hx : 0 < x) (hlambda : lambda ∈ Set.Icc x (2 * x))
    (hN : 0 < N) (hW : 0 < W) (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (lambda * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun z : ℝ =>
          ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
    ∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (x * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun z : ℝ =>
          ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) := by
  have hlambdaPos : 0 < lambda := hx.trans_le hlambda.1
  have hbase : 0 < lambda * N := mul_pos hlambdaPos hN
  have hwidth : 0 < lambda * W := mul_pos hlambdaPos hW
  have hold := smul_tsum_mul_routeTSmoothWindowWeight_eq_integral_of_upperSupported
    (upperSupported_heathBrownWindowRelevantEligiblePacket
      L X k T t (lambda * N)) hbase hwidth hsigma
  have hnew := smul_tsum_mul_routeTSmoothWindowWeight_eq_integral_of_upperSupported
    (upperSupported_heathBrownWindowRelevantEligiblePacket
      L X k T t (x * N)) hbase hwidth hsigma
  have hsum :
      (∑' n : ℕ,
        complexCoeff (heathBrownWindowRelevantEligiblePacket
            L X k T t (lambda * N)) n *
          ((routeTSmoothWindowWeight
            (lambda * N) (lambda * W) (n : ℝ) : ℝ) : ℂ)) =
      ∑' n : ℕ,
        complexCoeff (heathBrownWindowRelevantEligiblePacket
            L X k T t (x * N)) n *
          ((routeTSmoothWindowWeight
            (lambda * N) (lambda * W) (n : ℝ) : ℝ) : ℂ) := by
    apply tsum_congr
    exact complexCoeff_windowRelevant_mul_scaled_routeWeight_eq_leftWindowRelevant
      L X k T t hx hlambda hN hW
  rw [hsum] at hold
  calc
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (lambda * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun z : ℝ =>
          ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
      ∫ y : ℝ,
        LSeries (complexCoeff
          (heathBrownWindowRelevantEligiblePacket L X k T t (lambda * N)))
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun z : ℝ =>
            ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [LSeries_heathBrownWindowRelevantEligiblePacket]
    _ = ∫ y : ℝ,
        LSeries (complexCoeff
          (heathBrownWindowRelevantEligiblePacket L X k T t (x * N)))
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun z : ℝ =>
            ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := hold.symm.trans hnew
    _ = ∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (x * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun z : ℝ =>
          ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [LSeries_heathBrownWindowRelevantEligiblePacket]

/-- Width-normalized Perron recutting to the fixed left-base window-relevant packet. -/
theorem integral_windowRelevant_mul_scaled_routeTNormalizedMellin_eq_leftWindowRelevant
    (L X k : ℕ) (T t : ℝ) {x lambda N W sigma : ℝ}
    (hx : 0 < x) (hlambda : lambda ∈ Set.Icc x (2 * x))
    (hN : 0 < N) (hW : 0 < W) (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (lambda * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * W)
          ((sigma : ℂ) + (y : ℝ) * I)) =
    ∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (x * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * W)
          ((sigma : ℂ) + (y : ℝ) * I) := by
  have hraw := integral_windowRelevant_mul_scaled_routeTMellin_eq_leftWindowRelevant
    L X k T t hx hlambda hN hW hsigma
  calc
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (lambda * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * W)
          ((sigma : ℂ) + (y : ℝ) * I)) =
      ((lambda * W : ℝ) : ℂ)⁻¹ * ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (lambda * N)
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun z : ℝ =>
            ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        rw [routeTNormalizedSmoothWindowMellin]
        ring
    _ = ((lambda * W : ℝ) : ℂ)⁻¹ * ∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (x * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun z : ℝ =>
          ((routeTSmoothWindowWeight (lambda * N) (lambda * W) z : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) := by rw [hraw]
    _ = ∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (x * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * W)
          ((sigma : ℂ) + (y : ℝ) * I) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        rw [routeTNormalizedSmoothWindowMellin]
        ring

/-- The complete scaled adjacent normalized defect uses the fixed left-base window-relevant
packet over the whole dyadic physical block. -/
theorem integral_windowRelevant_mul_scaled_adjacentNormalizedMellin_eq_leftWindowRelevant
    (L X k : ℕ) (T t : ℝ) {x lambda N R H sigma : ℝ}
    (hx : 0 < x) (hlambda : lambda ∈ Set.Icc x (2 * x))
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (lambda * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
            ((sigma : ℂ) + (y : ℝ) * I))) =
    ∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (x * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
            ((sigma : ℂ) + (y : ℝ) * I)) := by
  have hlambdaPos : 0 < lambda := hx.trans_le hlambda.1
  have hbase : 0 < lambda * N := mul_pos hlambdaPos hN
  have hRscaled : 0 < lambda * R := mul_pos hlambdaPos hR
  have hHscaled : 0 < lambda * H := mul_pos hlambdaPos hH
  have hOldR := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
    L X k T t (lambda * N) hbase hRscaled hsigma
  have hOldH := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
    L X k T t (lambda * N) hbase hHscaled hsigma
  have hNewR := integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
    (upperSupported_heathBrownWindowRelevantEligiblePacket L X k T t (x * N))
    hbase hRscaled hsigma
  have hNewH := integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
    (upperSupported_heathBrownWindowRelevantEligiblePacket L X k T t (x * N))
    hbase hHscaled hsigma
  simp_rw [mul_sub]
  rw [integral_sub hOldR hOldH,
    integral_windowRelevant_mul_scaled_routeTNormalizedMellin_eq_leftWindowRelevant
      L X k T t hx hlambda hN hR hsigma,
    integral_windowRelevant_mul_scaled_routeTNormalizedMellin_eq_leftWindowRelevant
      L X k T t hx hlambda hN hH hsigma]
  have hNewR' : Integrable (fun y : ℝ =>
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (x * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
          ((sigma : ℂ) + (y : ℝ) * I)) := by
    refine hNewR.congr (Eventually.of_forall fun y => ?_)
    exact congrArg
      (fun z : ℂ => z * routeTNormalizedSmoothWindowMellin
        (lambda * N) (lambda * R) ((sigma : ℂ) + (y : ℝ) * I))
      (LSeries_heathBrownWindowRelevantEligiblePacket L X k T t (x * N)
        ((sigma : ℂ) + (y : ℝ) * I))
  have hNewH' : Integrable (fun y : ℝ =>
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t (x * N)
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
          ((sigma : ℂ) + (y : ℝ) * I)) := by
    refine hNewH.congr (Eventually.of_forall fun y => ?_)
    exact congrArg
      (fun z : ℂ => z * routeTNormalizedSmoothWindowMellin
        (lambda * N) (lambda * H) ((sigma : ℂ) + (y : ℝ) * I))
      (LSeries_heathBrownWindowRelevantEligiblePacket L X k T t (x * N)
        ((sigma : ℂ) + (y : ℝ) * I))
  exact (integral_sub hNewR' hNewH').symm

end RHTower.Sieve
