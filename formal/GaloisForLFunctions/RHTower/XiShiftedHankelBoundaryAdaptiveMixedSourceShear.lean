import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryFactorialEulerSourceConnection
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryHilbertChargeFlow

/-!
# Adaptive mixed-amplitude source shear

The marked odd crossing `L_y(p · Xp)` has an exact source-first derivative.  Completed moment
transport and the Euler Leibniz rule force

`d/dy L_y(p · Xp) = -2 L_y((Xp) · (X E₁p))`.

Thus the landing object is neither a fixed linear reporter nor a post-aggregation orientation
map.  It is the even bilinear shear between `Xp` and the source-adapted probe `X E₁p`.

If `c` is the finite coefficient packet of `p²`, the odd crossing is the base-one consecutive
completed aggregate `S_(1,c)`.  Its derivative lands on `S_(2,M₁c)`, whose factorial carrier is
exactly the mixed amplitude

`Q_(1,c)(T) = Σ c_j T^j / ((j+1)!(j+2)!)`.

On the Euler ray this completed landing splits before reflection aggregation into its
archimedean and Chebyshev-discrepancy source pairings.  The same object is simultaneously the
mixed `P^sharp` aggregate and twice the adaptive bilinear shear.
-/

open Complex Matrix MeasureTheory Set Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Coefficients of the odd contact polynomial `p²`, kept as one finite adaptive packet. -/
def xiShiftedOddCrossingCoefficientPacket (p : Polynomial ℝ) :
    Fin ((p ^ (2 : ℕ)).natDegree + 1) → ℝ :=
  Polynomial.toFn ((p ^ (2 : ℕ)).natDegree + 1) (p ^ (2 : ℕ))

private theorem shiftedEuler_monomial
    (a b : ℝ) (j : ℕ) :
    X * (monomial j a).derivative + C b * monomial j a =
      monomial j (((j : ℝ) + b) * a) := by
  rw [Polynomial.derivative_monomial]
  by_cases hj : j = 0
  · subst j
    simp
  · simp only [X_mul_monomial, C_mul_monomial]
    rw [show j - 1 + 1 = j by omega]
    ext k
    by_cases hk : k = j
    · subst k
      simp
      ring
    · have hjk : j ≠ k := Ne.symm hk
      simp [Polynomial.coeff_monomial, hjk]

/-- **Euler source connection on the full polynomial moment functional.** This is the
coordinate-free finite-packet extension of completed moment transport. -/
theorem hasDerivAt_xiShiftedMomentFunctional_sourceConnection
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) :
    HasDerivAt
      (fun v => HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment v k).re) p)
      (-HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (X * xiShiftedBoundaryShiftedEuler 1 p)) y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hfun :
          (fun v => HTGeometry.momentFunctional
            (fun k => (xiShiftedReciprocalMoment v k).re) (p + q)) =
            (fun v =>
              HTGeometry.momentFunctional
                  (fun k => (xiShiftedReciprocalMoment v k).re) p +
                HTGeometry.momentFunctional
                  (fun k => (xiShiftedReciprocalMoment v k).re) q) := by
        funext v
        rw [HTGeometry.momentFunctional_add]
      have htarget :
          -HTGeometry.momentFunctional
              (fun k => (xiShiftedReciprocalMoment y k).re)
              (X * xiShiftedBoundaryShiftedEuler 1 (p + q)) =
            -HTGeometry.momentFunctional
                (fun k => (xiShiftedReciprocalMoment y k).re)
                (X * xiShiftedBoundaryShiftedEuler 1 p) +
              -HTGeometry.momentFunctional
                (fun k => (xiShiftedReciprocalMoment y k).re)
                (X * xiShiftedBoundaryShiftedEuler 1 q) := by
        simp only [xiShiftedBoundaryShiftedEuler, map_add, mul_add,
          HTGeometry.momentFunctional_add]
        ring
      rw [hfun, htarget]
      exact hp.add hq
  | monomial n a =>
      have h := (hasDerivAt_re_xiShiftedReciprocalMoment hy n).const_mul a
      have hfun :
          (fun v => HTGeometry.momentFunctional
            (fun k => (xiShiftedReciprocalMoment v k).re) (monomial n a)) =
            (fun v => a * (xiShiftedReciprocalMoment v n).re) := by
        funext v
        simp
      have htarget :
          -HTGeometry.momentFunctional
              (fun k => (xiShiftedReciprocalMoment y k).re)
              (X * xiShiftedBoundaryShiftedEuler 1 (monomial n a)) =
            a * (-((n : ℝ) + 1) *
              (xiShiftedReciprocalMoment y (n + 1)).re) := by
        change -HTGeometry.momentFunctional
            (fun k => (xiShiftedReciprocalMoment y k).re)
            (X * (X * (monomial n a).derivative + C 1 * monomial n a)) = _
        rw [shiftedEuler_monomial]
        simp only [X_mul_monomial, HTGeometry.momentFunctional_monomial]
        ring
      rw [hfun, htarget]
      exact h

private theorem adaptiveShear_polynomial_identity (p : Polynomial ℝ) :
    X * xiShiftedBoundaryShiftedEuler 1 (p * (X * p)) =
      (2 : ℝ) •
        ((X * p) * (X * xiShiftedBoundaryShiftedEuler 1 p)) := by
  simp only [xiShiftedBoundaryShiftedEuler, Polynomial.derivative_mul,
    Polynomial.derivative_X, one_mul, C_1, Polynomial.smul_eq_C_mul]
  have hC : C (2 : ℝ) = (2 : Polynomial ℝ) := by
    ext n
    cases n <;> simp
  rw [hC]
  ring

/-- **Odd-to-even adaptive shear law.** The odd crossing differentiates into an even bilinear
landing selected by the Euler source connection. -/
theorem hasDerivAt_xiShiftedMomentInner_oddCrossing_eq_adaptiveShear
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) :
    HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re) p (X * p))
      (-2 * HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (X * p) (X * xiShiftedBoundaryShiftedEuler 1 p)) y := by
  have h := hasDerivAt_xiShiftedMomentFunctional_sourceConnection
    hy (p * (X * p))
  rw [adaptiveShear_polynomial_identity,
    HTGeometry.momentFunctional_smul] at h
  simpa only [HTGeometry.momentInner_def, neg_mul] using h

/-- The odd bilinear crossing is exactly the completed consecutive aggregate of the coefficient
packet of `p²`, with base order one. -/
theorem xiShiftedCompletedMomentAggregate_oddPacket_eq_momentInner
    (y : ℝ) (p : Polynomial ℝ) :
    xiShiftedCompletedMomentAggregate y 1
        (xiShiftedOddCrossingCoefficientPacket p) =
      HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re) p (X * p) := by
  let N := (p ^ (2 : ℕ)).natDegree + 1
  let c : Fin N → ℝ := xiShiftedOddCrossingCoefficientPacket p
  have hc : Polynomial.ofFn N c = p ^ (2 : ℕ) := by
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  have hprod : X * Polynomial.ofFn N c = p * (X * p) := by
    rw [hc]
    ring
  change xiShiftedCompletedMomentAggregate y 1 c = _
  rw [HTGeometry.momentInner_def, ← hprod]
  have hsum :
      HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (X * Polynomial.ofFn N c) =
        ∑ j : Fin N,
          c j * (xiShiftedReciprocalMoment y ((j : ℕ) + 1)).re := by
    rw [Polynomial.ofFn_eq_sum_monomial, Finset.mul_sum]
    rw [HTGeometry.momentFunctional_finset_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [X_mul_monomial, HTGeometry.momentFunctional_monomial]
  rw [hsum]
  simp only [xiShiftedCompletedMomentAggregate]
  apply Finset.sum_congr rfl
  intro j _
  rw [show 1 + (j : ℕ) = (j : ℕ) + 1 by omega]

/-- The source-selected successor aggregate is exactly twice the even Euler-adaptive shear. -/
theorem xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_two_shear
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) :
    xiShiftedCompletedMomentAggregate y 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket p)) =
      2 * HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (X * p) (X * xiShiftedBoundaryShiftedEuler 1 p) := by
  let c := xiShiftedOddCrossingCoefficientPacket p
  have haggregate := hasDerivAt_xiShiftedCompletedMomentAggregate hy 1 c
  have hfun :
      (fun v => xiShiftedCompletedMomentAggregate v 1 c) =
        (fun v => HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment v k).re) p (X * p)) := by
    funext v
    exact xiShiftedCompletedMomentAggregate_oddPacket_eq_momentInner v p
  rw [hfun] at haggregate
  have hshear :=
    hasDerivAt_xiShiftedMomentInner_oddCrossing_eq_adaptiveShear hy p
  have hderiv := haggregate.unique hshear
  change -xiShiftedCompletedMomentAggregate y 2
      (xiShiftedBoundaryAdaptiveMidpointCoefficients 1 c) =
    -2 * HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re)
      (X * p) (X * xiShiftedBoundaryShiftedEuler 1 p) at hderiv
  change xiShiftedCompletedMomentAggregate y 2
      (xiShiftedBoundaryAdaptiveMidpointCoefficients 1 c) = _
  linarith

/-- The intrinsic aperture crossing has the same source-first adaptive shear landing. -/
theorem hasDerivAt_xiShiftedAperturePairGap_oddCrossing_eq_adaptiveShear
    {y : ℝ} (hy : 0 < y) (p : Polynomial ℝ) :
    HasDerivAt
      (fun v => xiShiftedAperturePairGap v p (X * p))
      (-2 * xiShiftedAperturePairGap y
        (X * p) (X * xiShiftedBoundaryShiftedEuler 1 p)) y := by
  rw [xiShiftedAperturePairGap_eq_momentInner hy]
  have h := hasDerivAt_xiShiftedMomentInner_oddCrossing_eq_adaptiveShear
    hy p
  apply h.congr_of_eventuallyEq
  filter_upwards [tendsto_id.eventually_const_lt hy] with v hv
  exact xiShiftedAperturePairGap_eq_momentInner hv p (X * p)

/-- **Pre-aggregation arithmetic landing.** On the Euler ray, odd crossing current differentiates
into the sum of archimedean and Chebyshev-discrepancy pairings on the even adaptive shear. -/
theorem hasDerivAt_xiShiftedAperturePairGap_oddCrossing_eq_sourceShear
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) :
    HasDerivAt
      (fun y => xiShiftedAperturePairGap y p (X * p))
      (-2 *
        (xiShiftedApertureArchimedeanSourcePair w
            (X * p) (X * xiShiftedBoundaryShiftedEuler 1 p) +
          xiShiftedApertureDiscrepancySourcePair w
            (X * p) (X * xiShiftedBoundaryShiftedEuler 1 p))) (w ^ (2 : ℕ)) := by
  have h :=
    hasDerivAt_xiShiftedAperturePairGap_oddCrossing_eq_adaptiveShear
      (sq_pos_of_pos (by linarith : 0 < w)) p
  rw [xiShiftedAperturePairGap_eq_archimedeanSourcePair_add_discrepancySourcePair
    hw] at h
  exact h

/-- **Zero-free arithmetic shear law.** In the endpoint convergence window, the adaptive even
shear is expressed entirely by the absolutely convergent normalized prime--Gamma
negative-binomial source tower. No Xi zero coordinate occurs on the derivative side. -/
theorem hasDerivAt_xiShiftedAperturePairGap_oddCrossing_eq_primeArchAdaptiveShear
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2) (p : Polynomial ℝ) :
    HasDerivAt
      (fun v => xiShiftedAperturePairGap v p (X * p))
      (-2 * HTGeometry.momentInner
        (fun k => (primeArchShiftedReciprocalMoment y k).re)
        (X * p) (X * xiShiftedBoundaryShiftedEuler 1 p)) y := by
  have h :=
    hasDerivAt_xiShiftedAperturePairGap_oddCrossing_eq_adaptiveShear hy p
  rw [xiShiftedAperturePairGap_eq_primeArchMomentInner hy hymax] at h
  exact h

/-- The completed mixed successor aggregate is twice the source-only prime--Gamma adaptive shear
throughout the negative-binomial window. -/
theorem xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_two_primeArchShear
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2) (p : Polynomial ℝ) :
    xiShiftedCompletedMomentAggregate y 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket p)) =
      2 * HTGeometry.momentInner
        (fun k => (primeArchShiftedReciprocalMoment y k).re)
        (X * p) (X * xiShiftedBoundaryShiftedEuler 1 p) := by
  rw [xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_two_shear hy]
  congr 1
  rw [← xiShiftedAperturePairGap_eq_momentInner hy,
    xiShiftedAperturePairGap_eq_primeArchMomentInner hy hymax]

/-- On the odd packet, the successor `P^sharp` carrier is exactly the mixed factorial amplitude
`Q`; this specializes the one-Euler midpoint identity to the bilinear contact current. -/
theorem xiShiftedBoundaryFactorialCarrierPolynomial_adaptiveOddPacket_eq_mixed
    (p : Polynomial ℝ) (t : ℝ) :
    xiShiftedBoundaryFactorialCarrierPolynomial 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket p)) t =
      xiShiftedBoundaryMixedFactorialCarrierPolynomial 1
        (xiShiftedOddCrossingCoefficientPacket p) t := by
  exact xiShiftedBoundaryFactorialCarrierPolynomial_succ_midpoint_eq_mixed
    1 (xiShiftedOddCrossingCoefficientPacket p) t

/-- Completed mixed-amplitude aggregate equals twice the pre-aggregation arithmetic shear. -/
theorem xiShiftedCompletedAdaptiveOddPacketSource_eq_two_sourceShear
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) :
    xiShiftedBoundaryArchimedeanAggregate w 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket p)) +
      xiShiftedHankelBoundaryRadialDiscrepancy w 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket p)) =
      2 *
        (xiShiftedApertureArchimedeanSourcePair w
            (X * p) (X * xiShiftedBoundaryShiftedEuler 1 p) +
          xiShiftedApertureDiscrepancySourcePair w
            (X * p) (X * xiShiftedBoundaryShiftedEuler 1 p)) := by
  have h :=
    xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_two_shear
      (sq_pos_of_pos (by linarith : 0 < w)) p
  rw [xiShiftedCompletedMomentAggregate_sq_eq_boundaryCompletedAggregate
      (by linarith : 0 < w),
    xiShiftedBoundaryCompletedAggregate_eq_archimedean_add_radialDiscrepancy hw,
    ← xiShiftedAperturePairGap_eq_momentInner
      (sq_pos_of_pos (by linarith : 0 < w)),
    xiShiftedAperturePairGap_eq_archimedeanSourcePair_add_discrepancySourcePair hw]
    at h
  exact h

/-- **Adaptive mixed-amplitude completed source law.** The odd Γ-oriented crossing is consumed
before reflection aggregation and lands on the completed `P^sharp` successor packet. Its radial
carrier is the mixed amplitude `Q`, while its bilinear realization is the even adaptive shear. -/
theorem hasDerivAt_xiShiftedAperturePairGap_oddCrossing_eq_completedMixedSource
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) :
    HasDerivAt
      (fun y => xiShiftedAperturePairGap y p (X * p))
      (-(xiShiftedBoundaryArchimedeanAggregate w 2
          (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
            (xiShiftedOddCrossingCoefficientPacket p)) +
        xiShiftedHankelBoundaryRadialDiscrepancy w 2
          (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
            (xiShiftedOddCrossingCoefficientPacket p)))) (w ^ (2 : ℕ)) := by
  have h :=
    hasDerivAt_xiShiftedAperturePairGap_oddCrossing_eq_sourceShear hw p
  rw [xiShiftedCompletedAdaptiveOddPacketSource_eq_two_sourceShear hw p]
  simpa only [neg_mul] using h

end

end RHTower
