import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryReverseBesselCarrier

/-!
# Factorial Euler source connection for adaptive shifted-Xi packets

The squared-factorial carrier does not merely relate adjacent normalizations.  Actual mass
differentiation selects the unsquared midpoint between them.  For

`P_r(T) = sum_j c_j T^j / ((r+j)!)^2`

and `M_r(c)_j = (r+j+1)c_j`, define

`Q_r(T) = sum_j c_j T^j / ((r+j)!(r+j+1)!)`.

Then `Q_r = E_(r+1) P_(r+1) = P_(r+1,M_r c)` and
`P_r = E_(r+1) Q_r`.  More importantly, for the actual completed moment aggregate

`S_(r,c)(y) = sum_j c_j Re m_(r+j)(y)`

one has the source-first law

`S_(r,c)'(y) = -S_(r+1,M_r c)(y)`.

On the Euler source ray the landing aggregate splits before reflection into its archimedean and
Lebesgue-minus-Chebyshev channels.  Its radial channel is the positive Gamma carrier tested
against `Q_r`, not against a fixed reporter chosen after aggregation.
-/

open Complex Matrix MeasureTheory Set Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Coefficient adaptation forced by one completed-moment mass derivative. -/
def xiShiftedBoundaryAdaptiveMidpointCoefficients
    (r : ℕ) {N : ℕ} (c : Fin N → ℝ) (j : Fin N) : ℝ :=
  ((r + (j : ℕ) + 1 : ℕ) : ℝ) * c j

/-- Polynomial-valued squared-factorial carrier. -/
def xiShiftedBoundaryFactorialCarrier
    (r : ℕ) {N : ℕ} (c : Fin N → ℝ) : Polynomial ℝ :=
  ∑ j : Fin N,
    monomial (j : ℕ) (c j / (((r + (j : ℕ)).factorial : ℝ) ^ 2))

/-- Shifted Euler connection on polynomial amplitudes. -/
def xiShiftedBoundaryShiftedEuler
    (a : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  X * P.derivative + C a * P

/-- The actual one-Euler mixed factorial amplitude. -/
def xiShiftedBoundaryMixedFactorialCarrierPolynomial
    (r : ℕ) {N : ℕ} (c : Fin N → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin N,
    (c j /
      (((r + (j : ℕ)).factorial : ℝ) *
        ((r + (j : ℕ) + 1).factorial : ℝ))) * t ^ (j : ℕ)

/-- Actual shifted reciprocal-Xi moment aggregate before source presentation. -/
def xiShiftedCompletedMomentAggregate
    (y : ℝ) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N,
    c j * (xiShiftedReciprocalMoment y (r + (j : ℕ))).re

/-- Completed prime--Gamma presentation of an arbitrary consecutive adaptive aggregate. -/
def xiShiftedBoundaryCompletedAggregate
    (w : ℝ) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, c j * normalizedCompletedSourceMoment (r + (j : ℕ)) w

/-- Archimedean channel of the arbitrary-base completed aggregate. -/
def xiShiftedBoundaryArchimedeanAggregate
    (w : ℝ) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, c j * normalizedArchimedeanSourceMoment (r + (j : ℕ)) w

/-- Evaluation recovers the existing function-valued `P^sharp` carrier. -/
theorem eval_xiShiftedBoundaryFactorialCarrier
    (r : ℕ) {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    (xiShiftedBoundaryFactorialCarrier r c).eval t =
      xiShiftedBoundaryFactorialCarrierPolynomial r c t := by
  simp only [xiShiftedBoundaryFactorialCarrier,
    xiShiftedBoundaryFactorialCarrierPolynomial, eval_finsetSum, eval_monomial]

private theorem xiShiftedBoundaryShiftedEuler_monomial
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
      push_cast
      ring
    · have hjk : j ≠ k := Ne.symm hk
      simp [hjk]

/-- One Euler step is exactly the source-selected midpoint coefficient adaptation. -/
theorem xiShiftedBoundaryShiftedEuler_factorialCarrier_succ
    (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    xiShiftedBoundaryShiftedEuler (r + 1 : ℕ)
        (xiShiftedBoundaryFactorialCarrier (r + 1) c) =
      xiShiftedBoundaryFactorialCarrier (r + 1)
        (xiShiftedBoundaryAdaptiveMidpointCoefficients r c) := by
  simp only [xiShiftedBoundaryShiftedEuler, xiShiftedBoundaryFactorialCarrier,
    map_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [xiShiftedBoundaryShiftedEuler_monomial]
  rw [show r + 1 + (j : ℕ) = r + (j : ℕ) + 1 by omega,
    Nat.factorial_succ]
  simp only [xiShiftedBoundaryAdaptiveMidpointCoefficients]
  congr 1
  push_cast
  field_simp [Nat.factorial_ne_zero]
  ring

/-- The second Euler step reaches the preceding squared-factorial carrier. -/
theorem xiShiftedBoundaryShiftedEuler_midpoint_succ
    (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    xiShiftedBoundaryShiftedEuler (r + 1 : ℕ)
        (xiShiftedBoundaryFactorialCarrier (r + 1)
          (xiShiftedBoundaryAdaptiveMidpointCoefficients r c)) =
      xiShiftedBoundaryFactorialCarrier r c := by
  simp only [xiShiftedBoundaryShiftedEuler, xiShiftedBoundaryFactorialCarrier,
    map_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [xiShiftedBoundaryShiftedEuler_monomial]
  rw [show r + 1 + (j : ℕ) = r + (j : ℕ) + 1 by omega,
    Nat.factorial_succ]
  simp only [xiShiftedBoundaryAdaptiveMidpointCoefficients]
  congr 1
  push_cast
  field_simp [Nat.factorial_ne_zero]
  ring

/-- The midpoint-adapted `P^sharp` is the mixed factorial amplitude `Q`. -/
theorem xiShiftedBoundaryFactorialCarrierPolynomial_succ_midpoint_eq_mixed
    (r : ℕ) {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    xiShiftedBoundaryFactorialCarrierPolynomial (r + 1)
        (xiShiftedBoundaryAdaptiveMidpointCoefficients r c) t =
      xiShiftedBoundaryMixedFactorialCarrierPolynomial r c t := by
  simp only [xiShiftedBoundaryFactorialCarrierPolynomial,
    xiShiftedBoundaryMixedFactorialCarrierPolynomial]
  apply Finset.sum_congr rfl
  intro j _
  rw [show r + 1 + (j : ℕ) = r + (j : ℕ) + 1 by omega,
    Nat.factorial_succ]
  simp only [xiShiftedBoundaryAdaptiveMidpointCoefficients]
  push_cast
  field_simp [Nat.factorial_ne_zero]

/-- **Source-first midpoint law.** Mass differentiation of every adaptive completed aggregate
lands on the same coefficient adaptation as one unsquared Euler step of `P^sharp`. -/
theorem hasDerivAt_xiShiftedCompletedMomentAggregate
    {y : ℝ} (hy : 0 < y) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    HasDerivAt (fun v => xiShiftedCompletedMomentAggregate v r c)
      (-xiShiftedCompletedMomentAggregate y (r + 1)
        (xiShiftedBoundaryAdaptiveMidpointCoefficients r c)) y := by
  have hterm (j : Fin N) :
      HasDerivAt
        (fun v => c j * (xiShiftedReciprocalMoment v (r + (j : ℕ))).re)
        (-(c j * (((r + (j : ℕ) : ℕ) : ℝ) + 1) *
          (xiShiftedReciprocalMoment y (r + (j : ℕ) + 1)).re)) y := by
    simpa only [neg_mul, mul_neg, mul_assoc] using
      (hasDerivAt_re_xiShiftedReciprocalMoment hy
        (r + (j : ℕ))).const_mul (c j)
  have hsum : HasDerivAt
      (∑ j : Fin N,
        fun v => c j * (xiShiftedReciprocalMoment v (r + (j : ℕ))).re)
      (∑ j : Fin N,
        -(c j * (((r + (j : ℕ) : ℕ) : ℝ) + 1) *
          (xiShiftedReciprocalMoment y (r + (j : ℕ) + 1)).re)) y :=
    HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
    (fun j _ => hterm j)
  have htarget :
      -xiShiftedCompletedMomentAggregate y (r + 1)
          (xiShiftedBoundaryAdaptiveMidpointCoefficients r c) =
        ∑ j : Fin N,
          -(c j * (((r + (j : ℕ) : ℕ) : ℝ) + 1) *
            (xiShiftedReciprocalMoment y (r + (j : ℕ) + 1)).re) := by
    rw [xiShiftedCompletedMomentAggregate]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [xiShiftedBoundaryAdaptiveMidpointCoefficients]
    rw [show r + 1 + (j : ℕ) = r + (j : ℕ) + 1 by omega]
    push_cast
    ring
  have hfun :
      (fun v => xiShiftedCompletedMomentAggregate v r c) =
        ∑ j : Fin N,
          fun v => c j * (xiShiftedReciprocalMoment v (r + (j : ℕ))).re := by
    funext v
    simp only [xiShiftedCompletedMomentAggregate, Finset.sum_apply]
  rw [htarget]
  rw [hfun]
  exact hsum

/-- The divisor-moment aggregate and completed-source aggregate are identical at `y=w^2`. -/
theorem xiShiftedCompletedMomentAggregate_sq_eq_boundaryCompletedAggregate
    {w : ℝ} (hw : 0 < w) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    xiShiftedCompletedMomentAggregate (w ^ 2) r c =
      xiShiftedBoundaryCompletedAggregate w r c := by
  simp only [xiShiftedCompletedMomentAggregate, xiShiftedBoundaryCompletedAggregate]
  apply Finset.sum_congr rfl
  intro j _
  rw [normalizedCompletedSourceMoment_eq (r + (j : ℕ)) hw]

private theorem xiShiftedBoundaryDiscrepancyAggregate_eq_radialDiscrepancy
    {w : ℝ} (hw : 1 / 2 < w) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    (∑ j : Fin N,
      c j * normalizedChebyshevDiscrepancyMoment (r + (j : ℕ)) w) =
      xiShiftedHankelBoundaryRadialDiscrepancy w r c := by
  have hLeb (j : Fin N) : IntegrableOn
      (fun x : ℝ => c j * radialBesselKernel (r + (j : ℕ)) (1 / 2 + w) x /
        completedSourceMomentScale (r + (j : ℕ)) w) (Ioi (1 : ℝ)) := by
    have hs : 1 < 1 / 2 + w := by linarith
    change Integrable
      (fun x : ℝ => c j * radialBesselKernel (r + (j : ℕ)) (1 / 2 + w) x /
        completedSourceMomentScale (r + (j : ℕ)) w)
      (volume.restrict (Ioi (1 : ℝ)))
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (integrableOn_radialBesselKernel
        (n := r + (j : ℕ)) hs).const_mul
          (c j / completedSourceMomentScale (r + (j : ℕ)) w)
  have hCheb (j : Fin N) : Integrable
      (fun x : ℝ => c j * radialBesselKernel (r + (j : ℕ)) (1 / 2 + w) x /
        completedSourceMomentScale (r + (j : ℕ)) w)
      chebyshevPsiStieltjes.measure := by
    have hs : 1 < 1 / 2 + w := by linarith
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_chebyshevPsiStieltjes
        (summable_vonMangoldt_mul_norm_radialBesselKernel
          (n := r + (j : ℕ)) hs)).const_mul
            (c j / completedSourceMomentScale (r + (j : ℕ)) w)
  simp only [normalizedChebyshevDiscrepancyMoment,
    xiShiftedHankelBoundaryRadialDiscrepancy,
    xiShiftedHankelBoundaryRadialKernel]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hLeb j),
    MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hCheb j)]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [MeasureTheory.integral_div, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_div, MeasureTheory.integral_const_mul]
  ring

/-- The arbitrary-base completed aggregate splits into archimedean and arithmetic radial channels
without first compressing its adaptive coefficient packet. -/
theorem xiShiftedBoundaryCompletedAggregate_eq_archimedean_add_radialDiscrepancy
    {w : ℝ} (hw : 1 / 2 < w) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    xiShiftedBoundaryCompletedAggregate w r c =
      xiShiftedBoundaryArchimedeanAggregate w r c +
        xiShiftedHankelBoundaryRadialDiscrepancy w r c := by
  simp only [xiShiftedBoundaryCompletedAggregate,
    xiShiftedBoundaryArchimedeanAggregate,
    normalizedCompletedSourceMoment_eq_archimedean_add_discrepancy _ hw,
    mul_add, Finset.sum_add_distrib]
  rw [xiShiftedBoundaryDiscrepancyAggregate_eq_radialDiscrepancy hw]

/-- **Completed arithmetic midpoint landing.** At every Euler-source mass, derivative of the
adaptive moment aggregate is the negative completed prime--Gamma aggregate whose radial carrier
is the mixed amplitude `Q_r`.  Both source channels are retained before reflection aggregation. -/
theorem hasDerivAt_xiShiftedCompletedMomentAggregate_eq_midpointSource
    {w : ℝ} (hw : 1 / 2 < w) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    HasDerivAt (fun y => xiShiftedCompletedMomentAggregate y r c)
      (-(xiShiftedBoundaryArchimedeanAggregate w (r + 1)
          (xiShiftedBoundaryAdaptiveMidpointCoefficients r c) +
        xiShiftedHankelBoundaryRadialDiscrepancy w (r + 1)
          (xiShiftedBoundaryAdaptiveMidpointCoefficients r c))) (w ^ 2) := by
  have hmass := hasDerivAt_xiShiftedCompletedMomentAggregate
    (sq_pos_of_pos (by linarith : 0 < w)) r c
  rw [xiShiftedCompletedMomentAggregate_sq_eq_boundaryCompletedAggregate
      (by linarith : 0 < w),
    xiShiftedBoundaryCompletedAggregate_eq_archimedean_add_radialDiscrepancy hw]
    at hmass
  exact hmass

end

end RHTower
