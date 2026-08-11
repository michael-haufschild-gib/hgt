import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveNullGaugeSourceLaw

/-!
# Adaptive rational–Gamma/von Mangoldt source formation

The completed adaptive mixed-amplitude packet is formed before reflection aggregation as the
difference of two literal arithmetic sources:

* a rational–Gamma continuum source, equal to the archimedean jet plus Lebesgue mass of the
  adaptive reverse-Bessel kernel;
* the labelwise von Mangoldt source, carrying the same kernel at every prime power.

For the packet selected by a polynomial amplitude `A`, the common kernel contains the mixed
factorial carrier `Q₁,c(A)` itself.  Thus neither source is a fixed reporter: changing `A` changes
both formations before their final subtraction.
-/

open Complex Matrix MeasureTheory Set Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Rational–Gamma component of one normalized completed reverse-Bessel source moment. -/
def normalizedRationalGammaSourceMoment (n : ℕ) (w : ℝ) : ℝ :=
  (squaredXiAlternatingRationalGammaJetPolynomial n (w : ℂ)).re /
    completedSourceMomentScale n w

/-- Labelled von Mangoldt component of one normalized completed reverse-Bessel source moment. -/
def normalizedVonMangoldtSourceMoment (n : ℕ) (w : ℝ) : ℝ :=
  (squaredXiPrimeJetPolynomial n (w : ℂ)).re /
    completedSourceMomentScale n w

/-- Normalized completion is literally rational–Gamma source minus von Mangoldt source. -/
theorem normalizedCompletedSourceMoment_eq_rationalGamma_sub_vonMangoldt
    (n : ℕ) {w : ℝ} (hw : 1 / 2 < w) :
    normalizedCompletedSourceMoment n w =
      normalizedRationalGammaSourceMoment n w -
        normalizedVonMangoldtSourceMoment n w := by
  rw [normalizedCompletedSourceMoment, normalizedRationalGammaSourceMoment,
    normalizedVonMangoldtSourceMoment,
    completedSourceJet_eq_rationalGamma_sub_prime n hw]
  ring

/-- Rational–Gamma formation of an arbitrary finite consecutive source packet. -/
def xiShiftedBoundaryRationalGammaAggregate
    (w : ℝ) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, c j * normalizedRationalGammaSourceMoment (r + (j : ℕ)) w

/-- Von Mangoldt formation of an arbitrary finite consecutive source packet. -/
def xiShiftedBoundaryVonMangoldtAggregate
    (w : ℝ) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, c j * normalizedVonMangoldtSourceMoment (r + (j : ℕ)) w

/-- Every completed packet is the difference of its two source formations before any
reflection aggregation. -/
theorem xiShiftedBoundaryCompletedAggregate_eq_rationalGamma_sub_vonMangoldt
    {w : ℝ} (hw : 1 / 2 < w) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    xiShiftedBoundaryCompletedAggregate w r c =
      xiShiftedBoundaryRationalGammaAggregate w r c -
        xiShiftedBoundaryVonMangoldtAggregate w r c := by
  simp only [xiShiftedBoundaryCompletedAggregate,
    xiShiftedBoundaryRationalGammaAggregate,
    xiShiftedBoundaryVonMangoldtAggregate,
    normalizedCompletedSourceMoment_eq_rationalGamma_sub_vonMangoldt _ hw,
    mul_sub, Finset.sum_sub_distrib]

/-- One normalized von Mangoldt source moment is the Chebyshev–Stieltjes integral of the
corresponding normalized reverse-Bessel kernel. -/
theorem normalizedVonMangoldtSourceMoment_eq_integral
    (n : ℕ) {w : ℝ} (hw : 1 / 2 < w) :
    normalizedVonMangoldtSourceMoment n w =
      ∫ x, radialBesselKernel n (1 / 2 + w) x /
        completedSourceMomentScale n w ∂chebyshevPsiStieltjes.measure := by
  rw [normalizedVonMangoldtSourceMoment,
    squaredXiPrimeJetPolynomial_re_eq n hw,
    MeasureTheory.integral_div,
    integral_radialBesselKernel_chebyshev (by linarith : 1 < 1 / 2 + w)]

/-- The finite von Mangoldt packet is one integral of the packet-preserving radial kernel. -/
theorem xiShiftedBoundaryVonMangoldtAggregate_eq_integral
    {w : ℝ} (hw : 1 / 2 < w) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    xiShiftedBoundaryVonMangoldtAggregate w r c =
      ∫ x, xiShiftedHankelBoundaryRadialKernel w r c x
        ∂chebyshevPsiStieltjes.measure := by
  simp only [xiShiftedBoundaryVonMangoldtAggregate,
    xiShiftedHankelBoundaryRadialKernel]
  have hInt (j : Fin N) : Integrable
      (fun x : ℝ => c j * radialBesselKernel (r + (j : ℕ)) (1 / 2 + w) x /
        completedSourceMomentScale (r + (j : ℕ)) w)
      chebyshevPsiStieltjes.measure := by
    have hs : 1 < 1 / 2 + w := by linarith
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_chebyshevPsiStieltjes
        (summable_vonMangoldt_mul_norm_radialBesselKernel
          (n := r + (j : ℕ)) hs)).const_mul
            (c j / completedSourceMomentScale (r + (j : ℕ)) w)
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hInt j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [normalizedVonMangoldtSourceMoment_eq_integral (r + (j : ℕ)) hw,
    MeasureTheory.integral_div]
  have hpoint :
      (fun a : ℝ => c j * radialBesselKernel (r + (j : ℕ)) (1 / 2 + w) a /
        completedSourceMomentScale (r + (j : ℕ)) w) =
      (fun a : ℝ =>
        (c j / completedSourceMomentScale (r + (j : ℕ)) w) *
          radialBesselKernel (r + (j : ℕ)) (1 / 2 + w) a) := by
    funext a
    ring
  rw [hpoint, MeasureTheory.integral_const_mul]
  ring

/-- The von Mangoldt packet retains every arithmetic label until the final absolutely convergent
sum. -/
theorem xiShiftedBoundaryVonMangoldtAggregate_eq_labelwise
    {w : ℝ} (hw : 1 / 2 < w) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    xiShiftedBoundaryVonMangoldtAggregate w r c =
      ∑' m : ℕ, (ArithmeticFunction.vonMangoldt m : ℝ) *
        xiShiftedHankelBoundaryRadialKernel w r c (m : ℝ) := by
  rw [xiShiftedBoundaryVonMangoldtAggregate_eq_integral hw]
  exact integral_chebyshevPsiStieltjes
    (integrable_xiShiftedHankelBoundaryRadialKernel_chebyshev hw r c)

/-- Rational–Gamma formation is exactly the archimedean jet plus Lebesgue formation of the same
packet-preserving radial kernel. -/
theorem xiShiftedBoundaryRationalGammaAggregate_eq_archimedean_add_lebesgue
    {w : ℝ} (hw : 1 / 2 < w) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    xiShiftedBoundaryRationalGammaAggregate w r c =
      xiShiftedBoundaryArchimedeanAggregate w r c +
        ∫ x in Ioi (1 : ℝ), xiShiftedHankelBoundaryRadialKernel w r c x := by
  have hcompleted :=
    xiShiftedBoundaryCompletedAggregate_eq_archimedean_add_radialDiscrepancy
      hw r c
  have hsource :=
    xiShiftedBoundaryCompletedAggregate_eq_rationalGamma_sub_vonMangoldt
      hw r c
  rw [xiShiftedHankelBoundaryRadialDiscrepancy,
    ← xiShiftedBoundaryVonMangoldtAggregate_eq_integral hw r c] at hcompleted
  linarith

/-- Explicit common source kernel selected by the adaptive amplitude `A`.  The mixed factorial
carrier is formed inside the Gamma integral, before Lebesgue or von Mangoldt aggregation. -/
def xiShiftedAdaptiveMixedGammaKernel (w : ℝ) (A : Polynomial ℝ) (x : ℝ) : ℝ :=
  x ^ (-(1 / 2 + w)) / ((2 : ℝ) ^ 2 * w ^ 5) *
    ∫ u in Ioi (0 : ℝ),
      Real.exp (-u) * (u * (w * Real.log x + u / 2)) ^ 2 *
        xiShiftedBoundaryMixedFactorialCarrierPolynomial 1
          (xiShiftedOddCrossingCoefficientPacket A)
          (u * (w * Real.log x + u / 2) / (2 * w ^ 2))

/-- The adaptive successor packet's radial kernel is pointwise the explicit mixed-amplitude
source kernel. -/
theorem xiShiftedHankelBoundaryRadialKernel_adaptiveOddPacket_eq_mixedGammaKernel
    {w : ℝ} (hw : w ≠ 0) (A : Polynomial ℝ) (x : ℝ) :
    xiShiftedHankelBoundaryRadialKernel w 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket A)) x =
      xiShiftedAdaptiveMixedGammaKernel w A x := by
  rw [xiShiftedHankelBoundaryRadialKernel_eq_factorialCarrierIntegral
    hw 2]
  simp only [xiShiftedAdaptiveMixedGammaKernel]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  simp only [xiShiftedBoundaryFactorialCarrierPolynomial_adaptiveOddPacket_eq_mixed]

/-- The adaptive von Mangoldt formation is the actual prime-power sum of one endogenous mixed
kernel. -/
theorem xiShiftedBoundaryVonMangoldtAggregate_adaptiveOddPacket_eq_labelwise
    {w : ℝ} (hw : 1 / 2 < w) (A : Polynomial ℝ) :
    xiShiftedBoundaryVonMangoldtAggregate w 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket A)) =
      ∑' m : ℕ, (ArithmeticFunction.vonMangoldt m : ℝ) *
        xiShiftedAdaptiveMixedGammaKernel w A (m : ℝ) := by
  rw [xiShiftedBoundaryVonMangoldtAggregate_eq_labelwise hw]
  apply tsum_congr
  intro m
  rw [xiShiftedHankelBoundaryRadialKernel_adaptiveOddPacket_eq_mixedGammaKernel
    (ne_of_gt (by linarith : 0 < w))]

/-- Rational–Gamma formation of the adaptive packet is the archimedean packet plus the Lebesgue
formation of the same endogenous mixed kernel. -/
theorem xiShiftedBoundaryRationalGammaAggregate_adaptiveOddPacket_eq_archimedean_add_lebesgue
    {w : ℝ} (hw : 1 / 2 < w) (A : Polynomial ℝ) :
    xiShiftedBoundaryRationalGammaAggregate w 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket A)) =
      xiShiftedBoundaryArchimedeanAggregate w 2
          (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
            (xiShiftedOddCrossingCoefficientPacket A)) +
        ∫ x in Ioi (1 : ℝ), xiShiftedAdaptiveMixedGammaKernel w A x := by
  rw [xiShiftedBoundaryRationalGammaAggregate_eq_archimedean_add_lebesgue hw]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  rw [xiShiftedHankelBoundaryRadialKernel_adaptiveOddPacket_eq_mixedGammaKernel
    (ne_of_gt (by linarith : 0 < w))]

/-- Fully source-native completed adaptive formation.  Both sides use the same amplitude-dependent
kernel; only the source law (continuum versus von Mangoldt labels) differs. -/
def xiShiftedAdaptiveMixedCompletedArithmeticSource
    (w : ℝ) (A : Polynomial ℝ) : ℝ :=
  xiShiftedBoundaryArchimedeanAggregate w 2
      (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
        (xiShiftedOddCrossingCoefficientPacket A)) +
    (∫ x in Ioi (1 : ℝ), xiShiftedAdaptiveMixedGammaKernel w A x) -
      ∑' m : ℕ, (ArithmeticFunction.vonMangoldt m : ℝ) *
        xiShiftedAdaptiveMixedGammaKernel w A (m : ℝ)

/-- **Adaptive mixed-amplitude arithmetic source law.**  The completed `P^sharp` successor packet
is exactly rational–Gamma continuum formation minus the labelwise von Mangoldt formation of the
same admitted mixed kernel.  No fixed reporter or divisor orientation map occurs. -/
theorem xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource
    {w : ℝ} (hw : 1 / 2 < w) (A : Polynomial ℝ) :
    xiShiftedCompletedMomentAggregate (w ^ 2) 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket A)) =
      xiShiftedAdaptiveMixedCompletedArithmeticSource w A := by
  rw [xiShiftedCompletedMomentAggregate_sq_eq_boundaryCompletedAggregate
      (by linarith : 0 < w),
    xiShiftedBoundaryCompletedAggregate_eq_rationalGamma_sub_vonMangoldt hw,
    xiShiftedBoundaryRationalGammaAggregate_adaptiveOddPacket_eq_archimedean_add_lebesgue
      hw,
    xiShiftedBoundaryVonMangoldtAggregate_adaptiveOddPacket_eq_labelwise hw]
  rfl

/-- At an admitted flat face, the null-gauge producer lands directly in the two arithmetic source
formations.  Admission selects `A`; it is not reconstructed by a reporter after aggregation. -/
theorem two_mul_coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_arithmeticSource
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect (w ^ 2) c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    2 * PowerSeries.coeff 2
        (xiShiftedAdaptiveNullGaugeSourceSeries
          (xiShiftedHankelBoundaryPadeDefect (w ^ 2) c) A (n + m)) =
      ((2 * (n + m) + 1 : ℕ) : ℝ) *
        xiShiftedAdaptiveMixedCompletedArithmeticSource w A := by
  dsimp only
  rw [two_mul_coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_completedPacket
      (sq_pos_of_pos (by linarith : 0 < w)) c hlast hzero,
    xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource hw]

/-- Away from the original flat face, the producer is the transported null-gauge coefficient
minus its exact lower-flag memory.  That corrected, admission-sensitive object—not the raw
coefficient—is the rational–Gamma/von Mangoldt source difference. -/
theorem two_mul_coeff_two_xiShiftedAdaptiveNullGaugeMomentSourceSeries_sub_lowerResidual_eq_arithmeticSource
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    2 * PowerSeries.coeff 2
          (xiShiftedAdaptiveNullGaugeSourceSeries
            (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) A (n + m)) -
        2 * HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re)
          (xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A (n + m)) =
      ((2 * (n + m) + 1 : ℕ) : ℝ) *
        xiShiftedAdaptiveMixedCompletedArithmeticSource w A := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hA : A.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hAdeg : A.natDegree = n + m := by
    dsimp only [A]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m), hPdeg,
      Polynomial.natDegree_X_pow]
  rw [two_mul_coeff_two_xiShiftedAdaptiveNullGaugeMomentSourceSeries_sub_lowerResidual_eq_completedPacket
      (sq_pos_of_pos (by linarith : 0 < w)) hA hAdeg,
    xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource hw]

/-- Bilinear form of the same law: actual adaptive shear is formed by the two arithmetic sources
before their subtraction and reflection aggregation. -/
theorem two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource
    {w : ℝ} (hw : 1 / 2 < w) (A : Polynomial ℝ) :
    2 * HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re)
        (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A) =
      xiShiftedAdaptiveMixedCompletedArithmeticSource w A := by
  rw [← xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_two_shear
      (sq_pos_of_pos (by linarith : 0 < w)) A,
    xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource hw]

end

end RHTower
