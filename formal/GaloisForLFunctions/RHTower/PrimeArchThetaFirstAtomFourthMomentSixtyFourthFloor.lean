import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomWardObstructionScaleQuadrature

/-!
# Sixty-fourth-mesh floor for the first theta atom's fourth moment

Summing the existing 64-cell lower certificates through `7 / 8` sharpens the
dominant theta atom's exact fourth-moment floor to `2951 / 10^(6 : ℕ)`.  Integral
monotonicity then transports this rational certificate to the full positive
half-line moment.  No zero data or numerical integration enters.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators Interval

namespace RHTower

noncomputable section

/- Exact 64-cell rational lower certificate for the dominant atom's fourth moment. -/
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
theorem twoThousandNineHundredFiftyOne_div_oneMillion_lt_sum_firstAtomFourthLowerMass64 :
    (2951 / 1000000 : ℝ) <
      ∑ j ∈ Finset.range 56,
        thetaCuspFirstAtomRawLowerIntervalMass64 2 j := by
  norm_num [thetaCuspFirstAtomRawLowerIntervalMass64,
    thetaCuspPowAffineSubTaylorMass, thetaCuspIntervalPowSubMass,
    thetaCuspFirstSourceLowerAffineConstant64,
    thetaCuspFirstSourceLowerAffineSlope64,
    thetaCuspFirstRateUpperSlope64,
    thetaCuspFirstRateUpperEndpointCertificate64,
    thetaCuspFirstRateUpper64, thetaCuspSixtyFourthExpUpperChord,
    thetaCuspThirtySecondExpUpper, thetaCuspThirtySecondExpLower,
    eval_expNegTruncPoly, Nat.choose, Finset.sum_range_succ]

/-- The certified 64-cell mass is a lower bound for the full dominant-atom fourth moment. -/
theorem sum_firstAtomFourthLowerMass64_le_thetaCuspAtomRawEvenMoment_two_one :
    (∑ j ∈ Finset.range 56,
        thetaCuspFirstAtomRawLowerIntervalMass64 2 j) ≤
      thetaCuspAtomRawEvenMoment 2 1 := by
  let f : ℝ → ℝ := fun x => 2 * (x ^ (4 : ℕ) * thetaCuspSourceTerm x 1)
  have hfcont : Continuous f := by
    dsimp only [f]
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hfint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_pow_mul_thetaCuspSourceTerm 2 1).const_mul 2
    apply h.congr
    filter_upwards [] with x
    dsimp only [f]
  have hfnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (by norm_num) <|
      mul_nonneg (pow_nonneg hx.le _) (thetaCuspSourceTerm_nonneg_of_pos hx 1)
  have hsegment (j : ℕ) (hj : j < 56) :
      thetaCuspFirstAtomRawLowerIntervalMass64 2 j ≤
        ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x := by
    rw [← intervalIntegral_thetaCuspFirstAtomRawLowerCertificate64_eq_mass]
    apply intervalIntegral.integral_mono_on
    · push_cast
      linarith
    · have hcertcont : Continuous
          (thetaCuspFirstAtomRawLowerCertificate64 2 j) := by
        unfold thetaCuspFirstAtomRawLowerCertificate64
          thetaCuspSixtyFourthExpLowerTangent thetaCuspExpTaylorFive
        fun_prop
      exact hcertcont.intervalIntegrable _ _
    · exact hfcont.intervalIntegrable _ _
    · intro x hx
      exact thetaCuspFirstAtomRawLowerCertificate64_le_density hj hx
  have hsum :
      (∑ j ∈ Finset.range 56, thetaCuspFirstAtomRawLowerIntervalMass64 2 j) ≤
        ∑ j ∈ Finset.range 56,
          ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x := by
    exact Finset.sum_le_sum fun j hj => hsegment j (Finset.mem_range.mp hj)
  have hjoin :
      (∑ j ∈ Finset.range 56,
          ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x) =
        ∫ x in (0 : ℝ)..7 / 8, f x := by
    convert
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := f) (a := fun k : ℕ => (k : ℝ) / 64) (n := 56) (μ := volume)
        (fun k _ => hfcont.intervalIntegrable _ _)) using 1 <;> norm_num
  have hwindow : (∫ x in (0 : ℝ)..7 / 8, f x) ≤ ∫ x in Ioi 0, f x := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact setIntegral_mono_set hfint hfnonneg
      (Filter.Eventually.of_forall fun x hx => hx.1)
  have hraw : (∫ x in Ioi 0, f x) = thetaCuspAtomRawEvenMoment 2 1 := by
    rw [thetaCuspAtomRawEvenMoment]
    dsimp only [f]
    rw [← integral_const_mul]
  exact hsum.trans (hjoin.le.trans (hwindow.trans hraw.le))

/-- **Sharpened unconditional dominant-atom fourth-moment floor.** -/
theorem twoThousandNineHundredFiftyOne_div_oneMillion_lt_thetaCuspAtomRawEvenMoment_two_one :
    (2951 / 1000000 : ℝ) < thetaCuspAtomRawEvenMoment 2 1 :=
  twoThousandNineHundredFiftyOne_div_oneMillion_lt_sum_firstAtomFourthLowerMass64.trans_le
    sum_firstAtomFourthLowerMass64_le_thetaCuspAtomRawEvenMoment_two_one

end

end RHTower
