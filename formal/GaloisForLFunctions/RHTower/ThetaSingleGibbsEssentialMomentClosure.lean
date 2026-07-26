import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity
import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity
import GaloisForLFunctions.RHTower.ThetaSingleGibbsLikelihoodSingleLossClosure

/-!
# Essential moment closure for the first theta Gibbs atom

The rational-box interface for the first Gibbs atom contains eighteen moment endpoints.  The
low-degree source certificate only needs five bounds on the actual Ward, Stein, and Morse
functionals.  Positivity of all remaining factors follows from the source measure: the first
three Ward moments are nonnegative, the Morse upper energy dominates the strictly positive
virial energy, and its quartic remainder is a positive combination of two polynomial squares.
-/

open Real MeasureTheory Set Polynomial

namespace RHTower

noncomputable section

/-- The first-atom Gibbs moment functional is integration against its positive half-line
density. -/
theorem momentFunctional_thetaCuspFirstAtomGibbs_eq_integral
    (p : Polynomial ℝ) :
    HTGeometry.momentFunctional
        (fun m => thetaCuspLiouvilleGibbsMoment m 1) p =
      ∫ x : ℝ in Ioi 0,
        p.eval x * thetaCuspLiouvilleGibbsAtom 1 x := by
  rw [HTGeometry.momentFunctional_eq_support_sum]
  have heval :
      (fun x : ℝ =>
          p.eval x * thetaCuspLiouvilleGibbsAtom 1 x) =
        fun x =>
          ∑ k ∈ p.support,
            p.coeff k *
              (x ^ k * thetaCuspLiouvilleGibbsAtom 1 x) := by
    funext x
    rw [eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heval, integral_finsetSum p.support]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_const_mul]
    rfl
  · intro k hk
    exact
      (integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
        k (X ^ 2) (n := 1) (by norm_num)).const_mul _

/-- Every polynomial square is nonnegative for the first-atom Gibbs moment functional. -/
theorem momentFunctional_thetaCuspFirstAtomGibbs_sq_nonneg
    (p : Polynomial ℝ) :
    0 ≤ HTGeometry.momentFunctional
      (fun m => thetaCuspLiouvilleGibbsMoment m 1) (p ^ 2) := by
  rw [momentFunctional_thetaCuspFirstAtomGibbs_eq_integral]
  apply integral_nonneg_of_ae
  filter_upwards with x
  simp only [eval_pow]
  apply mul_nonneg (sq_nonneg _)
  rw [thetaCuspLiouvilleGibbsAtom_apply]
  positivity

/-- The quartic Morse remainder is a positive combination of two Gibbs polynomial squares:

`x⁴(6 - 18x + 51x²/2 - 15x³ + 3x⁴)
  = 3/4 [x²(x-2)(2x-1)]² + 3/4 [x²(x-2)]²`.
-/
theorem thetaCuspFirstAtomMorseQuarticRemainder_nonneg :
    0 ≤
      6 * thetaCuspLiouvilleGibbsMoment 4 1 -
        18 * thetaCuspLiouvilleGibbsMoment 5 1 +
        (51 / 2 : ℝ) * thetaCuspLiouvilleGibbsMoment 6 1 -
        15 * thetaCuspLiouvilleGibbsMoment 7 1 +
        3 * thetaCuspLiouvilleGibbsMoment 8 1 := by
  let L : ℕ → ℝ := fun m => thetaCuspLiouvilleGibbsMoment m 1
  let r : Polynomial ℝ :=
    (6 : ℝ) • X ^ 4 + (-18 : ℝ) • X ^ 5 + (51 / 2 : ℝ) • X ^ 6 +
      (-15 : ℝ) • X ^ 7 + (3 : ℝ) • X ^ 8
  have hreval (x : ℝ) :
      r.eval x =
        (3 / 4 : ℝ) * (x ^ 2 * (x - 2) * (2 * x - 1)) ^ 2 +
          (3 / 4 : ℝ) * (x ^ 2 * (x - 2)) ^ 2 := by
    dsimp [r]
    simp only [eval_add, eval_smul, eval_pow, eval_X]
    ring
  have hr :
      0 ≤ HTGeometry.momentFunctional L r := by
    rw [momentFunctional_thetaCuspFirstAtomGibbs_eq_integral]
    apply integral_nonneg_of_ae
    filter_upwards with x
    rw [hreval]
    apply mul_nonneg
    · exact add_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg (by norm_num) (sq_nonneg _))
    · rw [thetaCuspLiouvilleGibbsAtom_apply]
      positivity
  have hrvalue :
      HTGeometry.momentFunctional L r =
        6 * L 4 - 18 * L 5 + (51 / 2 : ℝ) * L 6 -
          15 * L 7 + 3 * L 8 := by
    dsimp [r]
    simp only [HTGeometry.momentFunctional_add,
      HTGeometry.momentFunctional_smul,
      HTGeometry.momentFunctional_X_pow]
    ring
  rw [← hrvalue]
  exact hr

/-- The finite-moment Morse upper value is strictly positive without any numerical enclosure. -/
theorem thetaCuspFirstRadialQuadraticMorseSingleGibbsUpperValue_pos :
    0 < thetaCuspFirstRadialQuadraticMorseSingleGibbsUpperValue := by
  rw [← thetaCuspFirstRadialQuadraticMorseFiniteMomentUpperValue_eq_singleGibbs,
    ← thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy_eq_finiteMoments]
  exact lt_of_lt_of_le thetaCuspFirstRadialQuadraticVirialEnergy_pos
    thetaCuspFirstRadialQuadraticVirialEnergy_le_morseQuadraticEnvelopeUpperEnergy

/-- Hellinger fidelity between the two half-density endpoint channels gives a source-only
upper bound for the zeroth first-atom Ward moment.  The bound is wide enough for the
low-degree Gibbs certificate, so this quantity need not remain in its hypothesis interface. -/
theorem thetaCuspFirstAtomWardMoment_zero_le_sevenThousandNineHundredTwentySix_div_oneHundredThousand :
    thetaCuspFirstAtomWardMoment 0 ≤ (0.07926 : ℝ) := by
  have hsq :=
    thetaCuspAtomRawEvenMoment_zero_sq_add_orientation_sq_le_budget_sq
      (n := 1) (by norm_num)
  have hraw := thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 0
  have hW : 0 ≤ thetaCuspFirstAtomWardMoment 0 :=
    thetaCuspFirstAtomWardMoment_nonneg 0
  have he0 : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  have hcoef0 : 0 < 4 * Real.pi - 1 := by
    nlinarith [Real.pi_gt_three]
  have hbudget :
      ((4 * Real.pi - 1) * Real.exp (-Real.pi)) ^ 2 ≤
        ((4 * (3.14159265358979323847 : ℝ) - 1) *
          (0.0432139182638 : ℝ)) ^ 2 := by
    have hcoef :
        4 * Real.pi - 1 ≤ 4 * (3.14159265358979323847 : ℝ) - 1 := by
      nlinarith [Real.pi_lt_d20]
    have hmul :
        (4 * Real.pi - 1) * Real.exp (-Real.pi) ≤
          (4 * (3.14159265358979323847 : ℝ) - 1) *
            (0.0432139182638 : ℝ) := by
      exact mul_le_mul hcoef exp_neg_pi_rationalEnclosure_upper he0.le
        (by norm_num)
    exact pow_le_pow_left₀ (mul_nonneg hcoef0.le he0.le) hmul 2
  have horient :
      (0.0432139182637 : ℝ) ^ 2 ≤ Real.exp (-Real.pi) ^ 2 := by
    exact pow_le_pow_left₀ (by norm_num)
      exp_neg_pi_rationalEnclosure_lower 2
  rw [hraw] at hsq
  norm_num at hsq
  by_contra hnot
  have hWlt : (0.07926 : ℝ) < thetaCuspFirstAtomWardMoment 0 :=
    lt_of_not_ge hnot
  have hrawLower :
      (2 * (3.14159265358979323846 : ℝ) * (0.07926 : ℝ)) ^ 2 <
        (2 * Real.pi * thetaCuspFirstAtomWardMoment 0) ^ 2 := by
    have hbase :
        2 * (3.14159265358979323846 : ℝ) * (0.07926 : ℝ) <
          2 * Real.pi * thetaCuspFirstAtomWardMoment 0 := by
      calc
        2 * (3.14159265358979323846 : ℝ) * (0.07926 : ℝ) <
            2 * Real.pi * (0.07926 : ℝ) := by
              gcongr
              exact Real.pi_gt_d20
        _ < 2 * Real.pi * thetaCuspFirstAtomWardMoment 0 := by
          gcongr
    exact pow_lt_pow_left₀ hbase (by positivity) (by norm_num)
  nlinarith

/-- Four quantitative source bounds actually used by the low-degree Gibbs certificate after
the zeroth Ward endpoint is supplied by half-density fidelity.  All sign conditions have been
removed from this interface. -/
structure ThetaCuspFirstAtomSingleGibbsEssentialBounds : Prop where
  ward_one_lower :
    (0.0036560148424 : ℝ) ≤ thetaCuspFirstAtomWardMoment 1
  ward_two_upper :
    thetaCuspFirstAtomWardMoment 2 ≤ (0.00047155079379 : ℝ)
  stein_coupling_lower :
    (0.000369937497095 : ℝ) ≤ thetaCuspFirstRadialQuadraticSteinCoupling
  morse_upper_energy_upper :
    thetaCuspFirstRadialQuadraticMorseSingleGibbsUpperValue ≤
      (0.00397751749476338850697725 : ℝ)

/-- Essential Ward--Stein--Morse bounds discharge the complete first-atom low-degree
certificate. -/
theorem thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_of_essentialBounds
    (h : ThetaCuspFirstAtomSingleGibbsEssentialBounds) :
    ThetaCuspFirstAtomSingleGibbsLowDegreeCertificate := by
  let L : ℕ → ℝ := fun m => thetaCuspLiouvilleGibbsMoment m 1
  let J0 : ℝ := 4 * L 1 - L 2
  let J1 : ℝ := 8 * L 3 - L 4
  let C0 : ℝ := 8 * L 3 - 6 * L 4 + (1 / 2 : ℝ) * L 5
  let U : ℝ := thetaCuspFirstRadialQuadraticMorseSingleGibbsUpperValue
  let E0 : ℝ := 2 * Real.exp (-Real.pi) - L 0
  have hJ0eq : J0 = thetaCuspFirstAtomWardMoment 1 := by
    simp [J0, L, thetaCuspFirstAtomWardMoment]
  have hJ1eq : J1 = thetaCuspFirstAtomWardMoment 2 := by
    norm_num [J1, L, thetaCuspFirstAtomWardMoment]
  have hCeq : C0 = thetaCuspFirstRadialQuadraticSteinCoupling := by
    rw [thetaCuspFirstRadialQuadraticSteinCoupling_eq_singleGibbs]
  have hE0eq : E0 = thetaCuspFirstAtomWardMoment 0 := by
    rfl
  have hJ0 : (0.0036560148424 : ℝ) ≤ J0 := by simpa [hJ0eq] using h.ward_one_lower
  have hJ1 : J1 ≤ (0.00047155079379 : ℝ) := by
    simpa [hJ1eq] using h.ward_two_upper
  have hC : (0.000369937497095 : ℝ) ≤ C0 := by
    simpa [hCeq] using h.stein_coupling_lower
  have hU : U ≤ (0.00397751749476338850697725 : ℝ) := by
    simpa [U] using h.morse_upper_energy_upper
  have hE0 : E0 ≤ (0.07926 : ℝ) := by
    simpa [hE0eq] using
      thetaCuspFirstAtomWardMoment_zero_le_sevenThousandNineHundredTwentySix_div_oneHundredThousand
  have hJ0nonneg : 0 ≤ J0 := by
    rw [hJ0eq]
    exact thetaCuspFirstAtomWardMoment_nonneg 1
  have hJ1nonneg : 0 ≤ J1 := by
    rw [hJ1eq]
    exact thetaCuspFirstAtomWardMoment_nonneg 2
  have hCnonneg : 0 ≤ C0 := le_trans (by norm_num) hC
  have hUnonneg : 0 ≤ U := by
    exact thetaCuspFirstRadialQuadraticMorseSingleGibbsUpperValue_pos.le
  have hE0nonneg : 0 ≤ E0 := by
    rw [hE0eq]
    exact thetaCuspFirstAtomWardMoment_nonneg 0
  rw [ThetaCuspFirstAtomSingleGibbsLowDegreeCertificate,
    ThetaCuspFirstAtomSingleGibbsMorseCertificate,
    ThetaCuspFirstAtomSingleGibbsRelaxedCertificate]
  constructor
  · change (14 * (3005 / 2997 : ℝ) ^ 2 - 9) * J1 ^ 2 * U ≤
      9 * J0 * C0 ^ 2
    calc
      (14 * (3005 / 2997 : ℝ) ^ 2 - 9) * J1 ^ 2 * U ≤
          (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
            (0.00047155079379 : ℝ) ^ 2 *
              (0.00397751749476338850697725 : ℝ) := by
            gcongr
      _ ≤ 9 * (0.0036560148424 : ℝ) *
          (0.000369937497095 : ℝ) ^ 2 := by norm_num
      _ ≤ 9 * J0 * C0 ^ 2 := by gcongr
  · change 16 * ((3005 / 2997 : ℝ) * E0) *
      ((3005 / 2997 : ℝ) * J1) ≤ 45 * J0 ^ 2
    calc
          16 * ((3005 / 2997 : ℝ) * E0) *
          ((3005 / 2997 : ℝ) * J1) ≤
          16 * ((3005 / 2997 : ℝ) * (0.07926 : ℝ)) *
            ((3005 / 2997 : ℝ) * (0.00047155079379 : ℝ)) := by
              gcongr
      _ ≤ 45 * (0.0036560148424 : ℝ) ^ 2 := by norm_num
      _ ≤ 45 * J0 ^ 2 := by gcongr

/-- Existing rational moment boxes imply the four remaining essential source-functional bounds.
Seven of the eighteen moment endpoints are not used. -/
theorem thetaCuspFirstAtomSingleGibbsEssentialBounds_of_rationalMomentBounds
    (h : ThetaCuspFirstAtomSingleGibbsRationalMomentBounds) :
    ThetaCuspFirstAtomSingleGibbsEssentialBounds := by
  let L : ℕ → ℝ := fun m => thetaCuspLiouvilleGibbsMoment m 1
  let A : ℝ := thetaCuspFirstAtomMorseFisherDecayFactor
  let B : ℝ := 3 * L 1 + (21 / 4 : ℝ) * L 2 -
    (25 / 8 : ℝ) * L 4 - (15 / 4 : ℝ) * L 5 + (39 / 16 : ℝ) * L 6
  let D : ℝ := 6 * L 4 - 18 * L 5 + (51 / 2 : ℝ) * L 6 -
    15 * L 7 + 3 * L 8
  have hA := thetaCuspFirstAtomMorseFisherDecayFactor_rationalBounds
  have hDnonneg : 0 ≤ D := by
    simpa [D, L] using thetaCuspFirstAtomMorseQuarticRemainder_nonneg
  have hB :
      B ≤ (0.003934927387704375 : ℝ) := by
    dsimp [B, L]
    linarith [h.moment_one_upper, h.moment_two_upper, h.moment_four_lower,
      h.moment_five_lower, h.moment_six_upper]
  have hD :
      D ≤ (0.000046610404575 : ℝ) := by
    dsimp [D, L]
    linarith [h.moment_four_upper, h.moment_five_lower, h.moment_six_upper,
      h.moment_seven_lower, h.moment_eight_upper]
  have hAD :
      A * D ≤
        (0.91374677923 : ℝ) * (0.000046610404575 : ℝ) := by
    exact mul_le_mul hA.2.le hD hDnonneg (by norm_num)
  constructor
  · simp only [thetaCuspFirstAtomWardMoment]
    linarith [h.moment_one_lower, h.moment_two_upper]
  · simp only [thetaCuspFirstAtomWardMoment]
    linarith [h.moment_three_upper, h.moment_four_lower]
  · rw [thetaCuspFirstRadialQuadraticSteinCoupling_eq_singleGibbs]
    linarith [h.moment_three_lower, h.moment_four_upper, h.moment_five_lower]
  · rw [thetaCuspFirstRadialQuadraticMorseSingleGibbsUpperValue]
    calc
      3 * thetaCuspLiouvilleGibbsMoment 1 1 +
              21 / 4 * thetaCuspLiouvilleGibbsMoment 2 1 +
            (-25 / 8 + 6 * thetaCuspFirstAtomMorseFisherDecayFactor) *
              thetaCuspLiouvilleGibbsMoment 4 1 -
          (15 / 4 + 18 * thetaCuspFirstAtomMorseFisherDecayFactor) *
            thetaCuspLiouvilleGibbsMoment 5 1 +
        (39 / 16 + 51 / 2 * thetaCuspFirstAtomMorseFisherDecayFactor) *
            thetaCuspLiouvilleGibbsMoment 6 1 -
          15 * thetaCuspFirstAtomMorseFisherDecayFactor *
            thetaCuspLiouvilleGibbsMoment 7 1 +
        3 * thetaCuspFirstAtomMorseFisherDecayFactor *
            thetaCuspLiouvilleGibbsMoment 8 1 =
          B + A * D := by
            dsimp [B, D, A, L]
            ring
      _ ≤ _ := by linarith

/-- Compatibility: the old moment-box premise now factors through the essential five-bound
interface. -/
theorem thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_of_rationalMomentBounds
    (h : ThetaCuspFirstAtomSingleGibbsRationalMomentBounds) :
    ThetaCuspFirstAtomSingleGibbsLowDegreeCertificate :=
  thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_of_essentialBounds
    (thetaCuspFirstAtomSingleGibbsEssentialBounds_of_rationalMomentBounds h)

/-- The two-channel hypervirial closure only consumes the low-degree certificate, independently
of how that certificate was proved. -/
theorem thetaCuspFirstAtomSingleGibbs_twoChannelHypervirialClosure_of_lowDegreeCertificate
    (h : ThetaCuspFirstAtomSingleGibbsLowDegreeCertificate) :
    ThetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate ∧
    (16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) ∧
    (∀ a b : ℝ, 0 ≤
      (primeArchSourceTraceHankel (Polynomial.C a + Polynomial.C b * Polynomial.X)).re) ∧
    (PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative →
      PrimeArchSourceTraceHankelIntNonnegative ∧ RiemannHypothesis) := by
  have hreduced :=
    (thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_iff).1 h
  have hmorse := hreduced.1
  have hrelaxed := hreduced.2
  have hquadraticVirial :=
    thetaCusp_quadraticVirialEnergyCertificate_of_morseQuadraticEnvelope hmorse
  have hquadraticStein :=
    quadraticSteinEnergyCertificate_iff_virialEnergyCertificate.2
      hquadraticVirial
  have htwoChannel :=
    twoChannelSteinEnergyCertificate_of_quadraticSteinEnergyCertificate
      hquadraticStein
  have hrayleigh :=
    thetaCuspFirstRadialTwoChannelRayleighRitzCertificate_iff.2 htwoChannel
  have hhypervirial :=
    thetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate_iff.2
      hrayleigh
  refine ⟨hhypervirial, hrelaxed, ?_, ?_⟩
  · exact
      forall_primeArchSourceTraceHankel_linear_nonneg_of_twoChannelVirialRayleighRitz
        hhypervirial hrelaxed
  · intro htail
    exact
      ⟨primeArchSourceTraceHankelIntNonnegative_of_twoChannelSteinEnergy_of_degreeTwoTail
          htwoChannel hrelaxed htail,
        riemannHypothesis_of_twoChannelVirialRayleighRitz_of_primeArchDegreeTwoTail
          hhypervirial hrelaxed htail⟩

/-- Five essential source-functional bounds supply the optimized two-channel hypervirial
closure. -/
theorem thetaCuspFirstAtomSingleGibbs_twoChannelHypervirialClosure_of_essentialBounds
    (h : ThetaCuspFirstAtomSingleGibbsEssentialBounds) :
    ThetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate ∧
    (16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) ∧
    (∀ a b : ℝ, 0 ≤
      (primeArchSourceTraceHankel (Polynomial.C a + Polynomial.C b * Polynomial.X)).re) ∧
    (PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative →
      PrimeArchSourceTraceHankelIntNonnegative ∧ RiemannHypothesis) :=
  thetaCuspFirstAtomSingleGibbs_twoChannelHypervirialClosure_of_lowDegreeCertificate
    (thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_of_essentialBounds h)

/-- Essential bounds also discharge both likelihood single-loss premises and every linear
source-Hankel test. -/
theorem thetaCuspFirstAtomSingleGibbs_likelihoodSingleLossClosure_of_essentialBounds
    (h : ThetaCuspFirstAtomSingleGibbsEssentialBounds) :
    ThetaCuspFirstRadialTwoChannelVirialRayleighRitzSingleLossCertificate ∧
    (16 * (3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1 *
          thetaCuspBornWittenRadialRawMoment 2 0 1 ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) ∧
    (∀ a b : ℝ, 0 ≤
      (primeArchSourceTraceHankel (Polynomial.C a + Polynomial.C b * Polynomial.X)).re) := by
  have hold :=
    thetaCuspFirstAtomSingleGibbs_twoChannelHypervirialClosure_of_essentialBounds h
  have htwoChannelSquared :=
    thetaCuspFirstRadialTwoChannelRayleighRitzCertificate_iff.1
      (thetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate_iff.1 hold.1)
  have htwoChannel :=
    twoChannelSteinSingleLossEnergyCertificate_of_squaredLoss htwoChannelSquared
  have hrayleigh :=
    thetaCuspFirstRadialTwoChannelRayleighRitzSingleLossCertificate_iff.2 htwoChannel
  have hvirial :=
    thetaCuspFirstRadialTwoChannelVirialRayleighRitzSingleLossCertificate_iff.2
      hrayleigh
  have hrelaxed :=
    thetaCuspFirstRadial_relaxedSingleFactor_of_squaredFactor
      (c := (3005 / 2997 : ℝ)) (by norm_num) hold.2.1
  exact
    ⟨hvirial, hrelaxed,
      forall_primeArchSourceTraceHankel_linear_nonneg_of_twoChannelSteinSingleLoss
        htwoChannel hrelaxed⟩

/-- Essential bounds discharge all equivalent theta thermal/information windows. -/
theorem thetaCuspFirstAtomSingleGibbs_thermalWindows_of_essentialBounds
    (h : ThetaCuspFirstAtomSingleGibbsEssentialBounds) :
    ThetaCuspSizeBiasedSusceptibilityWindow ∧
      ThetaCuspSizeBiasPearsonWindow ∧
        ThetaCuspSizeBiasMeanLiftWindow := by
  have hold :=
    thetaCuspFirstAtomSingleGibbs_twoChannelHypervirialClosure_of_essentialBounds h
  have hrayleigh :=
    thetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate_iff.1 hold.1
  have hsusceptibility :=
    thetaCuspSizeBiasedSusceptibilityWindow_of_twoChannelRayleighRitz
      hrayleigh hold.2.1
  exact
    ⟨hsusceptibility,
      thetaCuspSizeBiasPearsonWindow_iff_susceptibilityWindow.2 hsusceptibility,
      thetaCuspSizeBiasMeanLiftWindow_iff_susceptibilityWindow.2 hsusceptibility⟩

/-- After the low block is reduced to five source-functional bounds, only the RH-equivalent
degree-two source tail remains. -/
theorem riemannHypothesis_of_singleGibbsEssentialBounds_singleLoss_of_primeArchDegreeTwoTail
    (h : ThetaCuspFirstAtomSingleGibbsEssentialBounds)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis := by
  have hclosure :=
    thetaCuspFirstAtomSingleGibbs_likelihoodSingleLossClosure_of_essentialBounds h
  exact
    riemannHypothesis_of_twoChannelVirialRayleighRitzSingleLoss_of_primeArchDegreeTwoTail
      hclosure.1 hclosure.2.1 htail

end

end RHTower
