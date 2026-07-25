import GaloisForLFunctions.RHTower.PrimeArchThetaLikelihoodSteinSingleLoss
import GaloisForLFunctions.RHTower.PrimeArchThetaThermalSusceptibility
import GaloisForLFunctions.RHTower.ThetaSingleGibbsTwoChannelHypervirialClosureUniversalityLaw

/-!
# Single-Gibbs likelihood single-loss closure

The single-Gibbs rational enclosure was originally propagated with two copies of the first-atom
comparison loss.  Likelihood ordering needs only one copy.  Nonnegativity of the radial moments
therefore transports both low-degree certificates to the single-loss interfaces.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Two-channel Stein certificates are antitone in their target moment multiplier. -/
theorem twoChannelSteinScaledEnergyCertificate_of_le
    {κ₁ κ₂ : ℝ} (hκ : κ₁ ≤ κ₂)
    (hcert : ThetaCuspFirstRadialTwoChannelSteinScaledEnergyCertificate κ₂) :
    ThetaCuspFirstRadialTwoChannelSteinScaledEnergyCertificate κ₁ := by
  rcases hcert with ⟨a, b, henergy, hcert⟩
  refine ⟨a, b, henergy, ?_⟩
  have hfactor :
      0 ≤ thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
        thetaCuspFirstRadialTwoChannelSteinEnergy a b :=
    mul_nonneg (sq_nonneg _) henergy.le
  calc
    (κ₁ - 9) * thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
          thetaCuspFirstRadialTwoChannelSteinEnergy a b =
        (κ₁ - 9) *
          (thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
            thetaCuspFirstRadialTwoChannelSteinEnergy a b) := by ring
    _ ≤ (κ₂ - 9) *
          (thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
            thetaCuspFirstRadialTwoChannelSteinEnergy a b) :=
      mul_le_mul_of_nonneg_right (by linarith) hfactor
    _ = (κ₂ - 9) * thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
          thetaCuspFirstRadialTwoChannelSteinEnergy a b := by ring
    _ ≤ 9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
          thetaCuspFirstRadialTwoChannelSteinCoupling a b ^ 2 := hcert

/-- The original two-channel squared-loss certificate implies its likelihood single-loss
counterpart without returning to a fixed quadratic witness. -/
theorem twoChannelSteinSingleLossEnergyCertificate_of_squaredLoss
    (hcert : ThetaCuspFirstRadialTwoChannelSteinEnergyCertificate) :
    ThetaCuspFirstRadialTwoChannelSteinSingleLossEnergyCertificate := by
  apply twoChannelSteinScaledEnergyCertificate_of_le
    (κ₁ := 14 * (3005 / 2997 : ℝ))
    (κ₂ := 14 * (3005 / 2997 : ℝ) ^ 2)
  · norm_num
  · exact hcert

/-- A relaxed first-atom estimate carrying two copies of a factor `c ≥ 1` implies the
corresponding estimate carrying one copy. -/
theorem thetaCuspFirstRadial_relaxedSingleFactor_of_squaredFactor
    {c : ℝ} (hc : 1 ≤ c)
    (hrelaxed :
      16 * (c * thetaCuspBornWittenRadialRawMoment 0 0 1) *
          (c * thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) :
    16 * c * thetaCuspBornWittenRadialRawMoment 0 0 1 *
          thetaCuspBornWittenRadialRawMoment 2 0 1 ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2 := by
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  have hp :
      0 ≤ thetaCuspBornWittenRadialRawMoment 0 0 1 *
        thetaCuspBornWittenRadialRawMoment 2 0 1 :=
    mul_nonneg
      (by
        have h := thetaCuspAtomRawEvenMoment_nonneg 0 1
        rw [thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 0 0 1] at h
        nlinarith [Real.pi_pos])
      (by
        have h := thetaCuspAtomRawEvenMoment_nonneg 2 1
        rw [thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 2 0 1] at h
        nlinarith [Real.pi_pos])
  have hcoeff : 16 * c ≤ 16 * c ^ 2 := by
    nlinarith
  calc
    16 * c * thetaCuspBornWittenRadialRawMoment 0 0 1 *
          thetaCuspBornWittenRadialRawMoment 2 0 1 =
        (16 * c) *
          (thetaCuspBornWittenRadialRawMoment 0 0 1 *
            thetaCuspBornWittenRadialRawMoment 2 0 1) := by ring
    _ ≤ (16 * c ^ 2) *
          (thetaCuspBornWittenRadialRawMoment 0 0 1 *
            thetaCuspBornWittenRadialRawMoment 2 0 1) :=
      mul_le_mul_of_nonneg_right hcoeff hp
    _ = 16 * (c * thetaCuspBornWittenRadialRawMoment 0 0 1) *
          (c * thetaCuspBornWittenRadialRawMoment 2 0 1) := by ring
    _ ≤ 45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2 := hrelaxed

/-- A single rational enclosure supplies the likelihood single-loss two-channel certificate,
the matching relaxed inequality, and all linear source-Hankel tests. -/
theorem
    thetaCuspFirstAtomSingleGibbs_likelihoodSingleLossClosure_of_rationalEnclosure
    (h : ThetaCuspFirstAtomSingleGibbsRationalMomentEnclosure) :
    ThetaCuspFirstRadialTwoChannelVirialRayleighRitzSingleLossCertificate ∧
    (16 * (3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1 *
          thetaCuspBornWittenRadialRawMoment 2 0 1 ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) ∧
    (∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re) := by
  have hold :=
    thetaCuspFirstAtomSingleGibbs_twoChannelHypervirialClosure_of_rationalEnclosure h
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

/-- The same rational enclosure discharges all three equivalent thermal/information-theoretic
interfaces for the completed theta source. -/
theorem thetaCuspFirstAtomSingleGibbs_thermalWindows_of_rationalEnclosure
    (h : ThetaCuspFirstAtomSingleGibbsRationalMomentEnclosure) :
    ThetaCuspSizeBiasedSusceptibilityWindow ∧
      ThetaCuspSizeBiasPearsonWindow ∧
        ThetaCuspSizeBiasMeanLiftWindow := by
  have hold :=
    thetaCuspFirstAtomSingleGibbs_twoChannelHypervirialClosure_of_rationalEnclosure h
  have hrayleigh :=
    thetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate_iff.1 hold.1
  have hsusceptibility :=
    thetaCuspSizeBiasedSusceptibilityWindow_of_twoChannelRayleighRitz
      hrayleigh hold.2.1
  exact
    ⟨hsusceptibility,
      thetaCuspSizeBiasPearsonWindow_iff_susceptibilityWindow.2 hsusceptibility,
      thetaCuspSizeBiasMeanLiftWindow_iff_susceptibilityWindow.2 hsusceptibility⟩

/-- The single-Gibbs rational enclosure discharges both likelihood single-loss premises; only
the degree-two source tail remains for RH. -/
theorem
    riemannHypothesis_of_singleGibbsRationalEnclosure_singleLoss_of_primeArchDegreeTwoTail
    (h : ThetaCuspFirstAtomSingleGibbsRationalMomentEnclosure)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis := by
  have hclosure :=
    thetaCuspFirstAtomSingleGibbs_likelihoodSingleLossClosure_of_rationalEnclosure h
  exact
    riemannHypothesis_of_twoChannelVirialRayleighRitzSingleLoss_of_primeArchDegreeTwoTail
      hclosure.1 hclosure.2.1 htail

/-! ## Moment-only enclosure -/

/-- Exact lower endpoint used by the single-Gibbs rational enclosure. -/
theorem exp_neg_pi_rationalEnclosure_lower :
    (0.0432139182637 : ℝ) ≤ Real.exp (-Real.pi) := by
  let x : ℝ := -(3.14159265358979323847 : ℝ) / 4
  have hx : |x| ≤ 1 := by norm_num [x]
  have hb := Real.exp_bound (x := x) hx (n := 16) (by norm_num)
  have hsum :
      ∑ m ∈ Finset.range 16, x ^ m / m.factorial =
        ∑ m ∈ Finset.range 16,
          (-(3.14159265358979323847 : ℝ) / 4) ^ m / m.factorial := by
    rfl
  have hroot : (0.4559381277659 : ℝ) ≤ Real.exp x := by
    rw [hsum] at hb
    norm_num [Finset.sum_range_succ, Nat.factorial] at hb ⊢
    have h := (abs_le.mp hb).1
    linarith
  have hxpi : x ≤ -Real.pi / 4 := by
    dsimp [x]
    nlinarith [Real.pi_lt_d20]
  have hrootpi : (0.4559381277659 : ℝ) ≤ Real.exp (-Real.pi / 4) :=
    hroot.trans (Real.exp_le_exp.mpr hxpi)
  have hpow :
      Real.exp (-Real.pi) = Real.exp (-Real.pi / 4) ^ 4 := by
    calc
      Real.exp (-Real.pi) =
          Real.exp ((4 : ℕ) * (-Real.pi / 4)) := by congr 1; norm_num; ring
      _ = Real.exp (-Real.pi / 4) ^ 4 := by rw [Real.exp_nat_mul]
  rw [hpow]
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.4559381277659)
    hrootpi 4]

/-- Exact upper endpoint used by the single-Gibbs rational enclosure. -/
theorem exp_neg_pi_rationalEnclosure_upper :
    Real.exp (-Real.pi) ≤ (0.0432139182638 : ℝ) := by
  let x : ℝ := -(3.14159265358979323846 : ℝ) / 4
  have hx : |x| ≤ 1 := by norm_num [x]
  have hb := Real.exp_bound (x := x) hx (n := 16) (by norm_num)
  have hsum :
      ∑ m ∈ Finset.range 16, x ^ m / m.factorial =
        ∑ m ∈ Finset.range 16,
          (-(3.14159265358979323846 : ℝ) / 4) ^ m / m.factorial := by
    rfl
  have hroot : Real.exp x ≤ (0.45593812776605 : ℝ) := by
    rw [hsum] at hb
    norm_num [Finset.sum_range_succ, Nat.factorial] at hb ⊢
    have h := (abs_le.mp hb).2
    linarith
  have hpix : -Real.pi / 4 ≤ x := by
    dsimp [x]
    nlinarith [Real.pi_gt_d20]
  have hrootpi : Real.exp (-Real.pi / 4) ≤ (0.45593812776605 : ℝ) :=
    (Real.exp_le_exp.mpr hpix).trans hroot
  have hpow :
      Real.exp (-Real.pi) = Real.exp (-Real.pi / 4) ^ 4 := by
    calc
      Real.exp (-Real.pi) =
          Real.exp ((4 : ℕ) * (-Real.pi / 4)) := by congr 1; norm_num; ring
      _ = Real.exp (-Real.pi / 4) ^ 4 := by rw [Real.exp_nat_mul]
  rw [hpow]
  nlinarith [pow_le_pow_left₀ (Real.exp_pos _).le hrootpi 4]

/-- Source-facing rational enclosure containing only the nine Gibbs-moment intervals. -/
structure ThetaCuspFirstAtomSingleGibbsRationalMomentBounds : Prop where
  moment_zero_lower :
    (0.0073359406266 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 0 1
  moment_zero_upper :
    thetaCuspLiouvilleGibbsMoment 0 1 ≤ (0.0073359406267 : ℝ)
  moment_one_lower :
    (0.0009673899917 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 1 1
  moment_one_upper :
    thetaCuspLiouvilleGibbsMoment 1 1 ≤ (0.0009673899918 : ℝ)
  moment_two_lower :
    (0.0002135451243 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 2 1
  moment_two_upper :
    thetaCuspLiouvilleGibbsMoment 2 1 ≤ (0.0002135451244 : ℝ)
  moment_three_lower :
    (0.00006158723110 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 3 1
  moment_three_upper :
    thetaCuspLiouvilleGibbsMoment 3 1 ≤ (0.00006158723112 : ℝ)
  moment_four_lower :
    (0.00002114705517 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 4 1
  moment_four_upper :
    thetaCuspLiouvilleGibbsMoment 4 1 ≤ (0.00002114705518 : ℝ)
  moment_five_lower :
    (0.00000824395875 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 5 1
  moment_five_upper :
    thetaCuspLiouvilleGibbsMoment 5 1 ≤ (0.00000824395876 : ℝ)
  moment_six_lower :
    (0.00000354662642 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 6 1
  moment_six_upper :
    thetaCuspLiouvilleGibbsMoment 6 1 ≤ (0.00000354662643 : ℝ)
  moment_seven_lower :
    (0.00000165261304 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 7 1
  moment_seven_upper :
    thetaCuspLiouvilleGibbsMoment 7 1 ≤ (0.00000165261305 : ℝ)
  moment_eight_lower :
    (0.00000082318420 : ℝ) ≤ thetaCuspLiouvilleGibbsMoment 8 1
  moment_eight_upper :
    thetaCuspLiouvilleGibbsMoment 8 1 ≤ (0.00000082318421 : ℝ)

/-- The moment-only package supplies the original enclosure; both non-moment fields are
unconditional. -/
theorem thetaCuspFirstAtomSingleGibbsRationalMomentEnclosure_of_momentBounds
    (h : ThetaCuspFirstAtomSingleGibbsRationalMomentBounds) :
    ThetaCuspFirstAtomSingleGibbsRationalMomentEnclosure where
  exp_neg_pi_lower := exp_neg_pi_rationalEnclosure_lower
  exp_neg_pi_upper := exp_neg_pi_rationalEnclosure_upper
  moment_zero_lower := h.moment_zero_lower
  moment_zero_upper := h.moment_zero_upper
  moment_one_lower := h.moment_one_lower
  moment_one_upper := h.moment_one_upper
  moment_two_lower := h.moment_two_lower
  moment_two_upper := h.moment_two_upper
  moment_three_lower := h.moment_three_lower
  moment_three_upper := h.moment_three_upper
  moment_four_lower := h.moment_four_lower
  moment_four_upper := h.moment_four_upper
  moment_five_lower := h.moment_five_lower
  moment_five_upper := h.moment_five_upper
  moment_six_lower := h.moment_six_lower
  moment_six_upper := h.moment_six_upper
  moment_seven_lower := h.moment_seven_lower
  moment_seven_upper := h.moment_seven_upper
  moment_eight_lower := h.moment_eight_lower
  moment_eight_upper := h.moment_eight_upper

/-- Moment data alone supplies likelihood single-loss closure, relaxed moment control, and all
linear source-Hankel tests. -/
theorem thetaCuspFirstAtomSingleGibbs_likelihoodSingleLossClosure_of_momentBounds
    (h : ThetaCuspFirstAtomSingleGibbsRationalMomentBounds) :
    ThetaCuspFirstRadialTwoChannelVirialRayleighRitzSingleLossCertificate ∧
    (16 * (3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1 *
          thetaCuspBornWittenRadialRawMoment 2 0 1 ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) ∧
    (∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re) :=
  thetaCuspFirstAtomSingleGibbs_likelihoodSingleLossClosure_of_rationalEnclosure
    (thetaCuspFirstAtomSingleGibbsRationalMomentEnclosure_of_momentBounds h)

/-- Moment data alone supplies all equivalent theta thermal/information windows. -/
theorem thetaCuspFirstAtomSingleGibbs_thermalWindows_of_momentBounds
    (h : ThetaCuspFirstAtomSingleGibbsRationalMomentBounds) :
    ThetaCuspSizeBiasedSusceptibilityWindow ∧
      ThetaCuspSizeBiasPearsonWindow ∧
        ThetaCuspSizeBiasMeanLiftWindow :=
  thetaCuspFirstAtomSingleGibbs_thermalWindows_of_rationalEnclosure
    (thetaCuspFirstAtomSingleGibbsRationalMomentEnclosure_of_momentBounds h)

/-- After discharging both exponential endpoints and the likelihood interfaces, only moment
bounds and the RH-equivalent degree-two tail remain. -/
theorem
    riemannHypothesis_of_singleGibbsMomentBounds_singleLoss_of_primeArchDegreeTwoTail
    (h : ThetaCuspFirstAtomSingleGibbsRationalMomentBounds)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_singleGibbsRationalEnclosure_singleLoss_of_primeArchDegreeTwoTail
    (thetaCuspFirstAtomSingleGibbsRationalMomentEnclosure_of_momentBounds h) htail

end

end RHTower
