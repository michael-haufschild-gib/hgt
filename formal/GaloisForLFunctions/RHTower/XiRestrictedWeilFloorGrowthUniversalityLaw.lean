import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFloorGrowthSpectrum

/-!
# Xi restricted-Weil floor growth universality

The sampled and continuous growth presentations of one restricted-Weil negative floor form an
exact two-phase law.  Under RH all five upper-growth coordinates collapse.  Under failure of RH,
seven lower-growth and nonvanishing coordinates are synchronized by the right-transverse Xi
spectrum.
-/

open Complex Filter Function Set LSeries
open scoped Topology ENNReal

namespace RHTower

noncomputable section

/-- RH-side growth certificate for one continuous aperture floor and its logarithmic samples. -/
structure XiRestrictedWeilFloorRHCertificate (eta : ℝ → ℝ) : Prop where
  sampledAbscissa_eq_bot :
    LSeries.abscissaOfAbsConv
        (fun n => ((eta (Real.log n / 2) : ℝ) : ℂ)) = ⊥
  sampledSubpower :
    SubpowerAtNatInfinity (fun n => eta (Real.log n / 2))
  sampledUpperLogPowerExponent_eq_zero :
    SampledUpperLogPowerExponent (fun n => eta (Real.log n / 2)) = 0
  apertureUpperLogGrowthExponent_eq_zero :
    ApertureUpperLogGrowthExponent eta = 0
  apertureSubexponential :
    SubexponentialAtApertureInfinity eta

/-- False-RH growth certificate for the same floor.  The last coordinate records the exact
abscissa law whenever the logarithmic samples are monotone. -/
structure XiRestrictedWeilFloorFailureCertificate
    (eta : ℝ → ℝ) : Prop where
  sampledAbscissa_transverseLower :
    (((1 + xiRightTransverseSup : ℝ) : EReal)) ≤
      LSeries.abscissaOfAbsConv
        (fun n => ((eta (Real.log n / 2) : ℝ) : ℂ))
  sampledNotSubpower :
    ¬ SubpowerAtNatInfinity (fun n => eta (Real.log n / 2))
  sampledExponent_transverseLower :
    ENNReal.ofReal xiRightTransverseSup ≤
      SampledUpperLogPowerExponent (fun n => eta (Real.log n / 2))
  apertureExponent_transverseLower :
    ENNReal.ofReal xiRightTransverseSup ≤ ApertureUpperLogGrowthExponent eta
  apertureNotSubexponential :
    ¬ SubexponentialAtApertureInfinity eta
  sampledNotEventuallyZero :
    ¬ ∀ᶠ n : ℕ in atTop, eta (Real.log n / 2) = 0
  monotoneAbscissaIdentity :
    Monotone (fun n : ℕ => eta (Real.log n / 2)) →
      LSeries.abscissaOfAbsConv
          (fun n => ((eta (Real.log n / 2) : ℝ) : ℂ)) =
        1 + NonnegativeCoefficientLogPowerExponent
          (fun n => eta (Real.log n / 2))

/-- The sampled upper logarithmic exponent has the same exact zero locus as the continuous
aperture exponent: RH.  This is the missing connector between the sampled and continuous growth
theorems. -/
theorem riemannHypothesis_iff_sampledUpperLogPowerExponent_eq_zero
    {L : ℝ} (hL : 0 < L) {N : ℕ} {eta : ℕ → ℝ}
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N eta)
    (hzero : RiemannHypothesis → ∀ n, eta n = 0) :
    RiemannHypothesis ↔ SampledUpperLogPowerExponent eta = 0 := by
  constructor
  · intro hRH
    simp [SampledUpperLogPowerExponent, hzero hRH]
  · intro hexponent
    by_contra hnot
    have hne : Nonempty XiRightZeroCopy :=
      nonempty_xiRightZeroCopy_of_not_riemannHypothesis hnot
    have hlower := transverseSup_le_sampledUpperLogPowerExponent_of_false_rh
      hL hnot henv
    rw [hexponent] at hlower
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (xiRightTransverseSup_pos hne))) hlower

/-- The five RH-side coordinates are equivalent to RH. -/
theorem riemannHypothesis_iff_xiRestrictedWeilFloorRHCertificate
    {L : ℝ} (hL : 0 < L) {N : ℕ} {eta : ℝ → ℝ}
    (heta0 : ∀ a, 0 ≤ eta a)
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N
      (fun n => eta (Real.log n / 2)))
    (hzero : RiemannHypothesis → ∀ a, eta a = 0) :
    RiemannHypothesis ↔ XiRestrictedWeilFloorRHCertificate eta := by
  constructor
  · intro hRH
    have hsampleZero : RiemannHypothesis →
        ∀ n : ℕ, eta (Real.log n / 2) = 0 := fun h n => hzero h _
    refine
      { sampledAbscissa_eq_bot :=
          restrictedWeilFloor_abscissa_eq_bot_of_rh (hsampleZero hRH)
        sampledSubpower :=
          (riemannHypothesis_iff_restrictedWeilFloor_subpower
            hL henv hsampleZero).mp hRH
        sampledUpperLogPowerExponent_eq_zero :=
          (riemannHypothesis_iff_sampledUpperLogPowerExponent_eq_zero
            hL henv hsampleZero).mp hRH
        apertureUpperLogGrowthExponent_eq_zero :=
          (riemannHypothesis_iff_apertureUpperLogGrowthExponent_eq_zero
            hL heta0 henv hzero).mp hRH
        apertureSubexponential :=
          (riemannHypothesis_iff_aperture_subexponential
            hL henv hzero).mp hRH }
  · intro hcert
    exact (riemannHypothesis_iff_sampledUpperLogPowerExponent_eq_zero
      hL henv (fun h n => hzero h _)).mpr
        hcert.sampledUpperLogPowerExponent_eq_zero

/-- The seven false-RH coordinates are equivalent to failure of RH. -/
theorem not_riemannHypothesis_iff_xiRestrictedWeilFloorFailureCertificate
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {eta : ℝ → ℝ} (heta0 : ∀ a, 0 ≤ eta a)
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N
      (fun n => eta (Real.log n / 2)))
    (hzero : RiemannHypothesis → ∀ a, eta a = 0) :
    ¬ RiemannHypothesis ↔ XiRestrictedWeilFloorFailureCertificate eta := by
  constructor
  · intro hnot
    refine
      { sampledAbscissa_transverseLower :=
          restrictedWeilFloor_abscissa_lower_of_not_rh hL hN hnot henv
        sampledNotSubpower :=
          not_subpower_restrictedWeilFloor_of_false_rh hL hnot henv
        sampledExponent_transverseLower :=
          transverseSup_le_sampledUpperLogPowerExponent_of_false_rh hL hnot henv
        apertureExponent_transverseLower :=
          transverseSup_le_apertureUpperLogGrowthExponent_of_false_rh
            hL hnot heta0 henv
        apertureNotSubexponential :=
          not_aperture_subexponential_of_false_rh hL hnot henv
        sampledNotEventuallyZero :=
          restrictedWeilFloor_not_eventually_zero_of_not_rh hL hnot henv
        monotoneAbscissaIdentity := fun hmono =>
          restrictedWeilFloor_abscissa_eq_one_add_logPowerExponent_of_not_rh
            hL hnot henv hmono }
  · intro hcert hRH
    exact hcert.sampledNotSubpower
      ((riemannHypothesis_iff_restrictedWeilFloor_subpower
        hL henv (fun h n => hzero h _)).mp hRH)

/-- **Restricted-Weil floor growth universality.**  The five upper-growth coordinates and seven
lower-growth coordinates are exhaustive and mutually exclusive phases of one continuous floor. -/
theorem xiRestrictedWeilFloor_growth_universality
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {eta : ℝ → ℝ} (heta0 : ∀ a, 0 ≤ eta a)
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N
      (fun n => eta (Real.log n / 2)))
    (hzero : RiemannHypothesis → ∀ a, eta a = 0) :
    (RiemannHypothesis ↔ XiRestrictedWeilFloorRHCertificate eta) ∧
      (¬ RiemannHypothesis ↔ XiRestrictedWeilFloorFailureCertificate eta) ∧
      (XiRestrictedWeilFloorRHCertificate eta ↔
        ¬ XiRestrictedWeilFloorFailureCertificate eta) := by
  have hpositive := riemannHypothesis_iff_xiRestrictedWeilFloorRHCertificate
    hL heta0 henv hzero
  have hfailure := not_riemannHypothesis_iff_xiRestrictedWeilFloorFailureCertificate
    hL hN heta0 henv hzero
  refine ⟨hpositive, hfailure, ?_⟩
  constructor
  · intro hpos hfail
    exact (hfailure.mpr hfail) (hpositive.mpr hpos)
  · intro hnfail
    by_contra hnpos
    have hnot : ¬ RiemannHypothesis := fun hRH => hnpos (hpositive.mp hRH)
    exact hnfail (hfailure.mp hnot)

end

end RHTower
