import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyFiniteMassReflectionRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTopologicalDarbouxStarobinskySpectralFlow
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicPhysicalHorizonPolarizedSelector

/-!
# Moving-horizon third-mass/AIME anti-alignment

The exact moving-event-horizon third mass parity defect and the theta-mirror AIME chiral-kernel
defect are related by a unique positive susceptibility on every tilted Xi fibre.  Thus signed
third-order mass response has precisely the orientation needed for pointwise AIME cancellation;
sign/passivity alone cannot exclude that counterterm.

`[NEW] [THIRD-ORDER MASS JET] [AIME] [EXACT ANTI-ALIGNMENT] [SHARP NO-GO] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Canonical positive coefficient comparing the moving-horizon third mass jet with the
theta-mirror AIME chiral kernel. -/
def d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility
    (q : XiZeroCopy) : ℝ :=
  d4BMXiEventHorizonThirdMassReflectionSusceptibility q *
    d4BMXiThetaMirrorAIMEDenominator q / 12

theorem d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility_pos
    (q : XiZeroCopy) :
    0 < d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q := by
  exact div_pos
    (mul_pos (d4BMXiEventHorizonThirdMassReflectionSusceptibility_pos q)
      (d4BMXiThetaMirrorAIMEDenominator_pos q))
    (by norm_num)

/-- Exact anti-alignment of the physical moving-horizon third mass jet and the AIME chiral
theta-mirror defect. -/
theorem d4BMXiEventHorizonThirdMassParityJetDefect_eq_neg_susceptibility_mul_AIME
    (q : XiZeroCopy) :
    d4BMXiEventHorizonThirdMassParityJetDefect q =
      -d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q *
        d4BMXiThetaMirrorAIMEChiralKernelDefect q := by
  rw [d4BMXiEventHorizonThirdMassParityJetDefect_eq,
    d4BMXiThetaMirrorAIMEChiralKernelDefect_eq]
  unfold d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility
  have hD : d4BMXiThetaMirrorAIMEDenominator q ≠ 0 :=
    ne_of_gt (d4BMXiThetaMirrorAIMEDenominator_pos q)
  field_simp [hD]
  ring

/-- On every tilted fibre the two actual signed cubic defects have strictly opposite
orientation. -/
theorem d4BMXiEventHorizonThirdMassParityJetDefect_mul_AIME_neg_of_tilt
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiEventHorizonThirdMassParityJetDefect q *
        d4BMXiThetaMirrorAIMEChiralKernelDefect q < 0 := by
  rw [d4BMXiEventHorizonThirdMassParityJetDefect_eq_neg_susceptibility_mul_AIME]
  have hk := d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility_pos q
  have hA : d4BMXiThetaMirrorAIMEChiralKernelDefect q ≠ 0 :=
    (d4BMXiThetaMirrorAIMEChiralKernelDefect_ne_zero_iff q).2 htilt
  have hA2 : 0 < d4BMXiThetaMirrorAIMEChiralKernelDefect q ^ (2 : ℕ) :=
    sq_pos_of_ne_zero hA
  rw [show
      (-d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q *
          d4BMXiThetaMirrorAIMEChiralKernelDefect q) *
          d4BMXiThetaMirrorAIMEChiralKernelDefect q =
        -d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q *
          d4BMXiThetaMirrorAIMEChiralKernelDefect q ^ (2 : ℕ) by ring]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hk) hA2

/-- Sharp coefficient classification: off line the preceding positive susceptibility is the
unique scalar cancelling the moving-horizon third mass defect against the AIME defect. -/
theorem d4BMXiEventHorizonThirdMass_add_coefficient_mul_AIME_eq_zero_iff
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) (coefficient : ℝ) :
    d4BMXiEventHorizonThirdMassParityJetDefect q +
        coefficient * d4BMXiThetaMirrorAIMEChiralKernelDefect q = 0 ↔
      coefficient = d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q := by
  rw [d4BMXiEventHorizonThirdMassParityJetDefect_eq_neg_susceptibility_mul_AIME]
  have hA : d4BMXiThetaMirrorAIMEChiralKernelDefect q ≠ 0 :=
    (d4BMXiThetaMirrorAIMEChiralKernelDefect_ne_zero_iff q).2 htilt
  constructor
  · intro h
    have hfactor :
        (coefficient - d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q) *
          d4BMXiThetaMirrorAIMEChiralKernelDefect q = 0 := by
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hA)
  · intro h
    rw [h]
    ring

/-- Canonically compensated horizontal cubic mass-memory defect. -/
def d4BMXiEventHorizonThirdMassAIMECompensatedDefect (q : XiZeroCopy) : ℝ :=
  d4BMXiEventHorizonThirdMassParityJetDefect q +
    d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q *
      d4BMXiThetaMirrorAIMEChiralKernelDefect q

/-- The sign-compatible AIME counterchannel cancels the moving-horizon third mass defect
identically. -/
theorem d4BMXiEventHorizonThirdMassAIMECompensatedDefect_eq_zero
    (q : XiZeroCopy) :
    d4BMXiEventHorizonThirdMassAIMECompensatedDefect q = 0 := by
  rw [d4BMXiEventHorizonThirdMassAIMECompensatedDefect,
    d4BMXiEventHorizonThirdMassParityJetDefect_eq_neg_susceptibility_mul_AIME]
  ring

/-- Cubic absorbed-seed source carried by the actual moving-horizon third mass variant. -/
def d4BMXiEventHorizonThirdMassChiralSource
    (amplitude : ℂ) (q : XiZeroCopy) : ℂ :=
  amplitude * (Complex.normSq amplitude : ℂ) *
    (d4BMXiEventHorizonThirdMassParityJetDefect q : ℂ)

/-- The actual moving-horizon cubic source is nonzero exactly for a nonzero seed on a tilted
fibre. -/
theorem d4BMXiEventHorizonThirdMassChiralSource_ne_zero_iff
    (amplitude : ℂ) (q : XiZeroCopy) :
    d4BMXiEventHorizonThirdMassChiralSource amplitude q ≠ 0 ↔
      amplitude ≠ 0 ∧ (q.1 : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro hsource
    have ha : amplitude ≠ 0 := by
      intro ha
      apply hsource
      simp [d4BMXiEventHorizonThirdMassChiralSource, ha]
    have hdefC : (d4BMXiEventHorizonThirdMassParityJetDefect q : ℂ) ≠ 0 := by
      intro hdef
      apply hsource
      rw [d4BMXiEventHorizonThirdMassChiralSource, hdef, mul_zero]
    have hdefR : d4BMXiEventHorizonThirdMassParityJetDefect q ≠ 0 := by
      exact_mod_cast hdefC
    exact ⟨ha, fun hline => hdefR
      ((d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff q).2 hline)⟩
  · rintro ⟨ha, htilt⟩
    have hnormR : Complex.normSq amplitude ≠ 0 := by
      intro h
      exact ha (Complex.normSq_eq_zero.mp h)
    have hnormC : (Complex.normSq amplitude : ℂ) ≠ 0 := by
      exact_mod_cast hnormR
    have hdefR : d4BMXiEventHorizonThirdMassParityJetDefect q ≠ 0 :=
      (not_congr (d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff q)).2 htilt
    have hdefC : (d4BMXiEventHorizonThirdMassParityJetDefect q : ℂ) ≠ 0 := by
      exact_mod_cast hdefR
    exact mul_ne_zero (mul_ne_zero ha hnormC) hdefC

/-- Universal extinction of the exact moving-horizon third mass defect is RH. -/
theorem forall_d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff_rh :
    (∀ q : XiZeroCopy, d4BMXiEventHorizonThirdMassParityJetDefect q = 0) ↔
      RiemannHypothesis := by
  rw [← forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis 0]
  constructor
  · intro hall q
    apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff 0 q).2
    exact (d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff q).1 (hall q)
  · intro hall q
    apply (d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff q).2
    exact (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff 0 q).1 (hall q)

/-- For a nonzero absorbed seed, universal extinction of the actual moving-horizon cubic source
is RH. -/
theorem forall_d4BMXiEventHorizonThirdMassChiralSource_eq_zero_iff_rh
    {amplitude : ℂ} (ha : amplitude ≠ 0) :
    (∀ q : XiZeroCopy, d4BMXiEventHorizonThirdMassChiralSource amplitude q = 0) ↔
      RiemannHypothesis := by
  rw [← forall_d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff_rh]
  constructor
  · intro hall q
    by_contra hdef
    have hline : (q.1 : ℂ).re ≠ 1 / 2 :=
      (not_congr (d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff q)).1 hdef
    exact ((d4BMXiEventHorizonThirdMassChiralSource_ne_zero_iff amplitude q).2
      ⟨ha, hline⟩) (hall q)
  · intro hall q
    simp [d4BMXiEventHorizonThirdMassChiralSource, hall q]

end

end RHTower
