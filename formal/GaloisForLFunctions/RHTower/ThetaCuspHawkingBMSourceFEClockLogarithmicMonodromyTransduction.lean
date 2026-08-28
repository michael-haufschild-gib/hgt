import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEClockChiralAmplitudeTransduction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonLogarithmicCompanionOpticalLanding

/-!
# Source-FE clock/logarithmic-monodromy transduction

The reflected source-FE centered-QNM clock defect reaches the full finite-radiation radial response,
not only its horizon source coefficient.  On canonical logarithm sheets differing by `2πi`, the
actual Einstein-radiation sheet jump is exactly the clock coefficient times the nowhere-zero HC58
source transducer and the exact homogeneous mixed-BM monodromy mode.

The mode's already-proved nonzero Frobenius leading coefficient implies that it is nonzero somewhere
in every punctured horizon disk.  Therefore, for every nonzero Einstein seed, the unsquared radial
sheet response is identically dark exactly when the clock defect vanishes; universal sheet darkness
is RH.  The frozen Gram and finite-radiation optical deck coefficient then transport the associated
positive clock energy.  Homogeneous radial conservation is thus a faithful receiver of off-wall
clock charge, not an independent law annihilating it.

`[NEW] [RADIAL MONODROMY] [UNSQUARED RESPONSE] [CONSERVATION NO-GO] [LEAN-PROVED]`
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Canonical finite-radiation logarithmic deck jump driven by the actual Einstein source. -/
def hbXiPeierlsSourceFEClockFiniteRadiationDeckJump
    (n k : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) (z : ℂ) : ℂ :=
  ((d4BMXiMixedHorizonRadiationLogarithmicCompanionSheetResponse
        n k q (fun _ => 2 * Real.pi * Complex.I) -
      d4BMXiMixedHorizonRadiationLogarithmicCompanionSheetResponse
        n k q (fun _ => 0))
    (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
      amplitude orthogonalMixing q)) z

/-- The actual finite-radiation sheet jump is the clock defect times the physical transducer and
the exact homogeneous radial monodromy mode. -/
theorem hbXiPeierlsSourceFEClockFiniteRadiationDeckJump_eq
    (n k : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) (z : ℂ)
    (hz : ‖z‖ₑ < 1) :
    hbXiPeierlsSourceFEClockFiniteRadiationDeckJump
        n k amplitude orthogonalMixing q z =
      hbXiPeierlsClockToChiralSourceTransducer amplitude q *
        hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q *
          d4BMXiMixedHorizonExactMonodromyMode n k q z := by
  rw [hbXiPeierlsSourceFEClockFiniteRadiationDeckJump,
    d4BMXiMixedHorizonRadiationLogarithmicCompanionSheetResponse_sub_apply
      n k amplitude orthogonalMixing q
      (fun _ => 2 * Real.pi * Complex.I) (fun _ => 0) z hz (by ring),
    d4BMMixedHorizonOpticalSourceProjection_eq_clockTransducer_mul_defectCoefficient
      (n := n)]

/-- The exact Xi-fibre radial monodromy mode is nonzero somewhere in every punctured horizon
disk. -/
theorem exists_d4BMXiMixedHorizonExactMonodromyMode_ne_zero_puncturedDisk
    (n k : ℕ) (q : XiZeroCopy) (ε : ℝ) (hε : 0 < ε) :
    ∃ z : ℂ, z ≠ 0 ∧ ‖z‖ < ε ∧
      d4BMXiMixedHorizonExactMonodromyMode n k q z ≠ 0 := by
  have hratio :
      ∀ᶠ z : ℂ in 𝓝[≠] 0,
        d4BMXiMixedHorizonExactMonodromyMode n k q z /
            z ^ (d4BMMixedHorizonFrobeniusOrder n k + 1) ≠ 0 :=
    (tendsto_d4BMXiMixedHorizonExactMonodromyMode_div_pow_zero n k q).eventually_ne
      (d4BMXiMixedHorizonComplexMonodromyJump_ne_zero n k q)
  have hball : Metric.ball (0 : ℂ) ε ∈ 𝓝[≠] (0 : ℂ) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hε)
  have hball' : ∀ᶠ z : ℂ in 𝓝[≠] 0, z ∈ Metric.ball (0 : ℂ) ε := hball
  have hself : ∀ᶠ z : ℂ in 𝓝[≠] 0, z ≠ 0 := self_mem_nhdsWithin
  rcases (hself.and (hball'.and hratio)).exists with
    ⟨z, hz0, hzball, hratioz⟩
  refine ⟨z, hz0, mem_ball_zero_iff.mp hzball, ?_⟩
  intro hzero
  apply hratioz
  rw [hzero]
  simp

/-- In particular, the exact radial monodromy mode is nonzero at a point where its convergent
unit-disk representation is valid. -/
theorem exists_d4BMXiMixedHorizonExactMonodromyMode_ne_zero_unitDisk
    (n k : ℕ) (q : XiZeroCopy) :
    ∃ z : ℂ, z ≠ 0 ∧ ‖z‖ₑ < 1 ∧
      d4BMXiMixedHorizonExactMonodromyMode n k q z ≠ 0 := by
  rcases exists_d4BMXiMixedHorizonExactMonodromyMode_ne_zero_puncturedDisk
      n k q 1 one_pos with ⟨z, hz0, hz, hmode⟩
  refine ⟨z, hz0, ?_, hmode⟩
  rw [← ENNReal.coe_one, enorm_lt_coe]
  exact_mod_cast hz

/-- For a nonzero Einstein seed, a nonzero radial deck response exists exactly when the reflected
source-FE centered-clock coefficient is nonzero. -/
theorem exists_hbXiPeierlsSourceFEClockFiniteRadiationDeckJump_ne_zero_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n k : ℕ) (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    (∃ z : ℂ, z ≠ 0 ∧ ‖z‖ₑ < 1 ∧
      hbXiPeierlsSourceFEClockFiniteRadiationDeckJump
        n k amplitude orthogonalMixing q z ≠ 0) ↔
      hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q ≠ 0 := by
  constructor
  · rintro ⟨z, hz0, hz, hjump⟩ hdefect
    apply hjump
    rw [hbXiPeierlsSourceFEClockFiniteRadiationDeckJump_eq
      n k amplitude orthogonalMixing q z hz, hdefect]
    ring
  · intro hdefect
    rcases exists_d4BMXiMixedHorizonExactMonodromyMode_ne_zero_unitDisk n k q with
      ⟨z, hz0, hz, hmode⟩
    refine ⟨z, hz0, hz, ?_⟩
    rw [hbXiPeierlsSourceFEClockFiniteRadiationDeckJump_eq
      n k amplitude orthogonalMixing q z hz]
    exact mul_ne_zero
      (mul_ne_zero (hbXiPeierlsClockToChiralSourceTransducer_ne_zero ha q) hdefect)
      hmode

/-- The whole punctured-disk radial sheet response is dark exactly when the centered-clock
coefficient vanishes. -/
theorem forall_hbXiPeierlsSourceFEClockFiniteRadiationDeckJump_eq_zero_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n k : ℕ) (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    (∀ z : ℂ, ‖z‖ₑ < 1 →
      hbXiPeierlsSourceFEClockFiniteRadiationDeckJump
        n k amplitude orthogonalMixing q z = 0) ↔
      hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q = 0 := by
  constructor
  · intro hall
    by_contra hdefect
    rcases (exists_hbXiPeierlsSourceFEClockFiniteRadiationDeckJump_ne_zero_iff
      ha n k orthogonalMixing q).mpr hdefect with ⟨z, hz0, hz, hjump⟩
    exact hjump (hall z hz)
  · intro hdefect z hz
    rw [hbXiPeierlsSourceFEClockFiniteRadiationDeckJump_eq
      n k amplitude orthogonalMixing q z hz, hdefect]
    ring

/-- Radial sheet-response darkness on one Xi fibre is exactly critical-line placement. -/
theorem forall_hbXiPeierlsSourceFEClockFiniteRadiationDeckJump_eq_zero_iff_re_eq_half
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n k : ℕ) (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    (∀ z : ℂ, ‖z‖ₑ < 1 →
      hbXiPeierlsSourceFEClockFiniteRadiationDeckJump
        n k amplitude orthogonalMixing q z = 0) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [forall_hbXiPeierlsSourceFEClockFiniteRadiationDeckJump_eq_zero_iff
      ha n k orthogonalMixing q,
    hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff]

/-- Universal extinction of the actual finite-radiation logarithmic sheet response is RH. -/
theorem forall_hbXiPeierlsSourceFEClockFiniteRadiationDeckJump_eq_zero_iff_rh
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n k : ℕ) (orthogonalMixing : ℂ) :
    (∀ q : XiZeroCopy, ∀ z : ℂ, ‖z‖ₑ < 1 →
      hbXiPeierlsSourceFEClockFiniteRadiationDeckJump
        n k amplitude orthogonalMixing q z = 0) ↔
      RiemannHypothesis := by
  rw [← forall_hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff_rh n]
  constructor
  · intro hall q
    exact (forall_hbXiPeierlsSourceFEClockFiniteRadiationDeckJump_eq_zero_iff
      ha n k orthogonalMixing q).mp (hall q)
  · intro hall q
    exact (forall_hbXiPeierlsSourceFEClockFiniteRadiationDeckJump_eq_zero_iff
      ha n k orthogonalMixing q).mpr (hall q)

/-- Frozen finite-radiation optical Gram is exactly the product of transducer energy and clock
defect energy. -/
theorem d4BMXiMixedHorizonRadiationOpticalGramCokernel_apply_eq_clockEnergy
    (n : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMXiMixedHorizonRadiationOpticalGramCokernel amplitude orthogonalMixing q
        (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
          amplitude orthogonalMixing q) =
      (Complex.normSq (hbXiPeierlsClockToChiralSourceTransducer amplitude q) : ℂ) *
        (Complex.normSq
          (hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q) : ℂ) := by
  rw [d4BMXiMixedHorizonRadiationOpticalGramCokernel_apply,
    d4BMMixedHorizonOpticalSourceProjection_eq_clockTransducer_mul_defectCoefficient
      (n := n),
    Complex.normSq_mul]
  push_cast
  rfl

/-- The finite-radiation optical deck coefficient transports, rather than cancels, the positive
clock-defect energy. -/
theorem d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient_eq_clockEnergy
    (n k : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient
        n k amplitude orthogonalMixing q =
      d4BMXiMixedHorizonComplexMonodromyJump n k q *
        ((Complex.normSq (hbXiPeierlsClockToChiralSourceTransducer amplitude q) *
          Complex.normSq
            (hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q) : ℝ) : ℂ) := by
  rw [d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient,
    d4BMXiMixedHorizonRadiationOpticalGramCokernel_apply_eq_clockEnergy (n := n)]
  push_cast
  rfl

/-- With a nonzero seed, the finite-radiation optical deck coefficient vanishes exactly when the
unsquared centered-clock defect vanishes. -/
theorem d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient_eq_zero_iff_clockDefect
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n k : ℕ) (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient
        n k amplitude orthogonalMixing q = 0 ↔
      hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q = 0 := by
  rw [d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient_eq_causalOpticalSection,
    d4BMXiMixedHorizonCausalOpticalSection_eq_zero_iff ha n k orthogonalMixing q,
    hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff]

/-- Universal extinction of the finite-radiation optical deck coefficient is RH. -/
theorem forall_d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient_eq_zero_iff_rh
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n k : ℕ) (orthogonalMixing : ℂ) :
    (∀ q : XiZeroCopy,
      d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient
        n k amplitude orthogonalMixing q = 0) ↔ RiemannHypothesis := by
  rw [← forall_hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff_rh n]
  constructor
  · intro hall q
    exact (d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient_eq_zero_iff_clockDefect
      ha n k orthogonalMixing q).mp (hall q)
  · intro hall q
    exact (d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient_eq_zero_iff_clockDefect
      ha n k orthogonalMixing q).mpr (hall q)

end

end RHTower
