import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTiltedBackreactionGaugeEndpoint
import GaloisForLFunctions.RHTower.RouteRBurnolThetaSameFiberOrientation

/-!
# Theta-Hawking conservative reflected-sector transfer

Passive partially transmitting mirrors have a passive total mechanical impedance, and a full
lossless scattering dilation conserves total power.  Neither fact makes each theta/Xi resonance
port passive separately.  This endpoint computes the exact obstruction.

At a theta backreaction resonance `alpha`, source reflection preserves the physical response
energy while reversing Hawking anomaly port power:

`E(-alpha) = E(alpha) > 0`,  `D(-alpha) = -D(alpha)`.

Let a conservative material channel transfer power `c` into the `alpha` sector and `-c` into its
reflected partner.  Both corrected ports are passive exactly when

`c = -D(alpha) = -2 M Im(alpha) E(alpha)`.

Thus conservative total passivity does not by itself select the critical line: every reflected
pair has one passive completion.  But every nonzero tilt forces that completion to have nonzero
cross-sector transfer.  Sector-local passivity with zero transfer is equivalent to RH.  This is
the sharp alternative left by genuine Hawking backreaction: neutral tilt, or reflected-sector
mixing that cancels the complete modular work.

The result uses the coefficient-faithful theta root-energy reflection law and the conformal-anomaly
port identity.  Generic KMS, CCR, group, inverse, or Krein laws do not determine either coefficient.
-/

namespace RHTower

noncomputable section

open HedenmalmQuantile HedenmalmThetaSource

/-- Theta/Xi reflection preserves the full positive energy of the physical backreaction mode. -/
theorem thetaCuspHawkingBackreactionPhysicalEnergy_reflected
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingBackreactionPhysicalEnergy
        (thetaCuspHawkingBackreactionReflectedResonantMode r) =
      thetaCuspHawkingBackreactionPhysicalEnergy r := by
  rw [thetaCuspHawkingBackreactionPhysicalEnergy,
    thetaCuspHawkingBackreactionPhysicalEnergy]
  have hstrip := thetaCuspHawkingBackreactionResonantMode_mem_sourceStrip r
  have hsource : xiC thetaSource r.1 = 0 := by
    rw [xiC_thetaSource hstrip]
    exact thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero r
  have hroot : thetaRootEnergy (-r.1) = thetaRootEnergy r.1 :=
    thetaRootEnergy_neg_of_zero hstrip hsource
  change Complex.normSq ((Complex.I * (-r.1))⁻¹) * thetaRootEnergy (-r.1) = _
  rw [hroot]
  congr 1
  rw [show Complex.I * (-r.1) = -(Complex.I * r.1) by ring]
  simp

/-- Reflected theta-Hawking modes carry exactly opposite anomaly port powers. -/
theorem thetaCuspHawkingBackreactionPortDissipation_reflected
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingBackreactionPortDissipation
        (thetaCuspHawkingBackreactionReflectedResonantMode r) =
      -thetaCuspHawkingBackreactionPortDissipation r := by
  rw [thetaCuspHawkingBackreactionPortDissipation_eq,
    thetaCuspHawkingBackreactionPortDissipation_eq,
    thetaCuspHawkingBackreactionReflectedResonantMode_im,
    thetaCuspHawkingBackreactionPhysicalEnergy_reflected]
  ring

/-- Corrected power in one resonance sector after conservative material transfer. -/
def thetaCuspHawkingConservativeForwardPort
    (r : ThetaCuspHawkingBackreactionResonantMode) (transfer : ℝ) : ℝ :=
  thetaCuspHawkingBackreactionPortDissipation r + transfer

/-- Corrected power in the reflected sector; conservation fixes the correction to `-transfer`. -/
def thetaCuspHawkingConservativeReflectedPort
    (r : ThetaCuspHawkingBackreactionResonantMode) (transfer : ℝ) : ℝ :=
  thetaCuspHawkingBackreactionPortDissipation
      (thetaCuspHawkingBackreactionReflectedResonantMode r) - transfer

/-- Both members of a reflected resonance pair are passive after conservative transfer. -/
def ThetaCuspHawkingConservativePairPassive
    (r : ThetaCuspHawkingBackreactionResonantMode) (transfer : ℝ) : Prop :=
  0 ≤ thetaCuspHawkingConservativeForwardPort r transfer ∧
    0 ≤ thetaCuspHawkingConservativeReflectedPort r transfer

/-- Nonzero conservative transfer is the exact algebraic witness of reflected-sector mixing. -/
def ThetaCuspHawkingConservativePairMixes (transfer : ℝ) : Prop :=
  transfer ≠ 0

/-- A conservative correction leaves total reflected-pair power identically zero. -/
theorem thetaCuspHawkingConservativePair_totalPort_eq_zero
    (r : ThetaCuspHawkingBackreactionResonantMode) (transfer : ℝ) :
    thetaCuspHawkingConservativeForwardPort r transfer +
      thetaCuspHawkingConservativeReflectedPort r transfer = 0 := by
  rw [thetaCuspHawkingConservativeForwardPort,
    thetaCuspHawkingConservativeReflectedPort,
    thetaCuspHawkingBackreactionPortDissipation_reflected]
  ring

/-- **Unique conservative passive completion.** Both corrected ports are nonnegative exactly when
the transfer cancels the complete forward Hawking anomaly power. -/
theorem thetaCuspHawkingConservativePairPassive_iff
    (r : ThetaCuspHawkingBackreactionResonantMode) (transfer : ℝ) :
    ThetaCuspHawkingConservativePairPassive r transfer ↔
      transfer = -thetaCuspHawkingBackreactionPortDissipation r := by
  rw [ThetaCuspHawkingConservativePairPassive,
    thetaCuspHawkingConservativeForwardPort,
    thetaCuspHawkingConservativeReflectedPort,
    thetaCuspHawkingBackreactionPortDissipation_reflected]
  constructor
  · rintro ⟨hforward, hreflected⟩
    linarith
  · intro htransfer
    rw [htransfer]
    constructor <;> linarith

theorem existsUnique_thetaCuspHawkingConservativePairPassive
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    ∃! transfer : ℝ, ThetaCuspHawkingConservativePairPassive r transfer := by
  refine ⟨-thetaCuspHawkingBackreactionPortDissipation r,
    (thetaCuspHawkingConservativePairPassive_iff r _).mpr rfl, ?_⟩
  intro transfer htransfer
  exact (thetaCuspHawkingConservativePairPassive_iff r transfer).mp htransfer

/-- The unique transfer is coefficient-faithful: it cancels theta-source mass times tilt times
the full physical response energy. -/
theorem thetaCuspHawkingConservativePairPassive_transfer_eq
    (r : ThetaCuspHawkingBackreactionResonantMode) (transfer : ℝ)
    (hpassive : ThetaCuspHawkingConservativePairPassive r transfer) :
    transfer = -2 * thetaSource.mass * r.1.im *
      thetaCuspHawkingBackreactionPhysicalEnergy r := by
  rw [(thetaCuspHawkingConservativePairPassive_iff r transfer).mp hpassive,
    thetaCuspHawkingBackreactionPortDissipation_eq]
  ring

theorem thetaCuspHawkingBackreactionPortDissipation_ne_zero_iff
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingBackreactionPortDissipation r ≠ 0 ↔ r.1.im ≠ 0 := by
  rw [thetaCuspHawkingBackreactionPortDissipation_eq]
  have hmass : thetaSource.mass ≠ 0 := ne_of_gt thetaSource.mass_pos
  have henergy : thetaCuspHawkingBackreactionPhysicalEnergy r ≠ 0 :=
    ne_of_gt (thetaCuspHawkingBackreactionPhysicalEnergy_pos r)
  constructor
  · intro hdissipation him
    apply hdissipation
    rw [him]
    ring
  · intro him
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hmass) him) henergy

/-- Under conservative pair passivity, transfer is nonzero exactly off the neutral tilt. -/
theorem thetaCuspHawkingConservativePairMixes_iff_im_ne_zero
    (r : ThetaCuspHawkingBackreactionResonantMode) (transfer : ℝ)
    (hpassive : ThetaCuspHawkingConservativePairPassive r transfer) :
    ThetaCuspHawkingConservativePairMixes transfer ↔ r.1.im ≠ 0 := by
  rw [ThetaCuspHawkingConservativePairMixes,
    (thetaCuspHawkingConservativePairPassive_iff r transfer).mp hpassive]
  simpa using thetaCuspHawkingBackreactionPortDissipation_ne_zero_iff r

/-- At a tilted dark mode the only conservative passive correction cancels the entire modular
work found by the genuine Hawking backreaction gauge split. -/
theorem thetaCuspHawkingTiltedDarkMode_conservativePairPassive_iff
    {a w : ℝ}
    (hzero : thetaCuspHawkingTiltedDeembeddedPairCarrier a w = 0)
    (transfer : ℝ) :
    ThetaCuspHawkingConservativePairPassive
        (thetaCuspHawkingTiltedDarkBackreactionMode hzero) transfer ↔
      transfer = -(2 * thetaSource.mass * a *
        thetaCuspHawkingBackreactionPhysicalEnergy
          (thetaCuspHawkingTiltedDarkBackreactionMode hzero)) := by
  rw [thetaCuspHawkingConservativePairPassive_iff,
    thetaCuspHawkingTiltedDarkBackreactionMode_portDissipation_eq_modularWork]

/-- Zero-transfer sector-local passivity at one tilted dark mode is possible exactly at neutral
tilt. -/
theorem thetaCuspHawkingTiltedDarkMode_zeroTransfer_passive_iff
    {a w : ℝ}
    (hzero : thetaCuspHawkingTiltedDeembeddedPairCarrier a w = 0) :
    ThetaCuspHawkingConservativePairPassive
        (thetaCuspHawkingTiltedDarkBackreactionMode hzero) 0 ↔ a = 0 := by
  rw [thetaCuspHawkingTiltedDarkMode_conservativePairPassive_iff]
  constructor
  · intro hcancel
    have hproduct :
        2 * thetaSource.mass * a *
          thetaCuspHawkingBackreactionPhysicalEnergy
            (thetaCuspHawkingTiltedDarkBackreactionMode hzero) = 0 := by
      linarith
    by_contra ha
    exact (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt thetaSource.mass_pos)) ha)
      (ne_of_gt (thetaCuspHawkingBackreactionPhysicalEnergy_pos
        (thetaCuspHawkingTiltedDarkBackreactionMode hzero)))) hproduct
  · intro ha
    subst a
    ring

/-- Every nonzero tilted dark sector must mix with its reflected partner in any conservative
pair-passive completion. -/
theorem thetaCuspHawkingTiltedDarkMode_conservativePair_forces_mixing
    {a w : ℝ}
    (hzero : thetaCuspHawkingTiltedDeembeddedPairCarrier a w = 0)
    (ha : a ≠ 0) (transfer : ℝ)
    (hpassive : ThetaCuspHawkingConservativePairPassive
      (thetaCuspHawkingTiltedDarkBackreactionMode hzero) transfer) :
    ThetaCuspHawkingConservativePairMixes transfer := by
  apply (thetaCuspHawkingConservativePairMixes_iff_im_ne_zero
    (thetaCuspHawkingTiltedDarkBackreactionMode hzero) transfer hpassive).mpr
  rw [thetaCuspHawkingTiltedDarkBackreactionMode_coe,
    thetaCuspHawkingTiltedSpectralPoint_im]
  exact ha

/-- Closed all-sector form: conservative passivity forces every tilted theta-Hawking dark sector
to carry nonzero reflected-sector transfer. -/
def ThetaCuspHawkingAllTiltedConservativePairMixing : Prop :=
  ∀ (a w : ℝ)
    (hzero : thetaCuspHawkingTiltedDeembeddedPairCarrier a w = 0)
    (transfer : ℝ), a ≠ 0 →
    ThetaCuspHawkingConservativePairPassive
      (thetaCuspHawkingTiltedDarkBackreactionMode hzero) transfer →
    ThetaCuspHawkingConservativePairMixes transfer

theorem thetaCuspHawking_allTiltedConservativePairMixing :
    ThetaCuspHawkingAllTiltedConservativePairMixing := by
  intro a w hzero transfer ha hpassive
  exact thetaCuspHawkingTiltedDarkMode_conservativePair_forces_mixing
    hzero ha transfer hpassive

/-- Sector-locality is the RH-bearing alternative: requiring zero conservative transfer at every
two-ended theta-Hawking resonance is exactly RH. -/
def ThetaCuspHawkingConservativePairSectorLocal : Prop :=
  ∀ r : ThetaCuspHawkingBackreactionResonantMode,
    ThetaCuspHawkingConservativePairPassive r 0

theorem riemannHypothesis_iff_thetaCuspHawkingConservativePairSectorLocal :
    RiemannHypothesis ↔ ThetaCuspHawkingConservativePairSectorLocal := by
  constructor
  · intro hRH r
    have hpassive : ThetaCuspHawkingBackreactionResonancePassive :=
      riemannHypothesis_iff_thetaCuspHawkingBackreactionResonancePassive.mp hRH
    rw [ThetaCuspHawkingConservativePairPassive,
      thetaCuspHawkingConservativeForwardPort,
      thetaCuspHawkingConservativeReflectedPort]
    constructor
    · simpa using hpassive r
    · simpa using hpassive (thetaCuspHawkingBackreactionReflectedResonantMode r)
  · intro hlocal
    apply riemannHypothesis_iff_thetaCuspHawkingBackreactionResonancePassive.mpr
    intro r
    have hforward := (hlocal r).1
    simpa [thetaCuspHawkingConservativeForwardPort] using hforward

end

end RHTower
