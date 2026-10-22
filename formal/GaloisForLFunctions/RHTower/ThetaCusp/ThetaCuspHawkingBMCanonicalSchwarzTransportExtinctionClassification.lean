import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCanonicalLeftActionCovarianceEndpoint

open Complex

namespace RHTower

noncomputable section

/-- Coefficientwise complex conjugation on finite-support Xi packets. -/
def hbXiPeierlsPacketConjugation :
    HBXiPeierlsPacket →ₗ⋆[ℂ] HBXiPeierlsPacket where
  toFun x := Finsupp.mapRange (starRingEnd ℂ) (map_zero _) x
  map_add' x y := by
    ext q
    simp [Finsupp.mapRange_apply]
  map_smul' c x := by
    ext q
    simp [Finsupp.mapRange_apply, smul_eq_mul]

@[simp]
theorem hbXiPeierlsPacketConjugation_apply
    (x : HBXiPeierlsPacket) (q : XiZeroCopy) :
    hbXiPeierlsPacketConjugation x q = (starRingEnd ℂ) (x q) := by
  simp [hbXiPeierlsPacketConjugation, Finsupp.mapRange_apply]

theorem hbXiPeierlsPacketConjugation_single
    (q : XiZeroCopy) (c : ℂ) :
    hbXiPeierlsPacketConjugation (Finsupp.single q c) =
      Finsupp.single q ((starRingEnd ℂ) c) := by
  change Finsupp.mapRange (starRingEnd ℂ) (map_zero _)
      (Finsupp.single q c) = _
  rw [Finsupp.mapRange_single]

/-- Genuine Schwarz operation on the two-channel carrier: conjugate coefficients and exchange
the regular/complementary axes. -/
def hbXiPeierlsCanonicalChannelSchwarz :
    HBXiPeierlsCarrier →ₗ⋆[ℂ] HBXiPeierlsCarrier where
  toFun x :=
    (hbXiPeierlsPacketConjugation x.2,
      hbXiPeierlsPacketConjugation x.1)
  map_add' x y := by
    apply Prod.ext <;> simp
  map_smul' c x := by
    apply Prod.ext <;> simp

@[simp]
theorem hbXiPeierlsCanonicalChannelSchwarz_apply
    (x : HBXiPeierlsCarrier) :
    hbXiPeierlsCanonicalChannelSchwarz x =
      (hbXiPeierlsPacketConjugation x.2,
        hbXiPeierlsPacketConjugation x.1) := rfl

/-- Schwarz channel exchange is an involution. -/
theorem hbXiPeierlsCanonicalChannelSchwarz_involutive
    (x : HBXiPeierlsCarrier) :
    hbXiPeierlsCanonicalChannelSchwarz
        (hbXiPeierlsCanonicalChannelSchwarz x) = x := by
  apply Prod.ext <;> ext q <;>
    simp [hbXiPeierlsCanonicalChannelSchwarz_apply]

private theorem hbXiPeierlsDot_packetConjugation
    (x y : HBXiPeierlsPacket) :
    hbXiPeierlsDot (hbXiPeierlsPacketConjugation x)
        (hbXiPeierlsPacketConjugation y) =
      (starRingEnd ℂ) (hbXiPeierlsDot x y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [hbXiPeierlsDot]
  | add f g hf hg =>
      rw [map_add, hbXiPeierlsDot_add_left, hf, hg,
        hbXiPeierlsDot_add_left, map_add]
  | single q c =>
      rw [hbXiPeierlsPacketConjugation_single,
        hbXiPeierlsDot_single, hbXiPeierlsDot_single,
        hbXiPeierlsPacketConjugation_apply, map_mul]

/-- Carrier pairing is Schwarz-real: channel exchange conjugates its value. -/
theorem hbXiPeierlsPairing_channelSchwarz
    (x y : HBXiPeierlsCarrier) :
    hbXiPeierlsPairing (hbXiPeierlsCanonicalChannelSchwarz x)
        (hbXiPeierlsCanonicalChannelSchwarz y) =
      (starRingEnd ℂ) (hbXiPeierlsPairing x y) := by
  rw [hbXiPeierlsPairing_apply, hbXiPeierlsPairing_apply,
    hbXiPeierlsCanonicalChannelSchwarz_apply,
    hbXiPeierlsCanonicalChannelSchwarz_apply,
    hbXiPeierlsDot_packetConjugation,
    hbXiPeierlsDot_packetConjugation, map_add]
  ring

/-- Genuine channel Schwarz transport sends every plus packet to its matching minus packet,
without a critical-line premise. -/
theorem hbXiPeierlsCanonicalChannelSchwarz_plusSource
    (amplitude : ℂ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalChannelSchwarz (hbXiPeierlsPlusSource amplitude q) =
      hbXiPeierlsMinusSource amplitude q := by
  apply Prod.ext
  · simp [hbXiPeierlsPlusSource, hbXiPeierlsMinusSource,
      hbXiPeierlsCanonicalChannelSchwarz_apply]
  · rw [hbXiPeierlsPlusSource, hbXiPeierlsMinusSource,
      hbXiPeierlsCanonicalChannelSchwarz_apply,
      hbXiPeierlsPacketConjugation_single]

theorem hbXiPeierlsCanonicalChannelSchwarz_minusSource
    (amplitude : ℂ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalChannelSchwarz (hbXiPeierlsMinusSource amplitude q) =
      hbXiPeierlsPlusSource amplitude q := by
  rw [← hbXiPeierlsCanonicalChannelSchwarz_plusSource amplitude q,
    hbXiPeierlsCanonicalChannelSchwarz_involutive]

/-- Canonical left-coordinate packets obey genuine Schwarz transport on every Xi fibre. -/
theorem hbXiPeierlsCanonicalChannelSchwarz_plusLeftSource
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalChannelSchwarz
        (hbXiPeierlsPlusLeftSource n amplitude q) =
      hbXiPeierlsMinusLeftSource n amplitude q := by
  rw [hbXiPeierlsPlusLeftSource_eq, hbXiPeierlsMinusLeftSource_eq,
    hbXiPeierlsCanonicalChannelSchwarz_plusSource]

theorem hbXiPeierlsCanonicalChannelSchwarz_minusLeftSource
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalChannelSchwarz
        (hbXiPeierlsMinusLeftSource n amplitude q) =
      hbXiPeierlsPlusLeftSource n amplitude q := by
  rw [hbXiPeierlsPlusLeftSource_eq, hbXiPeierlsMinusLeftSource_eq,
    hbXiPeierlsCanonicalChannelSchwarz_minusSource]

/-- A plus-axis packet can literally equal a minus-axis packet only by simultaneous extinction. -/
theorem hbXiPeierlsPlusSource_eq_minusSource_iff_both_zero
    (amplitude : ℂ) (r q : XiZeroCopy) :
    hbXiPeierlsPlusSource amplitude r = hbXiPeierlsMinusSource amplitude q ↔
      hbXiPeierlsPlusSource amplitude r = 0 ∧
        hbXiPeierlsMinusSource amplitude q = 0 := by
  constructor
  · intro h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    constructor
    · apply Prod.ext
      · exact hfst
      · rfl
    · apply Prod.ext
      · rfl
      · exact hsnd.symm
  · rintro ⟨hplus, hminus⟩
    rw [hplus, hminus]

theorem hbXiPeierlsPlusSource_eq_zero_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    hbXiPeierlsPlusSource amplitude q = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsPlusSource]
  simp [d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff ha q]

theorem hbXiPeierlsMinusSource_eq_zero_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    hbXiPeierlsMinusSource amplitude q = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsMinusSource]
  simp [d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff ha q]

/-- Existing reflected left-source equality is not a nonzero exchange: it is exactly extinction
of both direct-sum axes. -/
theorem hbXiPeierlsCanonicalLeftSource_reflect_eq_iff_both_zero
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    hbXiPeierlsPlusLeftSource n amplitude (xiZeroCopyReflectEquiv q) =
        hbXiPeierlsMinusLeftSource n amplitude q ↔
      hbXiPeierlsPlusLeftSource n amplitude (xiZeroCopyReflectEquiv q) = 0 ∧
        hbXiPeierlsMinusLeftSource n amplitude q = 0 := by
  simpa only [hbXiPeierlsPlusLeftSource_eq, hbXiPeierlsMinusLeftSource_eq] using
    hbXiPeierlsPlusSource_eq_minusSource_iff_both_zero amplitude
      (xiZeroCopyReflectEquiv q) q

theorem hbXiPeierlsCanonicalLeftSource_reflect_both_zero_iff
    (n : ℕ) {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    (hbXiPeierlsPlusLeftSource n amplitude (xiZeroCopyReflectEquiv q) = 0 ∧
        hbXiPeierlsMinusLeftSource n amplitude q = 0) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [← hbXiPeierlsCanonicalLeftSource_reflect_eq_iff_both_zero,
    hbXiPeierlsCanonicalLeftSource_reflect_eq_iff n ha q]

/-- Off wall, genuine Schwarz transport still exchanges two nonzero packets; literal equality
fails because the packets inhabit distinct channel axes. -/
theorem hbXiPeierlsCanonicalChannelSchwarz_tilted_nonzeroExchange
    (n : ℕ) {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    hbXiPeierlsCanonicalChannelSchwarz
          (hbXiPeierlsPlusLeftSource n amplitude q) =
        hbXiPeierlsMinusLeftSource n amplitude q ∧
      hbXiPeierlsPlusLeftSource n amplitude q ≠ 0 ∧
      hbXiPeierlsMinusLeftSource n amplitude q ≠ 0 ∧
      hbXiPeierlsPlusLeftSource n amplitude q ≠
        hbXiPeierlsMinusLeftSource n amplitude q := by
  have hplus : hbXiPeierlsPlusLeftSource n amplitude q ≠ 0 := by
    rw [hbXiPeierlsPlusLeftSource_eq]
    exact (hbXiPeierlsPlusSource_eq_zero_iff ha q).not.mpr htilt
  have hminus : hbXiPeierlsMinusLeftSource n amplitude q ≠ 0 := by
    rw [hbXiPeierlsMinusLeftSource_eq]
    exact (hbXiPeierlsMinusSource_eq_zero_iff ha q).not.mpr htilt
  refine ⟨hbXiPeierlsCanonicalChannelSchwarz_plusLeftSource n amplitude q,
    hplus, hminus, ?_⟩
  intro heq
  have hzero := (hbXiPeierlsPlusSource_eq_minusSource_iff_both_zero amplitude q q).mp
    (by simpa only [hbXiPeierlsPlusLeftSource_eq,
      hbXiPeierlsMinusLeftSource_eq] using heq)
  exact hplus (by simpa only [hbXiPeierlsPlusLeftSource_eq] using hzero.1)

/-- Genuine channel-transport covariance is unconditional. -/
def HBXiPeierlsCanonicalLeftChannelSchwarzTransport (n : ℕ) : Prop :=
  ∀ q : XiZeroCopy,
    hbXiPeierlsCanonicalChannelSchwarz (hbXiPeierlsPlusLeftSource n 1 q) =
      hbXiPeierlsMinusLeftSource n 1 q

theorem hbXiPeierlsCanonicalLeftChannelSchwarzTransport_holds (n : ℕ) :
    HBXiPeierlsCanonicalLeftChannelSchwarzTransport n := by
  intro q
  exact hbXiPeierlsCanonicalChannelSchwarz_plusLeftSource n 1 q

/-- By contrast, the old universal equality endpoint is precisely global simultaneous source
extinction, hence remains the RH receiver. -/
theorem hbXiPeierlsCanonicalLeftBranchCovariance_iff_globalSourceExtinction
    (n : ℕ) :
    HBXiPeierlsCanonicalLeftBranchCovariance n ↔
      ∀ q : XiZeroCopy,
        hbXiPeierlsPlusLeftSource n 1 (xiZeroCopyReflectEquiv q) = 0 ∧
          hbXiPeierlsMinusLeftSource n 1 q = 0 := by
  unfold HBXiPeierlsCanonicalLeftBranchCovariance
  constructor
  · intro h q
    exact (hbXiPeierlsCanonicalLeftSource_reflect_eq_iff_both_zero n 1 q).mp (h q)
  · intro h q
    exact (hbXiPeierlsCanonicalLeftSource_reflect_eq_iff_both_zero n 1 q).mpr (h q)

theorem hbXiPeierlsCanonicalLeft_globalSourceExtinction_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      hbXiPeierlsPlusLeftSource n 1 (xiZeroCopyReflectEquiv q) = 0 ∧
        hbXiPeierlsMinusLeftSource n 1 q = 0) ↔ RiemannHypothesis := by
  rw [← hbXiPeierlsCanonicalLeftBranchCovariance_iff_globalSourceExtinction]
  exact hbXiPeierlsCanonicalLeftBranchCovariance_iff_rh n

/-- Final classification: physically typed Schwarz exchange holds unconditionally, whereas
untransported cross-axis equality is exactly the global extinction/RH endpoint. -/
theorem hbXiPeierlsCanonicalSchwarzTransport_vs_extinction (n : ℕ) :
    HBXiPeierlsCanonicalLeftChannelSchwarzTransport n ∧
      ((∀ q : XiZeroCopy,
        hbXiPeierlsPlusLeftSource n 1 (xiZeroCopyReflectEquiv q) = 0 ∧
          hbXiPeierlsMinusLeftSource n 1 q = 0) ↔ RiemannHypothesis) := by
  exact ⟨hbXiPeierlsCanonicalLeftChannelSchwarzTransport_holds n,
    hbXiPeierlsCanonicalLeft_globalSourceExtinction_iff_rh n⟩

end

end RHTower
