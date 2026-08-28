import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadiativeSourceFEPositiveHermitianMetricNoGo

/-!
# Unit-phase realification of actual radiative source-FE transport: no-go

HC90 proves positivity and Hermiticity cannot select critical-line copies. This module attacks
stronger surviving proposal: demand a real functional-equation coefficient. Actual nonlinear BM
raw Ward amplitude supplies a canonical polar phase gauge. It is globally nowhere zero and unit
modulus, reconstructs raw amplitude from its norm, and conjugates actual Green/source-FE transport.

At every off-line Xi copy, the gauged radiative cocycle is exactly its strictly positive norm.
The full finite-packet conjugated transport therefore has positive-real reflected coefficients and
remains an anti-linear involution, while HC89's two physical Ward channels remain bright and cancel.

Thus reflection-reality is not coordinate invariant under unitary source-following phase gauges.
Surviving RH-bearing burden must fix phase reference independently of divisor/source amplitude or
derive such fixing from local detector algebra.

`[NEW] [UNIT PHASE GAUGE] [POSITIVE REALIFICATION] [PACKET INVOLUTION] [NO-GO]`
-/

open Complex Real

namespace RHTower

noncomputable section

def hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude (q : XiZeroCopy) : ℂ :=
  d4BMMixedHorizonOpticalSourceProjection 1 0 q

def hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge (q : XiZeroCopy) : ℂ :=
  if hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude q = 0 then 1 else hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude q / (‖hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude q‖ : ℂ)

def hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle
    (b : XiZeroCopy → ℂ) (q : XiZeroCopy) : ℂ :=
  (b (xiZeroCopyReflectEquiv q))⁻¹ *
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q *
      (starRingEnd ℂ) (b q)

def hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle (q : XiZeroCopy) : ℂ :=
  hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge q

theorem hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude_ne_zero_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude q ≠ 0 := by
  exact (d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_re_eq_half
    one_ne_zero 0 q).not.mpr (by
      simpa only [deningerDivisorThetaEigen] using hoff)

theorem hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge_ne_zero (q : XiZeroCopy) : hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge q ≠ 0 := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge]
  split_ifs with h
  · norm_num
  · exact div_ne_zero h (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h))

theorem hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge_norm (q : XiZeroCopy) : ‖hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge q‖ = 1 := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge]
  split_ifs with h
  · simp
  · simp [norm_ne_zero_iff.mpr h]

theorem hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge_mul_norm (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge q * (‖hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude q‖ : ℂ) = hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude q := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge]
  split_ifs with h
  · simp [h]
  · field_simp [norm_ne_zero_iff.mpr h]

theorem hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge_eq_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge q = hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude q / (‖hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude q‖ : ℂ) := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge, if_neg (hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude_ne_zero_of_offLine q hoff)]

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle_eq_norm_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle q =
      (‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q‖ : ℂ) := by
  have hoffR : ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≠ 1 / 2 := by
    rw [xiZeroCopyReflect_re_eq_one_sub]
    intro h
    apply hoff
    linarith
  have hP := hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude_ne_zero_of_offLine q hoff
  have hPR := hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude_ne_zero_of_offLine (xiZeroCopyReflectEquiv q) hoffR
  have hk := hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_ne_zero q
  have htransport :
      hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q *
          (starRingEnd ℂ) (hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude q) =
        hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude (xiZeroCopyReflectEquiv q) := by
    exact hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_transport 0 q
  have hnormP :
      ‖hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude (xiZeroCopyReflectEquiv q)‖ =
        ‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q‖ * ‖hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude q‖ := by
    simpa [norm_mul] using (congrArg norm htransport).symm
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle, hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle,
    hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge_eq_of_offLine q hoff,
    hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge_eq_of_offLine (xiZeroCopyReflectEquiv q) hoffR,
    hnormP, ← htransport]
  rw [map_div₀, Complex.conj_ofReal]
  field_simp [hP, hk, norm_ne_zero_iff.mpr hP,
    norm_ne_zero_iff.mpr hk]
  push_cast
  ring

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle_im_eq_zero_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    (hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle q).im = 0 := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle_eq_norm_of_offLine q hoff]
  simp

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle_re_pos_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < (hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle q).re := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle_eq_norm_of_offLine q hoff]
  simpa using norm_pos_iff.mpr
    (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_ne_zero q)

def hbXiPhaseSensitiveUnitRadiativeSourceFEGaugeConjugatedPacketTransport (b : XiZeroCopy → ℂ) :
    HBXiPeierlsPacket →ₗ⋆[ℂ] HBXiPeierlsPacket where
  toFun x :=
    hbXiPeierlsWeightedPacket (fun q => (b q)⁻¹)
      (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport
        (hbXiPeierlsWeightedPacket b x))
  map_add' x y := by
    ext q
    simp
  map_smul' c x := by
    ext q
    simp [smul_eq_mul]
    ring

@[simp]
theorem hbXiPhaseSensitiveUnitRadiativeSourceFEGaugeConjugatedPacketTransport_apply
    (b : XiZeroCopy → ℂ) (x : HBXiPeierlsPacket) (r : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEGaugeConjugatedPacketTransport b x r =
      hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle b (xiZeroCopyReflectEquiv r) *
        (starRingEnd ℂ) (x (xiZeroCopyReflectEquiv r)) := by
  simp [hbXiPhaseSensitiveUnitRadiativeSourceFEGaugeConjugatedPacketTransport, hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle, map_mul]
  ring

theorem hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGaugeConjugatedPacketTransport_apply_of_offLine
    (x : HBXiPeierlsPacket) (r : XiZeroCopy)
    (hoff : (r.1 : ℂ).re ≠ 1 / 2) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEGaugeConjugatedPacketTransport hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge x r =
      (‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle
          (xiZeroCopyReflectEquiv r)‖ : ℂ) *
        (starRingEnd ℂ) (x (xiZeroCopyReflectEquiv r)) := by
  have hoffR : ((xiZeroCopyReflectEquiv r).1 : ℂ).re ≠ 1 / 2 := by
    rw [xiZeroCopyReflect_re_eq_one_sub]
    intro h
    apply hoff
    linarith
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEGaugeConjugatedPacketTransport_apply,
    ← hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle,
    hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle_eq_norm_of_offLine (xiZeroCopyReflectEquiv r) hoffR]

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle_involutive
    (b : XiZeroCopy → ℂ) (hb : ∀ q : XiZeroCopy, b q ≠ 0)
    (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle b (xiZeroCopyReflectEquiv q) *
        (starRingEnd ℂ) (hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle b q) = 1 := by
  have hcocycle :=
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_involutive q
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle, hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle,
    xiZeroCopyReflectEquiv_apply_apply, map_mul, map_mul, map_inv₀]
  field_simp [hb q, hb (xiZeroCopyReflectEquiv q)]
  rw [hcocycle]
  ring_nf
  simp

theorem hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGaugeConjugatedPacketTransport_involutive
    (x : HBXiPeierlsPacket) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEGaugeConjugatedPacketTransport hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge
        (hbXiPhaseSensitiveUnitRadiativeSourceFEGaugeConjugatedPacketTransport hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge x) = x := by
  ext q
  simp only [hbXiPhaseSensitiveUnitRadiativeSourceFEGaugeConjugatedPacketTransport_apply,
    xiZeroCopyReflectEquiv_apply_apply, map_mul]
  have hcocycle := hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle_involutive
    hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge_ne_zero q
  have hcc : (starRingEnd ℂ) ((starRingEnd ℂ) (x q)) = x q := by simp
  rw [hcc, ← mul_assoc, hcocycle, one_mul]

def HBXiPhaseSensitiveUnitRadiativeSourceFEUnitPhasePositiveRealBrightCancellation : Prop :=
  HBXiPhaseSensitiveUnitRadiativeSourceFEBrightCancellation ∧
  (∀ q : XiZeroCopy,
    hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge q ≠ 0 ∧
    ‖hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge q‖ = 1 ∧
    hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge q * (‖hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude q‖ : ℂ) = hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude q) ∧
  (∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
    hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle q =
        (‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q‖ : ℂ) ∧
    0 < (hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle q).re ∧
    (hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle q).im = 0) ∧
  (∀ x : HBXiPeierlsPacket,
    hbXiPhaseSensitiveUnitRadiativeSourceFEGaugeConjugatedPacketTransport hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge
        (hbXiPhaseSensitiveUnitRadiativeSourceFEGaugeConjugatedPacketTransport hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge x) = x) ∧
  (∀ x : HBXiPeierlsPacket, ∀ r : XiZeroCopy,
    (r.1 : ℂ).re ≠ 1 / 2 →
      hbXiPhaseSensitiveUnitRadiativeSourceFEGaugeConjugatedPacketTransport hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge x r =
        (‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle
            (xiZeroCopyReflectEquiv r)‖ : ℂ) *
          (starRingEnd ℂ) (x (xiZeroCopyReflectEquiv r)))

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEUnitPhasePositiveRealBrightCancellation : HBXiPhaseSensitiveUnitRadiativeSourceFEUnitPhasePositiveRealBrightCancellation := by
  refine ⟨hbXiPhaseSensitiveUnitRadiativeSourceFEBrightCancellation,
    ?_, ?_, hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGaugeConjugatedPacketTransport_involutive, ?_⟩
  · intro q
    exact ⟨hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge_ne_zero q, hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge_norm q,
      hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGauge_mul_norm q⟩
  · intro q hoff
    exact ⟨hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle_eq_norm_of_offLine q hoff,
      hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle_re_pos_of_offLine q hoff,
      hbXiPhaseSensitiveUnitRadiativeSourceFEPhaseGaugedCocycle_im_eq_zero_of_offLine q hoff⟩
  · intro x r hoff
    exact hbXiPhaseSensitiveUnitRadiativeSourceFERawPhaseGaugeConjugatedPacketTransport_apply_of_offLine x r hoff

end

end RHTower

