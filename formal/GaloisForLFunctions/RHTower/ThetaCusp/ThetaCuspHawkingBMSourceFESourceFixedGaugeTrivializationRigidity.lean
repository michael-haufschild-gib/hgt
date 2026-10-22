import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFELinearAntilinearClockReflectionCoherence

/-!
# Source-fixed gauge trivialization rigidity

The literal source-FE cocycle is algebraically gauge-trivial on every Xi orbit.  An explicit
nowhere-zero diagonal gauge is the polarized source amplitude itself away from its extinction wall,
and one on the wall.  Exact source transport then makes the transformed cocycle identically one;
the conjugated packet transport becomes pure reflection plus coefficient conjugation.

This algebraic Hilbert-90 trivialization is not a physical source normalization.  Any diagonal
gauge that leaves literal source coordinates fixed must equal one at every off-critical copy and
its reflection.  It therefore leaves the nonreal source cocycle unchanged off wall.  A global
nowhere-zero source-fixed gauge whose transformed cocycle is real exists exactly under RH.

`[NEW] [SOURCE GAUGE] [HILBERT 90] [PHYSICAL RIGIDITY] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Anti-linear source-FE coefficient after a diagonal complex change of packet basis. -/
def hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle
    (b : XiZeroCopy → ℂ) (q : XiZeroCopy) : ℂ :=
  (b (xiZeroCopyReflectEquiv q))⁻¹ * hbXiPeierlsUnitSourceFECocycle q *
    (starRingEnd ℂ) (b q)

/-- Diagonal conjugation of literal anti-linear source-FE packet transport. -/
def hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFETransport
    (b : XiZeroCopy → ℂ) (x : HBXiPeierlsPacket) : HBXiPeierlsPacket :=
  hbXiPeierlsWeightedPacket (fun q => (b q)⁻¹)
    (hbXiPeierlsUnitSourceFEPacketTransport
      (hbXiPeierlsWeightedPacket b x))

/-- Exact packet coefficient formula for diagonal gauge conjugation. -/
theorem hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFETransport_apply
    (b : XiZeroCopy → ℂ) (x : HBXiPeierlsPacket) (r : XiZeroCopy) :
    hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFETransport b x r =
      hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle b
          (xiZeroCopyReflectEquiv r) *
        (starRingEnd ℂ) (x (xiZeroCopyReflectEquiv r)) := by
  simp [hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFETransport,
    hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle, map_mul]
  ring

/-- Explicit source-amplitude Hilbert-90 gauge, with unit value on the source-extinction wall. -/
def hbXiPeierlsUnitSourceAmplitudeGauge (q : XiZeroCopy) : ℂ :=
  if d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q = 0 then 1
  else d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q

/-- The explicit amplitude gauge is nowhere zero. -/
theorem hbXiPeierlsUnitSourceAmplitudeGauge_ne_zero (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceAmplitudeGauge q ≠ 0 := by
  rw [hbXiPeierlsUnitSourceAmplitudeGauge]
  split_ifs with h
  · norm_num
  · exact h

private theorem hc60_unitSource_reflect_ne_zero
    (q : XiZeroCopy)
    (h : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q ≠ 0) :
    d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
      (xiZeroCopyReflectEquiv q) ≠ 0 := by
  intro hR
  have hRline :=
    (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero
      (xiZeroCopyReflectEquiv q)).mp hR
  rw [xiZeroCopyReflect_re_eq_one_sub] at hRline
  have hline : (q.1 : ℂ).re = 1 / 2 := by linarith
  exact h
    ((d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr hline)

/-- Source amplitude explicitly trivializes the literal anti-linear FE cocycle on every copy. -/
theorem hbXiPeierlsUnitSourceAmplitudeGauge_trivializes_cocycle
    (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle
        hbXiPeierlsUnitSourceAmplitudeGauge q = 1 := by
  by_cases hq : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q = 0
  · have hline :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mp hq
    have hRline :
        ((xiZeroCopyReflectEquiv q).1 : ℂ).re = 1 / 2 := by
      rw [xiZeroCopyReflect_re_eq_one_sub]
      linarith
    have hRq :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero
        (xiZeroCopyReflectEquiv q)).mpr hRline
    simp [hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle,
      hbXiPeierlsUnitSourceAmplitudeGauge, hbXiPeierlsUnitSourceFECocycle, hq, hRq]
  · have hRq := hc60_unitSource_reflect_ne_zero q hq
    rw [hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle]
    simp only [hbXiPeierlsUnitSourceAmplitudeGauge, if_neg hq, if_neg hRq]
    rw [mul_assoc, hbXiPeierlsUnitSourceFECocycle_sourceTransport]
    exact inv_mul_cancel₀ hRq

/-- In the amplitude gauge, literal source-FE transport is pure reflection and conjugation. -/
theorem hbXiPeierlsUnitSourceAmplitudeGauge_conjugatedTransport_apply
    (x : HBXiPeierlsPacket) (r : XiZeroCopy) :
    hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFETransport
        hbXiPeierlsUnitSourceAmplitudeGauge x r =
      (starRingEnd ℂ) (x (xiZeroCopyReflectEquiv r)) := by
  rw [hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFETransport_apply,
    hbXiPeierlsUnitSourceAmplitudeGauge_trivializes_cocycle, one_mul]

/-- A diagonal gauge fixes the literal nonlinear source coordinates pointwise. -/
def HBXiPeierlsUnitSourceDiagonalGaugeFixed
    (b : XiZeroCopy → ℂ) : Prop :=
  ∀ q : XiZeroCopy,
    b q * d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q =
      d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q

/-- Source-fixed gauges are forced to one at every off-critical copy. -/
theorem hbXiPeierlsUnitSourceDiagonalGauge_eq_one_of_fixed_of_offLine
    {b : XiZeroCopy → ℂ} (hfixed : HBXiPeierlsUnitSourceDiagonalGaugeFixed b)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    b q = 1 := by
  have hsource : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q ≠ 0 :=
    (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).not.mpr hoff
  apply mul_right_cancel₀ hsource
  simpa using hfixed q

/-- A source-fixed gauge leaves literal source-FE cocycle unchanged off critical line. -/
theorem hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle_eq_of_fixed_of_offLine
    {b : XiZeroCopy → ℂ} (hfixed : HBXiPeierlsUnitSourceDiagonalGaugeFixed b)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle b q =
      hbXiPeierlsUnitSourceFECocycle q := by
  have hoffR : ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≠ 1 / 2 := by
    rw [xiZeroCopyReflect_re_eq_one_sub]
    intro h
    apply hoff
    linarith
  rw [hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle,
    hbXiPeierlsUnitSourceDiagonalGauge_eq_one_of_fixed_of_offLine hfixed q hoff,
    hbXiPeierlsUnitSourceDiagonalGauge_eq_one_of_fixed_of_offLine hfixed
      (xiZeroCopyReflectEquiv q) hoffR]
  simp

/-- Reality of a source-fixed gauged cocycle forces critical-line placement. -/
theorem hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle_real_implies_line_of_fixed
    {b : XiZeroCopy → ℂ} (hfixed : HBXiPeierlsUnitSourceDiagonalGaugeFixed b)
    (q : XiZeroCopy)
    (hreal : (hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle b q).im = 0) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hoff
  rw [hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle_eq_of_fixed_of_offLine
    hfixed q hoff] at hreal
  exact hoff ((hbXiPeierlsUnitSourceFECocycle_im_eq_zero_iff q).mp hreal)

/-- No source-fixed diagonal gauge can trivialize the cocycle at an off-critical copy. -/
theorem hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle_ne_one_of_fixed_of_offLine
    {b : XiZeroCopy → ℂ} (hfixed : HBXiPeierlsUnitSourceDiagonalGaugeFixed b)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle b q ≠ 1 := by
  intro hone
  have hreal : (hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle b q).im = 0 := by
    rw [hone]
    norm_num
  exact hoff
    (hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle_real_implies_line_of_fixed
      hfixed q hreal)

/-- Existence of one global nowhere-zero, source-fixed real cocycle trivialization. -/
def HBXiPeierlsUnitSourceFixedRealGaugeTrivialization : Prop :=
  ∃ b : XiZeroCopy → ℂ,
    (∀ q : XiZeroCopy, b q ≠ 0) ∧
    HBXiPeierlsUnitSourceDiagonalGaugeFixed b ∧
    (∀ q : XiZeroCopy,
      (hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle b q).im = 0)

/-- Global physical source-fixed real trivialization exists exactly under RH. -/
theorem hbXiPeierlsUnitSourceFixedRealGaugeTrivialization_iff_rh :
    HBXiPeierlsUnitSourceFixedRealGaugeTrivialization ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨b, _hb, hfixed, hreal⟩
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    exact hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle_real_implies_line_of_fixed
      hfixed q (hreal q)
  · intro hRH
    refine ⟨fun _ => 1, ?_, ?_, ?_⟩
    · intro q
      norm_num
    · intro q
      simp
    · intro q
      have hline : (q.1 : ℂ).re = 1 / 2 :=
        (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp
          ((forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr hRH q)
      simpa [hbXiPeierlsUnitSourceFEDiagonalGaugedCocycle] using
        (hbXiPeierlsUnitSourceFECocycle_im_eq_zero_iff q).mpr hline

end

end RHTower
