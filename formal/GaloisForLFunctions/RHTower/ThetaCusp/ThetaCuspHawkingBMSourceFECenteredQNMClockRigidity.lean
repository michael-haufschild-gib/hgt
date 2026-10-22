import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFEQNMGeneratorLocalityNoGo

/-!
# Source-FE centered-QNM clock anticommutator rigidity

After removing the fixed overtone/redshift offset, the literal Birmingham--Mokhtari QNM frequency
is half the centered Xi spectral coordinate.  Functional-equation reflection negates this clock,
but the literal source transport is anti-linear.  Their anticommutator is therefore not zero: it is
exactly the reflected finite-packet coefficient multiplied by the Xi tilt and the nowhere-vanishing
source cocycle.

The defect vanishes on one unit basis packet exactly on the critical line.  Its global vanishing,
equivalently anticommutation of source-FE transport with the centered QNM generator, is equivalent
to RH.  This is the exact reflection-coupled clock Ward charge left after HC56 exhausted ordinary
time-translation conservation.

`[NEW] [SOURCE-FE CLOCK] [EXACT ANTICOMMUTATOR] [RH EQUIVALENCE] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Literal BM QNM frequency after removing its fixed overtone/redshift offset. -/
def hbXiPeierlsCenteredQNMFrequency (n : ℕ) (q : XiZeroCopy) : ℂ :=
  hbXiPeierlsQNMFrequency n q -
    (Complex.I / 4 - Complex.I *
      thetaCuspHawkingTopologicalBlackHoleConformalDecay n)

/-- Centering removes every overtone dependence and leaves half the Xi spectral coordinate. -/
theorem hbXiPeierlsCenteredQNMFrequency_eq (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsCenteredQNMFrequency n q = xiSpectralPoint q / 2 := by
  rw [hbXiPeierlsCenteredQNMFrequency, hbXiPeierlsQNMFrequency_eq]
  simp only [xiSpectralPoint]
  ring

theorem hbXiPeierlsCenteredQNMFrequency_reflect (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsCenteredQNMFrequency n (xiZeroCopyReflectEquiv q) =
      -hbXiPeierlsCenteredQNMFrequency n q := by
  rw [hbXiPeierlsCenteredQNMFrequency_eq,
    hbXiPeierlsCenteredQNMFrequency_eq, xiSpectralPoint_reflect]
  ring

/-- Anti-linearity plus FE reflection leaves exactly the transverse Xi tilt. -/
theorem hbXiPeierlsCenteredQNMFrequency_conj_add_reflect
    (n : ℕ) (q : XiZeroCopy) :
    (starRingEnd ℂ) (hbXiPeierlsCenteredQNMFrequency n q) +
        hbXiPeierlsCenteredQNMFrequency n (xiZeroCopyReflectEquiv q) =
      Complex.I * ((((q.1 : ℂ).re - 1 / 2 : ℝ) : ℂ)) := by
  rw [hbXiPeierlsCenteredQNMFrequency_reflect,
    hbXiPeierlsCenteredQNMFrequency_eq]
  simp only [map_div₀, map_ofNat]
  apply Complex.ext
  · norm_num [xiSpectralPoint, Complex.div_re, Complex.mul_re, Complex.mul_im]
  · norm_num [xiSpectralPoint, Complex.div_re, Complex.mul_re, Complex.mul_im]
    ring

/-- Centered BM QNM generator on finite Xi source packets. -/
def hbXiPeierlsCenteredQNMTimeGenerator (n : ℕ) :
    HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket :=
  hbXiPeierlsWeightedPacketLinear (hbXiPeierlsCenteredQNMFrequency n)

@[simp]
theorem hbXiPeierlsCenteredQNMTimeGenerator_single
    (n : ℕ) (q : XiZeroCopy) (c : ℂ) :
    hbXiPeierlsCenteredQNMTimeGenerator n (Finsupp.single q c) =
      Finsupp.single q (hbXiPeierlsCenteredQNMFrequency n q * c) := by
  exact hbXiPeierlsWeightedPacket_single _ q c

@[simp]
theorem hbXiPeierlsCenteredQNMTimeGenerator_apply
    (n : ℕ) (x : HBXiPeierlsPacket) (q : XiZeroCopy) :
    hbXiPeierlsCenteredQNMTimeGenerator n x q =
      hbXiPeierlsCenteredQNMFrequency n q * x q := by
  exact hbXiPeierlsWeightedPacket_apply _ x q

/-- Literal normalized source-FE cocycle never vanishes. -/
theorem hbXiPeierlsUnitSourceFECocycle_ne_zero (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFECocycle q ≠ 0 := by
  intro hzero
  have hinv := hbXiPeierlsUnitSourceFECocycle_involutive q
  rw [hzero, map_zero, mul_zero] at hinv
  norm_num at hinv

/-- Anticommutator of anti-linear source-FE transport and centered QNM time translation. -/
def hbXiPeierlsSourceFECenteredQNMClockDefect
    (n : ℕ) (x : HBXiPeierlsPacket) : HBXiPeierlsPacket :=
  hbXiPeierlsUnitSourceFEPacketTransport
      (hbXiPeierlsCenteredQNMTimeGenerator n x) +
    hbXiPeierlsCenteredQNMTimeGenerator n
      (hbXiPeierlsUnitSourceFEPacketTransport x)

/-- On a basis packet the reflection-coupled clock defect is exactly the Xi tilt times the literal
source cocycle. -/
theorem hbXiPeierlsSourceFECenteredQNMClockDefect_single
    (n : ℕ) (q : XiZeroCopy) (c : ℂ) :
    hbXiPeierlsSourceFECenteredQNMClockDefect n (Finsupp.single q c) =
      Finsupp.single (xiZeroCopyReflectEquiv q)
        (Complex.I * ((((q.1 : ℂ).re - 1 / 2 : ℝ) : ℂ)) *
          hbXiPeierlsUnitSourceFECocycle q * (starRingEnd ℂ) c) := by
  rw [hbXiPeierlsSourceFECenteredQNMClockDefect,
    hbXiPeierlsCenteredQNMTimeGenerator_single,
    hbXiPeierlsUnitSourceFEPacketTransport_single,
    hbXiPeierlsUnitSourceFEPacketTransport_single,
    hbXiPeierlsCenteredQNMTimeGenerator_single]
  rw [map_mul]
  rw [← Finsupp.single_add]
  congr 1
  rw [← hbXiPeierlsCenteredQNMFrequency_conj_add_reflect n q]
  ring

/-- Exact arbitrary-packet formula: every output coefficient is the reflected input coefficient
times the centered Xi tilt and source cocycle. -/
theorem hbXiPeierlsSourceFECenteredQNMClockDefect_apply
    (n : ℕ) (x : HBXiPeierlsPacket) (r : XiZeroCopy) :
    hbXiPeierlsSourceFECenteredQNMClockDefect n x r =
      Complex.I *
          (((((xiZeroCopyReflectEquiv r).1 : ℂ).re - 1 / 2 : ℝ) : ℂ)) *
        hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv r) *
        (starRingEnd ℂ) (x (xiZeroCopyReflectEquiv r)) := by
  rw [hbXiPeierlsSourceFECenteredQNMClockDefect, Finsupp.add_apply,
    hbXiPeierlsUnitSourceFEPacketTransport_apply,
    hbXiPeierlsCenteredQNMTimeGenerator_apply,
    hbXiPeierlsCenteredQNMTimeGenerator_apply,
    hbXiPeierlsUnitSourceFEPacketTransport_apply, map_mul]
  have hclock := hbXiPeierlsCenteredQNMFrequency_conj_add_reflect n
    (xiZeroCopyReflectEquiv r)
  rw [xiZeroCopyReflectEquiv_apply_apply] at hclock
  rw [← hclock]
  ring

/-- The reflection-coupled clock defect vanishes on one unit basis packet exactly on the critical
line. -/
theorem hbXiPeierlsSourceFECenteredQNMClockDefect_single_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsSourceFECenteredQNMClockDefect n (Finsupp.single q 1) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsSourceFECenteredQNMClockDefect_single]
  simp only [map_one, mul_one, Finsupp.single_eq_zero]
  constructor
  · intro hzero
    have htiltC : (((q.1 : ℂ).re - 1 / 2 : ℝ) : ℂ) = 0 := by
      rcases mul_eq_zero.mp hzero with hleft | hcocycle
      · exact (mul_eq_zero.mp hleft).resolve_left Complex.I_ne_zero
      · exact False.elim (hbXiPeierlsUnitSourceFECocycle_ne_zero q hcocycle)
    have htilt := congrArg Complex.re htiltC
    norm_num at htilt
    linarith
  · intro hline
    rw [hline]
    norm_num

/-- Global vanishing of the exact source-FE/centered-QNM clock defect is equivalent to RH. -/
theorem forall_hbXiPeierlsSourceFECenteredQNMClockDefect_eq_zero_iff_rh
    (n : ℕ) :
    (∀ x : HBXiPeierlsPacket,
      hbXiPeierlsSourceFECenteredQNMClockDefect n x = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    exact (hbXiPeierlsSourceFECenteredQNMClockDefect_single_eq_zero_iff n q).mp
      (hzero (Finsupp.single q 1))
  · intro hRH x
    have hfixed :=
      (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr hRH
    apply Finsupp.ext
    intro r
    rw [hbXiPeierlsSourceFECenteredQNMClockDefect_apply]
    have hline : ((xiZeroCopyReflectEquiv r).1 : ℂ).re = 1 / 2 :=
      (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff
        (xiZeroCopyReflectEquiv r)).mp (hfixed (xiZeroCopyReflectEquiv r))
    rw [hline]
    norm_num

/-- Equivalently, literal source-FE transport anticommutes with the centered BM QNM generator on
all finite packets exactly under RH. -/
theorem forall_hbXiPeierlsUnitSourceFETransport_centeredQNMGenerator_anticommute_iff_rh
    (n : ℕ) :
    (∀ x : HBXiPeierlsPacket,
      hbXiPeierlsUnitSourceFEPacketTransport
          (hbXiPeierlsCenteredQNMTimeGenerator n x) =
        -hbXiPeierlsCenteredQNMTimeGenerator n
          (hbXiPeierlsUnitSourceFEPacketTransport x)) ↔
      RiemannHypothesis := by
  rw [← forall_hbXiPeierlsSourceFECenteredQNMClockDefect_eq_zero_iff_rh n]
  constructor
  · intro h x
    rw [hbXiPeierlsSourceFECenteredQNMClockDefect, h x, neg_add_cancel]
  · intro h x
    have hzero := h x
    rw [hbXiPeierlsSourceFECenteredQNMClockDefect] at hzero
    exact eq_neg_of_add_eq_zero_left hzero

end

end RHTower
