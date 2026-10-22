import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicOuterPolarizedReciprocity

/-!
# Canonical left connection covectors for the BM second harmonic

The exact horizon-to-AdS connection determinant is nonzero on every Xi fibre.  Its inverse rows
therefore define canonical left covectors on outer source/response data.  They extract the regular
and complementary horizon coordinates, give the unique horizon decomposition of every outer
coefficient vector, and transport the AdS boundary symplectic concomitant to the alternating
determinant of those coordinates with exact multiplier `-lambda`.

This closes the radial left-normalization ambiguity.  It does not construct the missing global
time-oriented augmented Einstein Peierls propagator.

`[NEW] [BRIDGE] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Canonical left covector extracting the regular horizon coordinate from AdS outer data. -/
def d4BMXiPlusPlusRegularLeftConnectionCovector
    (n : ℕ) (q : XiZeroCopy) (source response : ℂ) : ℂ :=
  let chi := d4BMXiMixedHorizonAngularMomentum q
  let aR := d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi
  let bR := d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi
  let aC := d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi
  let bC := d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi
  (source * bC - response * aC) / (aR * bC - bR * aC)

/-- Canonical left covector extracting the complementary horizon coordinate from AdS outer data. -/
def d4BMXiPlusPlusComplementaryLeftConnectionCovector
    (n : ℕ) (q : XiZeroCopy) (source response : ℂ) : ℂ :=
  let chi := d4BMXiMixedHorizonAngularMomentum q
  let aR := d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi
  let bR := d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi
  let aC := d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi
  let bC := d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi
  (aR * response - bR * source) / (aR * bC - bR * aC)

/-- Regular left covector has unit normalization on the regular connection column. -/
theorem d4BMXiPlusPlusRegularLeftConnectionCovector_regular_eq_one
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiPlusPlusRegularLeftConnectionCovector n q
      (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
        (d4BMXiMixedHorizonAngularMomentum q))
      (d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
        (d4BMXiMixedHorizonAngularMomentum q)) = 1 := by
  have hD := d4BMXiPlusPlusAdSConnectionDet_ne_zero n q
  unfold d4BMXiPlusPlusRegularLeftConnectionCovector
  dsimp only
  field_simp

/-- Regular left covector annihilates the complementary connection column. -/
theorem d4BMXiPlusPlusRegularLeftConnectionCovector_complementary_eq_zero
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiPlusPlusRegularLeftConnectionCovector n q
      (d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
        (d4BMXiMixedHorizonAngularMomentum q))
      (d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
        (d4BMXiMixedHorizonAngularMomentum q)) = 0 := by
  unfold d4BMXiPlusPlusRegularLeftConnectionCovector
  dsimp only
  ring

/-- Complementary left covector annihilates the regular connection column. -/
theorem d4BMXiPlusPlusComplementaryLeftConnectionCovector_regular_eq_zero
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiPlusPlusComplementaryLeftConnectionCovector n q
      (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
        (d4BMXiMixedHorizonAngularMomentum q))
      (d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
        (d4BMXiMixedHorizonAngularMomentum q)) = 0 := by
  unfold d4BMXiPlusPlusComplementaryLeftConnectionCovector
  dsimp only
  ring

/-- Complementary left covector has unit normalization on its connection column. -/
theorem d4BMXiPlusPlusComplementaryLeftConnectionCovector_complementary_eq_one
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiPlusPlusComplementaryLeftConnectionCovector n q
      (d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
        (d4BMXiMixedHorizonAngularMomentum q))
      (d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
        (d4BMXiMixedHorizonAngularMomentum q)) = 1 := by
  have hD := d4BMXiPlusPlusAdSConnectionDet_ne_zero n q
  unfold d4BMXiPlusPlusComplementaryLeftConnectionCovector
  dsimp only
  field_simp

/-- Canonical left coordinates reconstruct the outer forbidden/source coefficient. -/
theorem d4BMXiPlusPlusLeftConnectionCovectors_reconstruct_source
    (n : ℕ) (q : XiZeroCopy) (source response : ℂ) :
    d4BMXiPlusPlusRegularLeftConnectionCovector n q source response *
        d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q) +
      d4BMXiPlusPlusComplementaryLeftConnectionCovector n q source response *
        d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q) = source := by
  have hD := d4BMXiPlusPlusAdSConnectionDet_ne_zero n q
  have hD' :
      d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) *
          d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) -
        d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) *
          d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) ≠ 0 := by
    simpa [mul_comm] using hD
  unfold d4BMXiPlusPlusRegularLeftConnectionCovector
    d4BMXiPlusPlusComplementaryLeftConnectionCovector
  dsimp only
  field_simp [hD']
  ring

/-- Canonical left coordinates reconstruct the outer normalizable/response coefficient. -/
theorem d4BMXiPlusPlusLeftConnectionCovectors_reconstruct_response
    (n : ℕ) (q : XiZeroCopy) (source response : ℂ) :
    d4BMXiPlusPlusRegularLeftConnectionCovector n q source response *
        d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q) +
      d4BMXiPlusPlusComplementaryLeftConnectionCovector n q source response *
        d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q) = response := by
  have hD := d4BMXiPlusPlusAdSConnectionDet_ne_zero n q
  have hD' :
      d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) *
          d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) -
        d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) *
          d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) ≠ 0 := by
    simpa [mul_comm] using hD
  unfold d4BMXiPlusPlusRegularLeftConnectionCovector
    d4BMXiPlusPlusComplementaryLeftConnectionCovector
  dsimp only
  field_simp [hD']
  ring

/-- Exact Xi-fibre outer data have a unique horizon-basis coordinate pair. -/
theorem d4BMXi_existsUnique_plusPlusHorizonCoordinates
    (n : ℕ) (q : XiZeroCopy) (source response : ℂ) :
    ∃! c : ℂ × ℂ,
      c.1 * d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) +
          c.2 * d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) = source ∧
        c.1 * d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) +
          c.2 * d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) = response := by
  let r := d4BMXiPlusPlusRegularLeftConnectionCovector n q source response
  let c := d4BMXiPlusPlusComplementaryLeftConnectionCovector n q source response
  refine ⟨(r, c),
    ⟨d4BMXiPlusPlusLeftConnectionCovectors_reconstruct_source n q source response,
      d4BMXiPlusPlusLeftConnectionCovectors_reconstruct_response n q source response⟩, ?_⟩
  intro d hd
  have hD := d4BMXiPlusPlusAdSConnectionDet_ne_zero n q
  have hfirst :
      (d.1 - r) *
        (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) *
            d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) -
          d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) *
            d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q)) = 0 := by
    have hs := hd.1
    have hr := hd.2
    have hrs := d4BMXiPlusPlusLeftConnectionCovectors_reconstruct_source n q source response
    have hrr := d4BMXiPlusPlusLeftConnectionCovectors_reconstruct_response n q source response
    dsimp [r, c] at hrs hrr ⊢
    linear_combination
      d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q) * (hs - hrs) -
        d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q) * (hr - hrr)
  have hsecond :
      (d.2 - c) *
        (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) *
            d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) -
          d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) *
            d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q)) = 0 := by
    have hs := hd.1
    have hr := hd.2
    have hrs := d4BMXiPlusPlusLeftConnectionCovectors_reconstruct_source n q source response
    have hrr := d4BMXiPlusPlusLeftConnectionCovectors_reconstruct_response n q source response
    dsimp [r, c] at hrs hrr ⊢
    linear_combination
      d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q) * (hr - hrr) -
        d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q) * (hs - hrs)
  have hd1 : d.1 = r := sub_eq_zero.mp ((mul_eq_zero.mp hfirst).resolve_right hD)
  have hd2 : d.2 = c := sub_eq_zero.mp ((mul_eq_zero.mp hsecond).resolve_right hD)
  exact Prod.ext hd1 hd2

/-- Boundary symplectic concomitant is the horizon-coordinate determinant times `-lambda`. -/
theorem d4BMXiAdSBoundaryPolarizedConcomitant_eq_horizonCoordinates
    (n : ℕ) (q : XiZeroCopy)
    (sourcePP responsePP sourceMM responseMM : ℂ) :
    d4BMAdSBoundaryPolarizedConcomitant sourcePP responsePP sourceMM responseMM =
      -d4BMPlusPlusComplementaryFrobeniusExponent n
          (d4BMXiMixedHorizonAngularMomentum q) *
        (d4BMXiPlusPlusRegularLeftConnectionCovector n q sourcePP responsePP *
            d4BMXiPlusPlusComplementaryLeftConnectionCovector n q
              ((starRingEnd ℂ) sourceMM) ((starRingEnd ℂ) responseMM) -
          d4BMXiPlusPlusComplementaryLeftConnectionCovector n q sourcePP responsePP *
            d4BMXiPlusPlusRegularLeftConnectionCovector n q
              ((starRingEnd ℂ) sourceMM) ((starRingEnd ℂ) responseMM)) := by
  have hD := d4BMXiPlusPlusAdSConnectionDet_ne_zero n q
  have hD' :
      d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) *
          d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) -
        d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) *
          d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) ≠ 0 := by
    simpa [mul_comm] using hD
  have hDeq := d4BMPlusPlusAdSConnectionDet_eq n
    (d4BMXiMixedHorizonAngularMomentum q)
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)
  have hscale :
      -d4BMPlusPlusComplementaryFrobeniusExponent n
          (d4BMXiMixedHorizonAngularMomentum q) =
        (d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) *
            d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) -
          d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) *
            d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q)) / 2 := by
    rw [show
      d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) *
            d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) -
          d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) *
            d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) =
        d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) *
            d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) -
          d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) *
            d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
              (d4BMXiMixedHorizonAngularMomentum q) by ring,
      hDeq]
    ring
  unfold d4BMAdSBoundaryPolarizedConcomitant
    d4BMXiPlusPlusRegularLeftConnectionCovector
    d4BMXiPlusPlusComplementaryLeftConnectionCovector
  dsimp only
  rw [hscale]
  field_simp [hD']
  ring

end

end RHTower
