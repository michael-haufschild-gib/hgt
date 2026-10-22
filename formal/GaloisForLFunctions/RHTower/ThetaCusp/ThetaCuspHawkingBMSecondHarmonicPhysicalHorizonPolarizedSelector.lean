import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicPhysicalHorizonGreenNoncollapseNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingSelfDualTeukolskyOpticalTransgression
import GaloisForLFunctions.RHTower.XiReciprocalTranslationSeamNormLaw

/-!
# Factorized BM physical horizon selector

The exact orthogonal-helicity mixing coefficient carries the critical-line zero locus.  The
physical ingoing-minus-outgoing point-source Green response is nonzero at a selectable interior
point on every Xi fibre.  Their product therefore vanishes exactly on the critical line, with no
radial denominator or source-support premise.

Choosing one certified noncollapse point on each fibre gives a global factorized observable whose
universal vanishing is equivalent to RH.  This is a receiver, not an unconditional RH proof: a
separate source-side Einstein/Peierls/Ward law must force the observable to vanish.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- The orthogonal-helicity mixing coefficient vanishes exactly on the critical line. -/
theorem d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff
    (q : XiZeroCopy) :
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [← Complex.normSq_eq_zero,
    normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient]
  have h := d4ThetaTeukolskyOrthogonalHelicityMixingEnergy_eq_zero_iff
    (H := ℂ) (1 : ℂ) one_ne_zero q
  simpa [d4ThetaTeukolskyOrthogonalHelicityMixingEnergy] using h

/-- Angular mixing times physical one-point radial causal response. -/
def d4BMXiPlusPlusFactorizedPhysicalHorizonObservable
    (n : ℕ) (q : XiZeroCopy) (t z : ℝ) : ℂ :=
  d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q *
    (d4BMPlusPlusPointIngoingAdSNormalizableGreenResponse n
        (d4BMXiMixedHorizonAngularMomentum q) t z -
      d4BMPlusPlusPointOutgoingAdSNormalizableGreenResponse n
        (d4BMXiMixedHorizonAngularMomentum q) t z)

/-- At any certified noncollapse point, the factorized observable vanishes exactly on the critical
line. -/
theorem d4BMXiPlusPlusFactorizedPhysicalHorizonObservable_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) {t : ℝ}
    (hdelta :
      d4BMPlusPlusPointIngoingAdSNormalizableGreenResponse n
          (d4BMXiMixedHorizonAngularMomentum q) t t -
        d4BMPlusPlusPointOutgoingAdSNormalizableGreenResponse n
          (d4BMXiMixedHorizonAngularMomentum q) t t ≠ 0) :
    d4BMXiPlusPlusFactorizedPhysicalHorizonObservable n q t t = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiPlusPlusFactorizedPhysicalHorizonObservable, mul_eq_zero]
  simp only [hdelta, or_false]
  exact d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q

/-- Every Xi fibre has an interior point at which the factorized physical observable has exactly
the critical-line zero locus. -/
theorem exists_d4BMXiPlusPlusFactorizedPhysicalHorizonObservable_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      (d4BMXiPlusPlusFactorizedPhysicalHorizonObservable n q t t = 0 ↔
        (q.1 : ℂ).re = 1 / 2) := by
  obtain ⟨t, ht0, ht1, hdelta⟩ :=
    exists_d4BMXiPlusPlusPointIngoing_sub_outgoingGreenResponse_ne_zero n q
  exact ⟨t, ht0, ht1,
    d4BMXiPlusPlusFactorizedPhysicalHorizonObservable_eq_zero_iff n q hdelta⟩

/-- Canonically selected interior point witnessing physical radial Green noncollapse. -/
def d4BMXiPlusPlusPhysicalHorizonNoncollapsePoint
    (n : ℕ) (q : XiZeroCopy) : ℝ :=
  Classical.choose
    (exists_d4BMXiPlusPlusPointIngoing_sub_outgoingGreenResponse_ne_zero n q)

/-- Selected point is interior and has nonzero ingoing-minus-outgoing point-source response. -/
theorem d4BMXiPlusPlusPhysicalHorizonNoncollapsePoint_spec
    (n : ℕ) (q : XiZeroCopy) :
    0 < d4BMXiPlusPlusPhysicalHorizonNoncollapsePoint n q ∧
      d4BMXiPlusPlusPhysicalHorizonNoncollapsePoint n q < 1 ∧
      d4BMPlusPlusPointIngoingAdSNormalizableGreenResponse n
          (d4BMXiMixedHorizonAngularMomentum q)
          (d4BMXiPlusPlusPhysicalHorizonNoncollapsePoint n q)
          (d4BMXiPlusPlusPhysicalHorizonNoncollapsePoint n q) -
        d4BMPlusPlusPointOutgoingAdSNormalizableGreenResponse n
          (d4BMXiMixedHorizonAngularMomentum q)
          (d4BMXiPlusPlusPhysicalHorizonNoncollapsePoint n q)
          (d4BMXiPlusPlusPhysicalHorizonNoncollapsePoint n q) ≠ 0 :=
  Classical.choose_spec
    (exists_d4BMXiPlusPlusPointIngoing_sub_outgoingGreenResponse_ne_zero n q)

/-- Canonical fibrewise angular-radial physical selector. -/
def d4BMXiPlusPlusCanonicalPhysicalHorizonSelector
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  d4BMXiPlusPlusFactorizedPhysicalHorizonObservable n q
    (d4BMXiPlusPlusPhysicalHorizonNoncollapsePoint n q)
    (d4BMXiPlusPlusPhysicalHorizonNoncollapsePoint n q)

/-- Canonical factorized selector vanishes exactly on the critical line. -/
theorem d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiPlusPlusCanonicalPhysicalHorizonSelector n q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  exact d4BMXiPlusPlusFactorizedPhysicalHorizonObservable_eq_zero_iff n q
    (d4BMXiPlusPlusPhysicalHorizonNoncollapsePoint_spec n q).2.2

/-- Global vanishing of the canonical factorized physical horizon selector is exactly RH. -/
theorem forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis
    (n : ℕ) :
    (∀ q : XiZeroCopy, d4BMXiPlusPlusCanonicalPhysicalHorizonSelector n q = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply xiSpectralPoint_im_eq_zero_iff_rh.mpr
    intro q
    have hline :=
      (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mp (h q)
    rw [xiSpectralPoint]
    simp [Complex.mul_im]
    linarith
  · intro hRH q
    apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mpr
    have him := xiSpectralPoint_im_eq_zero_iff_rh.mp hRH q
    rw [xiSpectralPoint] at him
    simp [Complex.mul_im] at him
    linarith

end

end RHTower
