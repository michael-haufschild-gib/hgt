import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicComplexOrientationClassification

/-!
# Hermitian-source orientation no-go for reflected BM currents

The literal polarized second-harmonic source supplies the real weight
`normSq (angular mixing × nonlinear Einstein carrier)`.  The exact complex-orientation
classification forces a nonreal reflected cancellation ratio on every Xi fibre.  These two laws
are compatible only on the critical wall, where the angular mixing coefficient and hence both
Hermitian source weights vanish.

Thus the literal norm-square source cannot generate missing off-wall Peierls orientation.  The
strongest survivor is an exact RH receiver: its reflected current vanishes precisely on the wall.
Any producer-level source incidence must retain unsquared complex phase and transform covariantly
under functional-equation reflection.

`[NEW] [NO-GO] [EXACT RECEIVER] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Literal Hermitian weight transported by the angular--Einstein second-harmonic source. -/
def d4BMXiSecondHarmonicHermitianSourceWeight (q : XiZeroCopy) : ℝ :=
  Complex.normSq (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q)

/-- The literal reflected source weights obey the forced complex orientation law. -/
def d4BMXiSecondHarmonicHermitianSourceOrientationCompatible
    (n : ℕ) (q : XiZeroCopy) : Prop :=
  ((d4BMXiSecondHarmonicHermitianSourceWeight
      (xiZeroCopyReflectEquiv q) : ℝ) : ℂ) =
    ((d4BMXiSecondHarmonicHermitianSourceWeight q : ℝ) : ℂ) *
      d4BMXiReflectionComplexCancellationRatio n q

/-- Literal Hermitian source orientation matches complex cancellation only where source dies. -/
theorem d4BMXiSecondHarmonicHermitianSourceOrientationCompatible_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicHermitianSourceOrientationCompatible n q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hcompat
    by_contra hline
    have hmix : d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q ≠ 0 :=
      (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).not.mpr hline
    have hcarrier :
        d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1 (xiSpectralPoint q) ≠ 0 :=
      d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero one_ne_zero q
    have hamp : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q ≠ 0 := by
      exact mul_ne_zero hmix hcarrier
    have hweight : d4BMXiSecondHarmonicHermitianSourceWeight q ≠ 0 := by
      unfold d4BMXiSecondHarmonicHermitianSourceWeight
      exact (Complex.normSq_eq_zero.not).2 hamp
    have him := congrArg Complex.im hcompat
    simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      zero_mul, add_zero] at him
    have hratio := d4BMXiReflectionComplexCancellationRatio_im_ne_zero n q
    have hwzero := (mul_eq_zero.mp him.symm).resolve_right hratio
    exact hweight hwzero
  · intro hline
    have hmix : d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q = 0 :=
      (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).mpr hline
    have hmixr :
        d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient
          (xiZeroCopyReflectEquiv q) = 0 := by
      rw [d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_reflect]
      exact hmix
    simp [d4BMXiSecondHarmonicHermitianSourceOrientationCompatible,
      d4BMXiSecondHarmonicHermitianSourceWeight,
      d4BMXiSecondHarmonicPolarizedSourceAmplitude, hmix, hmixr]

/-- Reflection-paired canonical current with literal Hermitian source weights. -/
def d4BMXiSecondHarmonicHermitianSourceReflectionCurrent
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  d4BMXiReflectionComplexWeightedRegularComplementaryCurrent n q
    (d4BMXiSecondHarmonicHermitianSourceWeight q)
    (d4BMXiSecondHarmonicHermitianSourceWeight (xiZeroCopyReflectEquiv q))

/-- Literal Hermitian source pair cancels exactly where both angular source factors vanish. -/
theorem d4BMXiSecondHarmonicHermitianSourceReflectionCurrent_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicHermitianSourceReflectionCurrent n q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiSecondHarmonicHermitianSourceReflectionCurrent,
    d4BMXiReflectionComplexWeightedRegularComplementaryCurrent_eq_zero_iff]
  exact d4BMXiSecondHarmonicHermitianSourceOrientationCompatible_iff n q

/-- Universal Hermitian-source reflection cancellation is equivalent to RH. -/
theorem forall_d4BMXiSecondHarmonicHermitianSourceReflectionCurrent_eq_zero_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicHermitianSourceReflectionCurrent n q = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis n).mp
    intro q
    apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mpr
    exact (d4BMXiSecondHarmonicHermitianSourceReflectionCurrent_eq_zero_iff n q).mp (h q)
  · intro hRH q
    apply (d4BMXiSecondHarmonicHermitianSourceReflectionCurrent_eq_zero_iff n q).mpr
    have hsel :=
      (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis n).mpr
        hRH q
    exact (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mp hsel

end

end RHTower
