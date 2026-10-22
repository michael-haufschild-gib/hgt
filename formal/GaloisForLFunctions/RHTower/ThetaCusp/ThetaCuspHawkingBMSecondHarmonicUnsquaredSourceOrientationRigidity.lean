import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicHermitianSourceOrientationNoGo

/-!
# Unsquared-source orientation rigidity for reflected BM currents

Retaining literal complex phase does not repair reflected source incidence.  On an Xi fibre, the
normalized Mellin carrier is the polynomial `s²(s+2)/8`, functional-equation reflection sends
`s` to `1-s`, and the complementary BM exponent is `4n+2+s`.  Away from the critical wall,
compatibility with the unique current-cancellation ratio reduces exactly to a quartic in
`u=(2s-1)²`:

`u² + (56n+46)u + (40n+25) = 0`.

Every Xi zero satisfying this quartic lies on the critical wall.  The proof uses nonzero Xi height:
an off-wall root would give a nonzero imaginary part of `u`; imaginary and real parts of the
quadratic then contradict the strict coefficient gap.  Hence the literal unsquared source law is
compatible exactly on the wall, where its angular factor already vanishes.

The remaining augmented Peierls producer must therefore include an additional response/left-QNM
functional phase beyond both literal source amplitude and its Hermitian square.

`[NEW] [RIGIDITY] [NO-GO] [EXACT RECEIVER] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Exact Xi-coordinate form of the BM complementary exponent. -/
theorem d4BMXiPlusPlusComplementaryExponent_eq_xi
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiPlusPlusComplementaryExponent n q =
      4 * (n : ℂ) + 2 + (q.1 : ℂ) := by
  rw [d4BMXiPlusPlusComplementaryExponent,
    d4BMPlusPlusComplementaryFrobeniusExponent_eq]
  simp only [d4BMXiMixedHorizonAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum, xiSpectralPoint]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Quartic obstruction left after cancelling the nonzero unsquared angular source phase. -/
def d4BMXiSecondHarmonicUnsquaredSourceOrientationPolynomial
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  let u := (2 * (q.1 : ℂ) - 1) ^ (2 : ℕ)
  u ^ (2 : ℕ) + (56 * (n : ℂ) + 46) * u + (40 * (n : ℂ) + 25)

/-- Every Xi zero of the unsquared source-orientation polynomial lies on the critical wall. -/
theorem d4BMXiSecondHarmonicUnsquaredSourceOrientationPolynomial_eq_zero_implies
    (n : ℕ) (q : XiZeroCopy)
    (hpoly : d4BMXiSecondHarmonicUnsquaredSourceOrientationPolynomial n q = 0) :
    (q.1 : ℂ).re = 1 / 2 := by
  let t : ℂ := 2 * (q.1 : ℂ) - 1
  let u : ℂ := t ^ (2 : ℕ)
  change u ^ (2 : ℕ) + (56 * (n : ℂ) + 46) * u + (40 * (n : ℂ) + 25) = 0 at hpoly
  have hre := congrArg Complex.re hpoly
  have him := congrArg Complex.im hpoly
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have htimi : t.im = 2 * (q.1 : ℂ).im := by
    dsimp [t]
    norm_num
  have htim : t.im ≠ 0 := by
    rw [htimi]
    exact mul_ne_zero (by norm_num) (xi_divisor_support_im_ne_zero q.1)
  have huim : u.im = 2 * t.re * t.im := by
    dsimp [u]
    norm_num [pow_two, Complex.mul_im]
    ring
  by_contra hline
  have htre : t.re ≠ 0 := by
    intro htre0
    apply hline
    have htrere : t.re = 2 * (q.1 : ℂ).re - 1 := by
      dsimp [t]
      norm_num
    rw [htre0] at htrere
    linarith
  have huimne : u.im ≠ 0 := by
    rw [huim]
    exact mul_ne_zero (mul_ne_zero (by norm_num) htre) htim
  have hlinear : 2 * u.re + (56 * (n : ℝ) + 46) = 0 := by
    apply (mul_right_cancel₀ huimne)
    nlinarith
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [sq_nonneg (n : ℝ), sq_nonneg u.im]

/-- Literal unsquared source amplitude obeys the forced reflected complex orientation. -/
def d4BMXiSecondHarmonicUnsquaredSourceOrientationCompatible
    (n : ℕ) (q : XiZeroCopy) : Prop :=
  d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 (xiZeroCopyReflectEquiv q) =
    d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q *
      d4BMXiReflectionComplexCancellationRatio n q

/-- Literal unsquared angular--Einstein source phase matches BM cancellation only on the wall. -/
theorem d4BMXiSecondHarmonicUnsquaredSourceOrientationCompatible_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicUnsquaredSourceOrientationCompatible n q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hcompat
    by_contra hline
    have hmix : d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q ≠ 0 :=
      (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).not.mpr hline
    rw [d4BMXiSecondHarmonicUnsquaredSourceOrientationCompatible,
      d4BMXiSecondHarmonicPolarizedSourceAmplitude,
      d4BMXiSecondHarmonicPolarizedSourceAmplitude,
      d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_reflect] at hcompat
    have hcarrier :
        d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1
            (xiSpectralPoint (xiZeroCopyReflectEquiv q)) =
          d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1 (xiSpectralPoint q) *
            d4BMXiReflectionComplexCancellationRatio n q := by
      apply (mul_left_cancel₀ hmix)
      simpa only [mul_assoc] using hcompat
    rw [d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq,
      d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq,
      d4BMXiReflectionComplexCancellationRatio,
      d4BMXiPlusPlusComplementaryExponent_eq_xi,
      d4BMXiPlusPlusComplementaryExponent_eq_xi] at hcarrier
    have href : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := by
      exact xiZeroReflectEquiv_apply q.1
    rw [href] at hcarrier
    have hden : 4 * (n : ℂ) + 2 + (1 - (q.1 : ℂ)) ≠ 0 := by
      have hne := d4BMXiPlusPlusComplementaryExponent_ne_zero n
        (xiZeroCopyReflectEquiv q)
      rw [d4BMXiPlusPlusComplementaryExponent_eq_xi, href] at hne
      exact hne
    have hpoly :
        d4BMXiSecondHarmonicUnsquaredSourceOrientationPolynomial n q = 0 := by
      unfold d4BMXiSecondHarmonicUnsquaredSourceOrientationPolynomial
      field_simp [hden] at hcarrier
      ring_nf at hcarrier ⊢
      linear_combination 8 * hcarrier
    exact hline
      (d4BMXiSecondHarmonicUnsquaredSourceOrientationPolynomial_eq_zero_implies n q hpoly)
  · intro hline
    have hmix : d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q = 0 :=
      (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).mpr hline
    have hmixr :
        d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient
          (xiZeroCopyReflectEquiv q) = 0 := by
      rw [d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_reflect]
      exact hmix
    simp [d4BMXiSecondHarmonicUnsquaredSourceOrientationCompatible,
      d4BMXiSecondHarmonicPolarizedSourceAmplitude, hmix, hmixr]

/-- Reflection-paired BM current weighted by literal unsquared source amplitudes. -/
def d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  d4BMXiReflectionComplexWeightedRegularComplementaryCurrent n q
    (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q)
    (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 (xiZeroCopyReflectEquiv q))

/-- Literal unsquared source-weighted reflection current vanishes exactly on critical wall. -/
theorem d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent n q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent,
    d4BMXiReflectionComplexWeightedRegularComplementaryCurrent_eq_zero_iff]
  exact d4BMXiSecondHarmonicUnsquaredSourceOrientationCompatible_iff n q

/-- Universal unsquared-source reflection cancellation is equivalent to RH. -/
theorem forall_d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent n q = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis n).mp
    intro q
    apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mpr
    exact (d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff n q).mp (h q)
  · intro hRH q
    apply (d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff n q).mpr
    have hsel :=
      (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis n).mpr
        hRH q
    exact (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mp hsel

end

end RHTower
