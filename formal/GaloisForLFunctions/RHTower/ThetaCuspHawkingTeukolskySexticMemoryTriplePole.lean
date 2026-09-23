import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyChargeDecayResonanceLadder

/-!
# Sextic Hawking--Teukolsky memory triple pole

The first charge-minus-two source frequency that can meet the quadratically dealiased
Birmingham--Mokhtari tower has radiative monomial `A^(2 : ℕ) * conj(A)^(4 : ℕ)`. It is the quadratic partner
carrier `conj(A)^(2 : ℕ)` dressed by two neutral horizon memories `(A * conj(A))^(2 : ℕ)`.

Two stationary mass insertions are governed by the second inverse-family identity

`G'' = 2 G L' G L' G - G L'' G`.

At a simple QNM, the repeated first insertion has three Green factors and therefore a triple pole.
The `L''` term has only two Green factors. The same is true of any direct or transient completion
whose two- and one-Green numerators are continuous at the QNM. Multiplication by the cube of the
local frequency coordinate kills all those lower pole grades and leaves

`2 * conj(A)^(2 : ℕ) * (|A|^(2 : ℕ) K)^(2 : ℕ) / J'(omega_0)^(3 : ℕ)`,

where `K=-12/(Q+2)` is the exact chiral Birmingham--Mokhtari first mass insertion evaluated in the
dealiased channel `Q=1/4+z^(2 : ℕ)`. This coefficient is nonzero at every Xi divisor for `A != 0`.

Thus a local second mass-potential term cannot cancel the sextic repeated-memory principal part.
Any cancellation must introduce another genuine three-Green stationary insertion. Combined with
the exact charge-decay frequency law, the protected sextic pole is hit exactly when the Xi tilt is
zero.

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`

This module proves pole protection after a nonzero charge-minus-two carrier is present. Deriving
that carrier from the full quadratic vacuum Teukolsky source remains separate; scalar optical
energy, KMS, CCR, and generic passivity do not provide it.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Normalized negative-branch Green function in the quadratically dealiased channel. -/
def d4ThetaHawkingDealiasedNormalizedMinusGreen (z omega : ℂ) : ℂ :=
  (thetaCuspHawkingHypergeometricJostMinus omega
    (d4ThetaCuspHawkingQuadraticDealiasedLift z))⁻¹

/-- Exact normalized Green residue at every negative-branch overtone. -/
theorem d4ThetaHawkingDealiasedNormalizedMinusGreen_tendsto_residue
    (n : ℕ) (z : ℂ) :
    Tendsto
      (fun omega =>
        (omega - thetaCuspHawkingTopologicalBlackHoleQNMMinus n
          (d4ThetaCuspHawkingQuadraticDealiasedLift z)) *
            d4ThetaHawkingDealiasedNormalizedMinusGreen z omega)
      (𝓝[≠] (thetaCuspHawkingTopologicalBlackHoleQNMMinus n
        (d4ThetaCuspHawkingQuadraticDealiasedLift z)))
      (𝓝 (teukolskyNormalizedJostOmegaDerivative n)⁻¹) := by
  let zl := d4ThetaCuspHawkingQuadraticDealiasedLift z
  let sigma := thetaCuspHawkingTopologicalBlackHoleQNMMinus n zl
  let D : ℂ → ℂ := fun omega => thetaCuspHawkingHypergeometricJostMinus omega zl
  let N : ℂ → ℂ := fun _ => 1
  have hD : HasDerivAt D (teukolskyNormalizedJostOmegaDerivative n) sigma := by
    simpa [D, sigma, zl, teukolskyNormalizedJostOmegaDerivative] using
      thetaCuspHawkingHypergeometricHasDerivAt_jostMinus_qnm n zl
  have hD0 : D sigma = 0 := by
    simp [D, sigma, thetaCuspHawkingHypergeometricJostMinus_qnm_zero]
  have hlim := tendsto_residue_of_simple_zero hD hD0
    (teukolskyNormalizedJostOmegaDerivative_ne_zero n)
    (continuousAt_const : ContinuousAt N sigma)
  simpa [sigma, zl, D, N, d4ThetaHawkingDealiasedNormalizedMinusGreen,
    div_eq_mul_inv] using hlim

/-- The dealiased chiral first mass insertion has no `Q+2` pole at an Xi divisor. -/
lemma d4ThetaHawkingDealiasedAngularQ_xi_add_two_ne_zero (q : XiZeroCopy) :
    d4ThetaTeukolskyAngularQ
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)) + 2 ≠ 0 := by
  rw [d4ThetaCuspHawkingQuadraticDealiased_q]
  intro h
  have hQ : (1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ) = -2 := by
    linear_combination h
  have him0 :
      (d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue
        (xiSpectralPoint q)).im = 0 := by
    rw [d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_eq, hQ]
    norm_num
  have hz :=
    (d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_xi_im_eq_zero_iff q).1 him0
  have hgt :=
    d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_xi_re_gt_quarter q hz
  rw [d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_eq, hQ] at hgt
  norm_num at hgt

/-- One neutral horizon-memory mass insertion in the dealiased chiral channel. -/
def d4ThetaHawkingSexticFirstMemoryInsertion (amplitude z : ℂ) : ℂ :=
  (Complex.normSq amplitude : ℂ) *
    d4FundamentalQNMCrossBranchChiralMassJetNumerator
      (d4ThetaCuspHawkingQuadraticDealiasedLift z)

theorem d4ThetaHawkingSexticFirstMemoryInsertion_xi_ne_zero
    (amplitude : ℂ) (q : XiZeroCopy) (ha : amplitude ≠ 0) :
    d4ThetaHawkingSexticFirstMemoryInsertion amplitude (xiSpectralPoint q) ≠ 0 := by
  unfold d4ThetaHawkingSexticFirstMemoryInsertion
  apply mul_ne_zero
  · exact_mod_cast (show Complex.normSq amplitude ≠ 0 by
      intro h
      exact ha (Complex.normSq_eq_zero.mp h))
  · rw [d4FundamentalQNMCrossBranchChiralMassJetNumerator_eq]
    exact div_ne_zero (by norm_num)
      (d4ThetaHawkingDealiasedAngularQ_xi_add_two_ne_zero q)

/-- Triple-pole coefficient of the first sextic charge-decay rung. -/
def d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient
    (amplitude z : ℂ) : ℂ :=
  2 * star amplitude ^ (2 : ℕ) *
    d4ThetaHawkingSexticFirstMemoryInsertion amplitude z ^ (2 : ℕ) *
      (teukolskyNormalizedJostOmegaDerivative 3)⁻¹ ^ (3 : ℕ)

/-- The protected coefficient is nonzero at every Xi divisor exactly for nonzero radiative
amplitude. -/
theorem d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient_xi_ne_zero_iff
    (amplitude : ℂ) (q : XiZeroCopy) :
    d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient amplitude
        (xiSpectralPoint q) ≠ 0 ↔
      amplitude ≠ 0 := by
  constructor
  · intro h ha
    rw [ha] at h
    simp [d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient] at h
  · intro ha
    unfold d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 (by simpa using ha)))
        (pow_ne_zero 2
          (d4ThetaHawkingSexticFirstMemoryInsertion_xi_ne_zero amplitude q ha)))
      (pow_ne_zero 3
        (inv_ne_zero (teukolskyNormalizedJostOmegaDerivative_ne_zero 3)))

/-- Repeated-memory term together with arbitrary two- and one-Green lower-grade completions. -/
def d4ThetaHawkingSexticRepeatedMemoryCompletion
    (amplitude z : ℂ) (twoGreenNumerator oneGreenNumerator : ℂ → ℂ)
    (omega : ℂ) : ℂ :=
  2 * star amplitude ^ (2 : ℕ) *
      d4ThetaHawkingSexticFirstMemoryInsertion amplitude z ^ (2 : ℕ) *
      d4ThetaHawkingDealiasedNormalizedMinusGreen z omega ^ (3 : ℕ) +
    twoGreenNumerator omega *
      d4ThetaHawkingDealiasedNormalizedMinusGreen z omega ^ (2 : ℕ) +
    oneGreenNumerator omega *
      d4ThetaHawkingDealiasedNormalizedMinusGreen z omega

/-- Triple-pole grade forgets every continuous `L''`, direct, transient, or continuum numerator
with fewer than three copies of the resonant Green function. -/
theorem d4ThetaHawkingSexticRepeatedMemoryCompletion_tendsto_triplePoleCoefficient
    (amplitude : ℂ) (q : XiZeroCopy)
    (twoGreenNumerator oneGreenNumerator : ℂ → ℂ)
    (hN2 : ContinuousAt twoGreenNumerator
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))))
    (hN1 : ContinuousAt oneGreenNumerator
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)))) :
    Tendsto
      (fun omega =>
        (omega - thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) ^ (3 : ℕ) *
          d4ThetaHawkingSexticRepeatedMemoryCompletion amplitude
            (xiSpectralPoint q) twoGreenNumerator oneGreenNumerator omega)
      (𝓝[≠] (thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))))
      (𝓝 (d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient amplitude
        (xiSpectralPoint q))) := by
  let sigma := thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
    (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))
  let x : ℂ → ℂ := fun omega => omega - sigma
  let G : ℂ → ℂ := fun omega =>
    d4ThetaHawkingDealiasedNormalizedMinusGreen (xiSpectralPoint q) omega
  have hx : Tendsto x (𝓝[≠] sigma) (𝓝 0) := by
    have hid : Tendsto (fun omega : ℂ => omega) (𝓝[≠] sigma) (𝓝 sigma) :=
      continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    have hc : Tendsto (fun _ : ℂ => sigma) (𝓝[≠] sigma) (𝓝 sigma) :=
      tendsto_const_nhds
    simpa only [x, sub_self] using hid.sub hc
  have hG : Tendsto (fun omega => x omega * G omega) (𝓝[≠] sigma)
      (𝓝 (teukolskyNormalizedJostOmegaDerivative 3)⁻¹) := by
    simpa [x, G, sigma] using
      d4ThetaHawkingDealiasedNormalizedMinusGreen_tendsto_residue 3
        (xiSpectralPoint q)
  have h2 := hN2.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] sigma ≤ 𝓝 sigma)
  have h1 := hN1.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] sigma ≤ 𝓝 sigma)
  have htop : Tendsto
      (fun omega => x omega ^ (3 : ℕ) *
        (2 * star amplitude ^ (2 : ℕ) *
          d4ThetaHawkingSexticFirstMemoryInsertion amplitude
              (xiSpectralPoint q) ^ (2 : ℕ) * G omega ^ (3 : ℕ)))
      (𝓝[≠] sigma)
      (𝓝 (d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient amplitude
        (xiSpectralPoint q))) := by
    have h := (hG.pow 3).const_mul
      (2 * star amplitude ^ (2 : ℕ) *
        d4ThetaHawkingSexticFirstMemoryInsertion amplitude (xiSpectralPoint q) ^ (2 : ℕ))
    convert h using 1
    · funext omega
      ring
    · simp [d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient]
  have hlower2 : Tendsto
      (fun omega => x omega ^ (3 : ℕ) * (twoGreenNumerator omega * G omega ^ (2 : ℕ)))
      (𝓝[≠] sigma) (𝓝 0) := by
    have h := hx.mul ((hG.pow 2).mul h2)
    convert h using 1
    · funext omega
      ring
    · ring
  have hlower1 : Tendsto
      (fun omega => x omega ^ (3 : ℕ) * (oneGreenNumerator omega * G omega))
      (𝓝[≠] sigma) (𝓝 0) := by
    have h := (hx.pow 2).mul (hG.mul h1)
    convert h using 1
    · funext omega
      ring
    · ring
  have hsum := (htop.add hlower2).add hlower1
  convert hsum using 1
  · funext omega
    simp only [d4ThetaHawkingSexticRepeatedMemoryCompletion, x, G, sigma]
    ring
  · simp

/-- No lower-grade completion can cancel the sextic triple pole for a nonzero seed. -/
theorem d4ThetaHawkingSexticRepeatedMemoryCompletion_cannot_cancel
    (amplitude : ℂ) (q : XiZeroCopy)
    (twoGreenNumerator oneGreenNumerator : ℂ → ℂ)
    (ha : amplitude ≠ 0)
    (hN2 : ContinuousAt twoGreenNumerator
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))))
    (hN1 : ContinuousAt oneGreenNumerator
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)))) :
    ¬ Tendsto
      (fun omega =>
        (omega - thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) ^ (3 : ℕ) *
          d4ThetaHawkingSexticRepeatedMemoryCompletion amplitude
            (xiSpectralPoint q) twoGreenNumerator oneGreenNumerator omega)
      (𝓝[≠] (thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))))
      (𝓝 0) := by
  intro hzero
  have hcoefficient :=
    d4ThetaHawkingSexticRepeatedMemoryCompletion_tendsto_triplePoleCoefficient
      amplitude q twoGreenNumerator oneGreenNumerator hN2 hN1
  have heq :
      d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient amplitude
        (xiSpectralPoint q) = 0 :=
    tendsto_nhds_unique hcoefficient hzero
  exact
    (d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient_xi_ne_zero_iff
      amplitude q).mpr ha heq

/-- With nonzero carrier amplitude, protected sextic pole incidence is exactly zero Xi tilt. -/
theorem d4ThetaHawkingSexticProtectedMemoryPoleIncidence_iff
    (amplitude : ℂ) (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    (d4ThetaHawkingChargeDecayInputFrequency 0 (xiSpectralPoint q) =
        thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)) ∧
      d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient amplitude
        (xiSpectralPoint q) ≠ 0) ↔
      (xiSpectralPoint q).im = 0 := by
  rw [and_iff_left
    ((d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient_xi_ne_zero_iff
      amplitude q).mpr ha)]
  exact d4ThetaHawkingSexticInputFrequency_eq_thirdQNMMinus_iff
    (xiSpectralPoint q)

end

end RHTower
