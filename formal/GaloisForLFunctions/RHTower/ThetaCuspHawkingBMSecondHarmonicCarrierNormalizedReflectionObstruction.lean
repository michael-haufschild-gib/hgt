import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicPeierlsPolarizedLanding

/-!
# Carrier-normalized reflected BM Peierls obstruction

The nonzero self-dual Einstein carrier can be normalized exactly to one.  At that normalization,
functional-equation reflection preserves the angular mixing coefficient but the canonical BM
regular/Schwarz-complementary currents add to `-(8*n+5)`.  The reflected Peierls candidates thus
add to one explicit nonzero multiple of the angular mixing norm, whose universal zero locus is RH.

This is a receiver and a source-global normalization law, not the missing physical Peierls
source-incidence theorem.
-/

open Complex Real Set

namespace RHTower

noncomputable section

private theorem complex_sqrt_sq_local (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  by_cases hz : z = 0
  · simp [hz]
  · calc
      Complex.sqrt z ^ 2 = Complex.exp (Complex.log z / 2) ^ 2 := by
        rw [sqrt_eq_exp hz]
      _ = Complex.exp (Complex.log z) := by
        rw [pow_two, ← Complex.exp_add]
        congr 1
        ring
      _ = z := Complex.exp_log hz

/-- Seed amplitude making the nonzero self-dual Einstein carrier exactly one. -/
def d4BMXiSecondHarmonicUnitCarrierAmplitude (q : XiZeroCopy) : ℂ :=
  Complex.sqrt
    ((d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1 (xiSpectralPoint q))⁻¹)

theorem d4BMXiSecondHarmonicUnitCarrierAmplitude_carrier_eq_one
    (q : XiZeroCopy) :
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient
        (d4BMXiSecondHarmonicUnitCarrierAmplitude q) (xiSpectralPoint q) = 1 := by
  let c := d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1 (xiSpectralPoint q)
  have hc : c ≠ 0 :=
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero one_ne_zero q
  change Complex.sqrt (c⁻¹) ^ 2 *
      ads4SelfDualNormalizedMellinSourceCoefficient
        (d4ThetaHawkingSelfDualDilationExponent (xiSpectralPoint q))
        (d4ThetaTeukolskyLinearCuspWeight (xiSpectralPoint q)) = 1
  rw [complex_sqrt_sq_local]
  have hbase :
      ads4SelfDualNormalizedMellinSourceCoefficient
          (d4ThetaHawkingSelfDualDilationExponent (xiSpectralPoint q))
          (d4ThetaTeukolskyLinearCuspWeight (xiSpectralPoint q)) = c := by
    simp [c, d4ThetaHawkingSelfDualQuadraticCarrierCoefficient]
  rw [hbase, inv_mul_cancel₀ hc]

theorem d4BMXiSecondHarmonicUnitCarrierAmplitude_ne_zero (q : XiZeroCopy) :
    d4BMXiSecondHarmonicUnitCarrierAmplitude q ≠ 0 := by
  intro hzero
  have h := d4BMXiSecondHarmonicUnitCarrierAmplitude_carrier_eq_one q
  rw [hzero] at h
  simp [d4ThetaHawkingSelfDualQuadraticCarrierCoefficient] at h

/-- Functional-equation reflection preserves the exact orthogonal-helicity mixing coefficient. -/
theorem d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_reflect
    (q : XiZeroCopy) :
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient
        (xiZeroCopyReflectEquiv q) =
      d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q := by
  rw [d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq,
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq,
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_eq,
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_eq,
    xiSpectralPoint_reflect]
  ring_nf

/-- Peierls candidate with self-dual Einstein carrier normalized to unit amplitude. -/
def d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut
    (n : ℕ) (q : XiZeroCopy) (z : ℝ) : ℂ :=
  2 * (Complex.normSq
      (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) : ℂ) *
    d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue n
      (d4BMXiMixedHorizonAngularMomentum q) z

theorem d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate_unitCarrierAmplitude
    (n : ℕ) (q : XiZeroCopy) (z : ℝ) :
    d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate n
        (d4BMXiSecondHarmonicUnitCarrierAmplitude q) q z =
      d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n q z := by
  rw [d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate,
    d4BMXiSecondHarmonicUnitCarrierAmplitude_carrier_eq_one]
  simp [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut]

/-- Reflected unit-carrier candidates add to one explicit critical-line obstruction. -/
theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add
    (n : ℕ) (q : XiZeroCopy) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n q z +
        d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n
          (xiZeroCopyReflectEquiv q) z =
      -2 * (Complex.normSq
        (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) : ℂ) *
          (8 * (n : ℂ) + 5) := by
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut,
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut,
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_reflect]
  have hcurrent := d4BMXi_reflectionPair_regularComplementaryPolarizedCurrent_add
    n q hz0 hz1
  linear_combination
    2 * (Complex.normSq
      (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) : ℂ) * hcurrent

/-- Reflected unit-carrier Peierls sum vanishes exactly on the critical line. -/
theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n q z +
        d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n
          (xiZeroCopyReflectEquiv q) z = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add
    n q hz0 hz1]
  have hconst : (8 * (n : ℂ) + 5) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hn : 0 ≤ (n : ℝ) := by positivity
    norm_num at hre
    nlinarith
  constructor
  · intro hsum
    have hleft := (mul_eq_zero.mp hsum).resolve_right hconst
    have hnormC :
        (Complex.normSq
          (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) : ℂ) = 0 :=
      (mul_eq_zero.mp hleft).resolve_left (by norm_num)
    have hnormR :
        Complex.normSq (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) = 0 :=
      Complex.ofReal_eq_zero.mp hnormC
    exact (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).mp
      (Complex.normSq_eq_zero.mp hnormR)
  · intro hline
    have hmix :=
      (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).mpr hline
    simp [hmix]

/-- Universal vanishing of reflected unit-carrier Peierls sums is exactly RH. -/
theorem forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add_eq_zero_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n q (1 / 2) +
        d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n
          (xiZeroCopyReflectEquiv q) (1 / 2) = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis n).mp
    intro q
    apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mpr
    exact (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add_eq_zero_iff
      n q (by norm_num) (by norm_num)).mp (h q)
  · intro hRH q
    apply (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add_eq_zero_iff
      n q (by norm_num) (by norm_num)).mpr
    have hsel :=
      (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis n).mpr
        hRH q
    exact (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mp hsel

end

end RHTower
