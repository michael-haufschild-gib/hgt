import GaloisForLFunctions.RHTower.XiGaussianExactOrbitRemainder
import GaloisForLFunctions.RHTower.XiGaussianAnnihilatorPhaseControl
import GaloisForLFunctions.RHTower.XiGaussianAnnihilatorPrimeCancellation
import GaloisForLFunctions.RHTower.XiGaussianRealChannelEnergy

/-!
# Quantitative fixed-time localization of the full signed Xi form

For each nonreal squared divisor node and each prescribed positive heat
time, one constant bounds the entire remaining tail exponentially in the
spectral cutoff. Polynomial degree grows without changing time or constant.
The result includes native energy, both phase channels, and the complete
prime--Gamma residual. It does not assert an off-critical node exists.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators Real
noncomputable section
namespace RHTower

/-- Exact head normalization gives a quantitative remainder on the entire
actual divisor, with one constant independent of cutoff and polynomial degree. -/
theorem exists_xiGaussian_fixedTime_exponential_orbit_localization
    (t : {t : ℝ // 0 < t})
    (q₀ : {q : XiZeroCopy // (xiSpectralPoint q ^ 2).im ≠ 0}) :
    ∃ C : ℝ, 0 < C ∧
      ∀ R : {R : ℝ // (xiSpectralPoint q₀.1 ^ 2).re ≤ R},
        ∃ P : Polynomial ℝ,
          ((xiGaussianConjugateOrbit q₀.1).card : ℝ) ≤ xiGaussianNativeEnergy P t ∧
          xiGaussianNativeEnergy P t ≤ ((xiGaussianConjugateOrbit q₀.1).card : ℝ) +
            C * Real.exp (-((t : ℝ) / 2 * (R : ℝ))) ∧
          ‖xiPolynomialGaussianHeatTrace P t +
            ((xiGaussianConjugateOrbit q₀.1).card : ℂ)‖ ≤
              C * Real.exp (-((t : ℝ) / 2 * (R : ℝ))) ∧
          xiGaussianRealChannelEnergy P t ≤ C * Real.exp (-((t : ℝ) / 2 * (R : ℝ))) ∧
          ((xiGaussianConjugateOrbit q₀.1).card : ℝ) ≤
            ∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P t q ∧
          |xiGaussianCompletedSourceResidual P t +
            π * ((xiGaussianConjugateOrbit q₀.1).card : ℝ)| ≤
              π * C * Real.exp (-((t : ℝ) / 2 * (R : ℝ))) := by
  classical
  let z : {z : ℂ // z.im ≠ 0} := ⟨xiSpectralPoint q₀.1 ^ 2, q₀.property⟩
  let v := Complex.I * Complex.exp (((t : ℝ) : ℂ) * z / 2)
  obtain ⟨C, hC, htail⟩ := exists_xiGaussianNormalizedOrbit_exponential_tail z v t
  refine ⟨C, hC, fun R => ?_⟩
  obtain ⟨F, hF, hcut⟩ :=
    (htail.and (eventually_ge_atTop (finite_xiHeatShell R).toFinset)).exists
  let P := xiGaussianNegativeOrbitPolynomial t q₀.1 F
  let m : ℝ := (xiGaussianConjugateOrbit q₀.1).card
  let E := xiGaussianTailEnergy P t R
  have hE : E ≤ C * Real.exp (-((t : ℝ) / 2 * (R : ℝ))) := hF R
  have hE0 : 0 ≤ E := xiGaussianTailEnergy_nonneg P t R
  have hK : xiGaussianNativeEnergy P t = m + E :=
    (xiGaussianNegativeOrbitPolynomial_exact_remainder t q₀ R ⟨F, hcut⟩).2
  have hH : ‖xiPolynomialGaussianHeatTrace P t +
      ((xiGaussianConjugateOrbit q₀.1).card : ℂ)‖ ≤ E :=
    norm_xiGaussianNegativeOrbitPolynomial_remainder_le_tail t q₀ R ⟨F, hcut⟩
  have hHreal : |xiPolynomialGaussianHeatTraceReal P t + m| ≤ E := by
    exact (Complex.abs_re_le_norm
      (xiPolynomialGaussianHeatTrace P t +
        ((xiGaussianConjugateOrbit q₀.1).card : ℂ))).trans hH
  have hupper := (abs_le.mp hHreal).2
  refine ⟨P, ?_, ?_, hH.trans hE, ?_, ?_, ?_⟩
  · linarith only [hK, hE0]
  · linarith only [hK, hE]
  · rw [xiGaussianRealChannelEnergy_eq_half_energy_add_trace]
    change (xiGaussianNativeEnergy P t + xiPolynomialGaussianHeatTraceReal P t) / 2 ≤ _
    linarith only [hK, hupper, hE]
  · rw [xiGaussianImaginaryChannel_eq_half_nativeEnergy_sub_trace]
    linarith only [hK, hupper]
  · rw [xiGaussianCompletedSourceResidual_eq_trace, ← mul_add, abs_mul,
      abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_left (hHreal.trans hE) Real.pi_pos.le).trans_eq
      (by ring)

/-- An unconditional actual-divisor alternative, with an exponential full
remainder at every prescribed positive time. No off-critical copy is assumed. -/
theorem xiGaussian_fixedTime_exponential_localization_alternative :
    RiemannHypothesis ∨ ∀ t : {t : ℝ // 0 < t},
      ∃ m C R₀ : ℝ, 0 < m ∧ 0 < C ∧ ∀ R : Set.Ici R₀,
        ∃ P : Polynomial ℝ,
          m ≤ xiGaussianNativeEnergy P t ∧
          xiGaussianNativeEnergy P t ≤ m + C * Real.exp (-((t : ℝ) / 2 * (R : ℝ))) ∧
          ‖xiPolynomialGaussianHeatTrace P t + (m : ℂ)‖ ≤
            C * Real.exp (-((t : ℝ) / 2 * (R : ℝ))) := by
  classical
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · refine Or.inr fun t => ?_
    obtain ⟨q, hq⟩ := exists_spectralSq_im_pos_of_not_riemannHypothesis hRH
    let q₀ : {q : XiZeroCopy // (xiSpectralPoint q ^ 2).im ≠ 0} := ⟨q, ne_of_gt hq⟩
    obtain ⟨C, hC, hloc⟩ := exists_xiGaussian_fixedTime_exponential_orbit_localization t q₀
    have hm : (0 : ℝ) < (xiGaussianConjugateOrbit q).card := by
      exact_mod_cast xiGaussianConjugateOrbit_card_pos q
    refine ⟨(xiGaussianConjugateOrbit q).card, C, (xiSpectralPoint q ^ 2).re,
      hm, hC, fun R => ?_⟩
    obtain ⟨P, hKlo, hKhi, hH, _, _, _⟩ := hloc R
    refine ⟨P, hKlo, hKhi, ?_⟩
    simpa only [Complex.ofReal_natCast] using hH

end RHTower
