import GaloisForLFunctions.RHTower.XiGaussianFixedTimeLocalization
import GaloisForLFunctions.RHTower.XiGaussianAnnihilatorPhaseControl
import GaloisForLFunctions.RHTower.XiGaussianAnnihilatorPrimeCancellation
import GaloisForLFunctions.RHTower.XiGaussianRealChannelEnergy

/-!
# The sharp fixed-time phase threshold over all polynomial orders

If an off-critical orbit exists, full real polynomial tests approach the
negative energy endpoint at every positive time. Thus any positive uniform
real-channel fraction, however small, already forces RH. The theorem does
not produce that fraction or assert that an off-critical orbit exists.
-/

open Complex Filter Topology
open scoped Real
noncomputable section
namespace RHTower

/-- Arbitrarily sharp negative saturation at a prescribed positive time. -/
theorem exists_xiGaussian_fixedTime_near_negative_energy
    (t : {t : ℝ // 0 < t})
    (q₀ : {q : XiZeroCopy // (xiSpectralPoint q ^ 2).im ≠ 0})
    (ε : {ε : ℝ // 0 < ε}) :
    ∃ P : Polynomial ℝ, 0 < xiGaussianNativeEnergy P t ∧
      xiPolynomialGaussianHeatTraceReal P t < (-1 + (ε : ℝ)) * xiGaussianNativeEnergy P t := by
  obtain ⟨P, hK, hH⟩ := exists_xiGaussian_fixedTime_negative_localization t q₀
  have hm : (0 : ℝ) < (xiGaussianConjugateOrbit q₀.1).card := by
    exact_mod_cast xiGaussianConjugateOrbit_card_pos q₀.1
  have hlim := hH.sub (hK.const_mul (-1 + (ε : ℝ)))
  have hneg : -((xiGaussianConjugateOrbit q₀.1).card : ℝ) -
      (-1 + (ε : ℝ)) * (xiGaussianConjugateOrbit q₀.1).card < 0 := by
    nlinarith [mul_pos ε.property hm]
  obtain ⟨F, hF⟩ := ((hK.eventually (Ioi_mem_nhds hm)).and
    (hlim.eventually (Iio_mem_nhds hneg))).exists
  exact ⟨P F, hF.1, sub_neg.mp hF.2⟩

/-- An unconditional alternative on the actual divisor. The second branch
retains the full signed form, phase debt, real channel, and arithmetic source. -/
theorem xiGaussian_fixedTime_sharp_phase_alternative :
    RiemannHypothesis ∨
      ∀ (t : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}),
        ∃ P : Polynomial ℝ,
          0 < xiGaussianNativeEnergy P t ∧
          xiPolynomialGaussianHeatTraceReal P t < (-1 + (ε : ℝ)) * xiGaussianNativeEnergy P t ∧
          (2 - (ε : ℝ)) * xiGaussianNativeEnergy P t <
            2 * (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P t q) ∧
          xiGaussianRealChannelEnergy P t < (ε : ℝ) / 2 * xiGaussianNativeEnergy P t ∧
          xiGaussianCompletedSourceResidual P t <
            π * ((-1 + (ε : ℝ)) * xiGaussianNativeEnergy P t) := by
  classical
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · refine Or.inr fun t ε => ?_
    obtain ⟨q, hq⟩ := exists_spectralSq_im_pos_of_not_riemannHypothesis hRH
    obtain ⟨P, hK, hH⟩ := exists_xiGaussian_fixedTime_near_negative_energy t
      ⟨q, ne_of_gt hq⟩ ε
    refine ⟨P, hK, hH, ?_, ?_, ?_⟩
    · rw [xiGaussianImaginaryChannel_eq_half_nativeEnergy_sub_trace]
      linarith only [hH]
    · rw [xiGaussianRealChannelEnergy_eq_half_energy_add_trace]
      change (xiGaussianNativeEnergy P t + xiPolynomialGaussianHeatTraceReal P t) / 2 < _
      nlinarith only [hH]
    · rw [xiGaussianCompletedSourceResidual_eq_trace]
      exact mul_lt_mul_of_pos_left hH Real.pi_pos

/-- At one fixed positive time, any degree-independent retained fraction
in the actual real-amplitude channel already implies full RH. -/
theorem riemannHypothesis_iff_fixedTime_realChannel_floor
    (t : {t : ℝ // 0 < t}) :
    RiemannHypothesis ↔
      ∃ c : ℝ, 0 < c ∧ ∀ P : Polynomial ℝ,
        c * xiGaussianNativeEnergy P t ≤ xiGaussianRealChannelEnergy P t := by
  constructor
  · intro hRH
    refine ⟨1 / 2, by positivity, fun P => ?_⟩
    have hH := xiPolynomialGaussianHeatTraceReal_nonneg_of_riemannHypothesis hRH P t.property
    rw [xiGaussianRealChannelEnergy_eq_half_energy_add_trace]
    change 1 / 2 * xiGaussianNativeEnergy P t ≤
      (xiGaussianNativeEnergy P t + xiPolynomialGaussianHeatTraceReal P t) / 2
    linarith only [hH]
  · rintro ⟨c, hc, hfloor⟩
    rcases xiGaussian_fixedTime_sharp_phase_alternative with hRH | hbad
    · exact hRH
    · obtain ⟨P, hK, _, _, hJ, _⟩ := hbad t ⟨c, hc⟩
      have hF := hfloor P
      nlinarith [mul_pos hc hK]

/-- A strict uniform improvement over the trivial phase-debt bound `2K`
is sufficient; reaching the initially requested bound `K` is unnecessary. -/
theorem riemannHypothesis_iff_fixedTime_strict_phase_ceiling
    (t : {t : ℝ // 0 < t}) :
    RiemannHypothesis ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ P : Polynomial ℝ,
        2 * (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P t q) ≤
          (2 - δ) * xiGaussianNativeEnergy P t := by
  constructor
  · intro hRH
    refine ⟨1, one_pos, fun P => ?_⟩
    rw [xiGaussianImaginaryChannel_eq_half_nativeEnergy_sub_trace]
    have hH := xiPolynomialGaussianHeatTraceReal_nonneg_of_riemannHypothesis hRH P t.property
    linarith only [hH]
  · rintro ⟨δ, hδ, hbound⟩
    rcases xiGaussian_fixedTime_sharp_phase_alternative with hRH | hbad
    · exact hRH
    · obtain ⟨P, _, _, hD, _, _⟩ := hbad t ⟨δ, hδ⟩
      exact False.elim ((not_lt_of_ge (hbound P)) hD)

/-- For the existing relative-channel route, a finite uniform constant is
enough. It need not be at most one, but it must cover every polynomial order. -/
theorem riemannHypothesis_iff_fixedTime_relative_phase_bounded
    (t : {t : ℝ // 0 < t}) :
    RiemannHypothesis ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Polynomial ℝ,
        (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P t q) ≤
          C * xiGaussianRealChannelEnergy P t := by
  constructor
  · intro hRH
    refine ⟨1, zero_le_one, fun P => ?_⟩
    rw [xiGaussianImaginaryChannel_eq_half_nativeEnergy_sub_trace,
      xiGaussianRealChannelEnergy_eq_half_energy_add_trace, one_mul]
    change (xiGaussianNativeEnergy P t - xiPolynomialGaussianHeatTraceReal P t) / 2 ≤
      (xiGaussianNativeEnergy P t + xiPolynomialGaussianHeatTraceReal P t) / 2
    have hH := xiPolynomialGaussianHeatTraceReal_nonneg_of_riemannHypothesis hRH P t.property
    linarith only [hH]
  · rintro ⟨C, hC, hbound⟩
    have hden : 0 < C + 1 := by linarith
    apply (riemannHypothesis_iff_fixedTime_realChannel_floor t).mpr
    refine ⟨1 / (C + 1), one_div_pos.mpr hden, fun P => ?_⟩
    have hb := hbound P
    rw [xiGaussianImaginaryChannel_eq_half_nativeEnergy_sub_trace] at hb
    have hJ := xiGaussianRealChannelEnergy_eq_half_energy_add_trace P t
    change xiGaussianRealChannelEnergy P t =
      (xiGaussianNativeEnergy P t + xiPolynomialGaussianHeatTraceReal P t) / 2 at hJ
    rw [one_div_mul_eq_div, div_le_iff₀ hden]
    nlinarith only [hb, hJ]

end RHTower
