import GaloisForLFunctions.RHTower.BernsteinEllipseMixedModeGap
import GaloisForLFunctions.RHTower.PrimeArchBernsteinConfinedPhase
import GaloisForLFunctions.RHTower.FiniteExponentialPencilUniformGap

/-!
# Uniform maximal-packet gap for the Xi Bernstein source

Failure of RH produces a finite, source-attained maximal endpoint-amplitude packet.  Its
complement lies below one common strict submaximal amplitude.  On the maximal packet, distinct
normalized reciprocal-square coordinates have distinct Bernstein ellipse phases.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Endpoint atom amplitudes converge cofinally to the neutral value one. -/
theorem tendsto_xiEndpointBernsteinAtomAmplitudeBase_cofinite_one :
    Tendsto xiEndpointBernsteinAtomAmplitudeBase cofinite (nhds 1) := by
  have hzero : Tendsto xiZeroCopyReciprocalSquare cofinite (nhds 0) :=
    summable_xiZeroCopyReciprocalSquare.tendsto_cofinite_zero
  have hu : Tendsto xiEndpointNormalizedReciprocalSquare cofinite (nhds 0) := by
    have h2 : Tendsto (fun q : XiZeroCopy =>
        xiZeroCopyReciprocalSquare q / (primeArchEndpointHausdorffRadius : ℂ))
        cofinite (nhds 0) := by
      simpa using hzero.div_const (primeArchEndpointHausdorffRadius : ℂ)
    exact h2
  have hone : Tendsto (fun _ : XiZeroCopy => (1 : ℂ)) cofinite (nhds 1) :=
    tendsto_const_nhds
  have h := hu.norm.add (hone.sub hu).norm
  have h2 : Tendsto (fun q : XiZeroCopy =>
      ‖xiEndpointNormalizedReciprocalSquare q‖ +
        ‖1 - xiEndpointNormalizedReciprocalSquare q‖) cofinite (nhds 1) := by
    simpa only [norm_zero, sub_zero, norm_one, zero_add] using h
  exact h2

/-- Failure of RH supplies one strictly superunit endpoint amplitude. -/
theorem exists_one_lt_xiEndpointBernsteinAtomAmplitudeBase_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ q : XiZeroCopy, 1 < xiEndpointBernsteinAtomAmplitudeBase q := by
  obtain ⟨q, hqim⟩ :=
    exists_xiZeroCopyReciprocalSquare_im_ne_zero_of_not_riemannHypothesis hRH
  have huim : (xiEndpointNormalizedReciprocalSquare q).im ≠ 0 := by
    dsimp only [xiEndpointNormalizedReciprocalSquare]
    rw [Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_div, sub_zero,
      Complex.normSq_ofReal]
    exact div_ne_zero
      (mul_ne_zero hqim primeArchEndpointHausdorffRadius_pos.ne')
      (mul_ne_zero primeArchEndpointHausdorffRadius_pos.ne'
        primeArchEndpointHausdorffRadius_pos.ne')
  exact ⟨q, by
    simpa only [xiEndpointBernsteinAtomAmplitudeBase, add_comm] using
      one_lt_norm_add_norm_one_sub huim⟩

/-- **Finite uniformly separated maximal Xi endpoint-amplitude packet.** -/
theorem exists_uniformlySeparated_maximal_xiEndpointAmplitudePacket_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ D : Finset XiZeroCopy, ∃ B beta : ℝ,
      1 < B ∧ 1 < beta ∧ beta < B ∧ D.Nonempty ∧
        (∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) ∧
        (∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) := by
  let A : XiZeroCopy → ℝ := xiEndpointBernsteinAtomAmplitudeBase
  let a : XiZeroCopy → ℂ := fun q => (A q : ℂ)
  have hA : Tendsto A cofinite (nhds 1) :=
    tendsto_xiEndpointBernsteinAtomAmplitudeBase_cofinite_one
  have ha : Tendsto a cofinite (nhds 1) := by
    have h := Complex.continuous_ofReal.tendsto 1
    exact h.comp hA
  obtain ⟨q0, hq0⟩ := exists_one_lt_xiEndpointBernsteinAtomAmplitudeBase_of_not_rh hRH
  have hAnonneg (q : XiZeroCopy) : 0 ≤ A q :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hnorm (q : XiZeroCopy) : ‖a q‖ = A q := by
    dsimp only [a]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hAnonneg q)]
  have hq0a : 1 < ‖a q0‖ := by rw [hnorm]; exact hq0
  obtain ⟨D, B, beta, hB, hbeta1, hbeta, hDne, hD, hDsub⟩ :=
    exists_finite_maximal_norm_packet_uniformly_separated a ha hq0a
  refine ⟨D, B, beta, hB, hbeta1, hbeta, hDne, ?_, ?_⟩
  · intro q hq
    simpa only [hnorm] using hD q hq
  · intro q hq
    simpa only [hnorm] using hDsub q hq

/-- A strictly superunit endpoint amplitude is off the critical line and has nonreal normalized
reciprocal-square coordinate. -/
lemma xiEndpoint_offLine_and_normalized_im_ne_zero_of_one_lt_amplitude
    (q : XiZeroCopy) (hA : 1 < xiEndpointBernsteinAtomAmplitudeBase q) :
    (q.1 : ℂ).re ≠ 1 / 2 ∧ (xiEndpointNormalizedReciprocalSquare q).im ≠ 0 := by
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := by
    intro hline
    have hone := xiEndpointBernsteinAtomAmplitudeBase_eq_one_of_onLine q hline
    linarith
  refine ⟨hoff, ?_⟩
  have him0 : (xiZeroCopyReciprocalSquare q).im ≠ 0 := by
    rw [xiZeroCopyReciprocalSquare_eq]
    exact fun him => hoff ((xiCentralReciprocalSquare_im_eq_zero_iff q.1).mp him)
  dsimp only [xiEndpointNormalizedReciprocalSquare]
  rw [Complex.div_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_div, sub_zero,
    Complex.normSq_ofReal]
  exact div_ne_zero
    (mul_ne_zero him0 primeArchEndpointHausdorffRadius_pos.ne')
    (mul_ne_zero primeArchEndpointHausdorffRadius_pos.ne'
      primeArchEndpointHausdorffRadius_pos.ne')

/-- Distinct maximal Xi coordinates have distinct maximizing ellipse phases. -/
theorem bernsteinEllipsePhase_ne_of_distinct_maximal_xiEndpointCoordinates
    {q r : XiZeroCopy} {B : ℝ}
    (hB : 1 < B)
    (hqB : xiEndpointBernsteinAtomAmplitudeBase q = B)
    (hrB : xiEndpointBernsteinAtomAmplitudeBase r = B)
    (hcoord : xiEndpointNormalizedReciprocalSquare q ≠
      xiEndpointNormalizedReciprocalSquare r) :
    bernsteinEllipsePhase (xiEndpointNormalizedReciprocalSquare q) ≠
      bernsteinEllipsePhase (xiEndpointNormalizedReciprocalSquare r) := by
  let u := xiEndpointNormalizedReciprocalSquare q
  let v := xiEndpointNormalizedReciprocalSquare r
  have hqA : 1 < xiEndpointBernsteinAtomAmplitudeBase q := hB.trans_eq hqB.symm
  have hrA : 1 < xiEndpointBernsteinAtomAmplitudeBase r := hB.trans_eq hrB.symm
  obtain ⟨hqoff, huim⟩ :=
    xiEndpoint_offLine_and_normalized_im_ne_zero_of_one_lt_amplitude q hqA
  obtain ⟨hroff, hvim⟩ :=
    xiEndpoint_offLine_and_normalized_im_ne_zero_of_one_lt_amplitude r hrA
  intro hphase
  have hamp : ‖v‖ + ‖1 - v‖ = ‖u‖ + ‖1 - u‖ := by
    simpa only [u, v, xiEndpointBernsteinAtomAmplitudeBase] using hrB.trans hqB.symm
  rcases eq_or_eq_one_sub_conj_of_bernsteinEllipsePhase_eq_of_amplitude_eq
    huim hvim hphase.symm hamp with heq | hreflect
  · exact hcoord heq.symm
  · have hqbound := norm_xiEndpointNormalizedReciprocalSquare_le_offLineRadius q hqoff
    have hrbound := norm_xiEndpointNormalizedReciprocalSquare_le_offLineRadius r hroff
    change ‖u‖ ≤ xiOffLineNormalizedBernsteinRadius at hqbound
    change ‖v‖ ≤ xiOffLineNormalizedBernsteinRadius at hrbound
    have hone : (1 : ℝ) ≤ ‖1 - star u‖ + ‖star u‖ := by
      have htri := norm_add_le (1 - star u) (star u)
      norm_num at htri ⊢
      exact htri
    rw [← hreflect, norm_star] at hone
    nlinarith [xiOffLineNormalizedBernsteinRadius_lt_one_fourth]

/-- Distinct coordinates in one maximal Xi packet have a uniform mixed Gutzmer radius below
`B^(2 : ℕ)`. -/
theorem exists_uniform_mixedXiBernsteinProduct_gap_of_distinct_maximal_coordinates
    {q r : XiZeroCopy} {B : ℝ}
    (hB : 1 < B)
    (hqB : xiEndpointBernsteinAtomAmplitudeBase q = B)
    (hrB : xiEndpointBernsteinAtomAmplitudeBase r = B)
    (hcoord : xiEndpointNormalizedReciprocalSquare q ≠
      xiEndpointNormalizedReciprocalSquare r) :
    ∃ gamma : ℝ, 0 ≤ gamma ∧ gamma < B ^ (2 : ℕ) ∧
      ∀ w : ℂ, ‖w‖ = 1 →
        ‖reflectedBernsteinProduct
          (xiEndpointNormalizedReciprocalSquare q)
          (xiEndpointNormalizedReciprocalSquare r) w‖ ≤ gamma := by
  have hqA : 1 < xiEndpointBernsteinAtomAmplitudeBase q := hB.trans_eq hqB.symm
  have hrA : 1 < xiEndpointBernsteinAtomAmplitudeBase r := hB.trans_eq hrB.symm
  obtain ⟨_, huim⟩ :=
    xiEndpoint_offLine_and_normalized_im_ne_zero_of_one_lt_amplitude q hqA
  obtain ⟨_, hvim⟩ :=
    xiEndpoint_offLine_and_normalized_im_ne_zero_of_one_lt_amplitude r hrA
  apply exists_uniform_reflectedBernsteinProduct_gap_of_phase_ne huim hvim
  · simpa only [xiEndpointBernsteinAtomAmplitudeBase] using hqB
  · simpa only [xiEndpointBernsteinAtomAmplitudeBase] using hrB
  · exact bernsteinEllipsePhase_ne_of_distinct_maximal_xiEndpointCoordinates
      hB hqB hrB hcoord

/-- Distinct maximal Xi coordinates have exponentially subdominant normalized cross moments. -/
theorem exists_uniform_mixedXiBernsteinCrossMoment_gap_of_distinct_maximal_coordinates
    {q r : XiZeroCopy} {B : ℝ}
    (hB : 1 < B)
    (hqB : xiEndpointBernsteinAtomAmplitudeBase q = B)
    (hrB : xiEndpointBernsteinAtomAmplitudeBase r = B)
    (hcoord : xiEndpointNormalizedReciprocalSquare q ≠
      xiEndpointNormalizedReciprocalSquare r) :
    ∃ gamma : ℝ, 0 ≤ gamma ∧ gamma < B ^ (2 : ℕ) ∧
      ∀ n : ℕ,
        ‖reflectedBernsteinCrossMoment
          (xiEndpointNormalizedReciprocalSquare q)
          (xiEndpointNormalizedReciprocalSquare r) n‖ ≤ gamma ^ n := by
  obtain ⟨gamma, hgamma0, hgamma, hpoint⟩ :=
    exists_uniform_mixedXiBernsteinProduct_gap_of_distinct_maximal_coordinates
      hB hqB hrB hcoord
  exact ⟨gamma, hgamma0, hgamma,
    norm_reflectedBernsteinCrossMoment_le_pow hpoint⟩

end


end RHTower
