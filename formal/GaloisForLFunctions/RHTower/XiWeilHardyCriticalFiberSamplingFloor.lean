import GaloisForLFunctions.RHTower.XiWeilHardyReferenceLorentzianPlane
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity

/-!
# Hardy critical-fiber sampling floor for the Xi Weil source

A complete analytic-multiplicity fiber is a finite-rank positive spectral block whenever its
centered Xi coordinate lies on the real axis.  This module computes its exact Hilbert mass and its
pairing with every spectral-fiber-constant vector.  For a separated continued-Cauchy source packet
`P`, the contribution of a fixed Xi divisor point `ρ` is

`multiplicity(ρ) * ‖∑ i, coeff i / (xiSpectralPointSupport ρ - pole i)‖²`.

RH is equivalent to the explicit prime--Gamma source energy dominating this one sampling floor for
every packet.  The result holds at every fixed Xi divisor point; Hardy's theorem supplies an
unconditional point on the critical line.  Equivalently, subtracting one known complete fiber from
the Weil source leaves a nonnegative residual exactly under RH.

This is the sharp positive survivor of spectral deflation.  It does not prove residual source
positivity: diagonal positivity alone is not stable under positive-atom subtraction, and the
Burnol source-leakage and Hedenmalm continuous-frame identities do not control this residual.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

/-- Pairing a complete fiber indicator against a fiber-constant vector is multiplicity times any
one coordinate on that fiber. -/
theorem inner_xiWeilFiberIndicatorLp_eq_card_mul
    (ρ : XiDivisorSupport) (w : XiWeilCarrier)
    (hw : FactorsThroughSpectral w) :
    inner ℂ (xiWeilFiberIndicatorLp (xiSpectralPointSupport ρ)) w =
      ((xiZeroCopyFiber ρ).card : ℂ) * w (xiFirstZeroCopy ρ) := by
  rw [lp.inner_eq_tsum]
  rw [tsum_eq_sum (s := xiZeroCopyFiber ρ) (fun q hq => by
    rw [xiWeilFiberIndicatorLp_apply]
    have hne : xiSpectralPoint q ≠ xiSpectralPointSupport ρ := by
      intro h
      apply hq
      rw [mem_xiZeroCopyFiber]
      exact xiSpectralPointSupport_injective (by
        simpa only [xiSpectralPoint_eq_support] using h)
    simp [hne])]
  calc
    ∑ q ∈ xiZeroCopyFiber ρ,
        inner ℂ (xiWeilFiberIndicatorLp (xiSpectralPointSupport ρ) q) (w q) =
        ∑ q ∈ xiZeroCopyFiber ρ, w (xiFirstZeroCopy ρ) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hρ : q.1 = ρ := mem_xiZeroCopyFiber.mp hq
      have hspectral : xiSpectralPoint q =
          xiSpectralPoint (xiFirstZeroCopy ρ) := by
        simp only [xiSpectralPoint_eq_support, hρ, xiFirstZeroCopy_fst]
      rw [xiWeilFiberIndicatorLp_apply]
      simp only [xiSpectralPoint_eq_support, hρ]
      rw [hw q (xiFirstZeroCopy ρ) hspectral]
      simp
    _ = ((xiZeroCopyFiber ρ).card : ℂ) * w (xiFirstZeroCopy ρ) := by simp

/-- The squared Hilbert norm of a complete fiber indicator is its analytic multiplicity. -/
theorem norm_sq_xiWeilFiberIndicatorLp_eq_card (ρ : XiDivisorSupport) :
    ‖xiWeilFiberIndicatorLp (xiSpectralPointSupport ρ)‖ ^ 2 =
      (xiZeroCopyFiber ρ).card := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  have hfac : FactorsThroughSpectral
      (xiWeilFiberIndicatorLp (xiSpectralPointSupport ρ)) := by
    intro q q' hqq
    simp only [xiWeilFiberIndicatorLp_apply, hqq]
  rw [inner_xiWeilFiberIndicatorLp_eq_card_mul ρ _ hfac]
  simp [xiWeilFiberIndicatorLp_apply, xiSpectralPoint_eq_support]

/-- Exact squared overlap with a complete multiplicity fiber. -/
theorem normSq_inner_xiWeilFiberIndicatorLp_eq_card_sq_mul
    (ρ : XiDivisorSupport) (w : XiWeilCarrier)
    (hw : FactorsThroughSpectral w) :
    Complex.normSq
        (inner ℂ (xiWeilFiberIndicatorLp (xiSpectralPointSupport ρ)) w) =
      ((xiZeroCopyFiber ρ).card : ℝ) ^ 2 *
        Complex.normSq (w (xiFirstZeroCopy ρ)) := by
  rw [inner_xiWeilFiberIndicatorLp_eq_card_mul ρ w hw,
    Complex.normSq_mul]
  simp [Complex.normSq_eq_norm_sq]

/-- Fixed-fiber sampling theorem.  RH holds exactly when every separated prime--Gamma packet's
source energy dominates the full multiplicity-weighted mass sampled at `ρ`. -/
theorem riemannHypothesis_iff_fixedFiber_samplingFloor
    (ρ : XiDivisorSupport) :
    RiemannHypothesis ↔
      ∀ P : XiSeparatedContinuedCauchyPacket,
        ((xiZeroCopyFiber ρ).card : ℝ) *
            Complex.normSq (P.evaluation (xiFirstZeroCopy ρ)) ≤
          P.sourceEnergy := by
  have hmNat : 0 < (xiZeroCopyFiber ρ).card := by
    rw [Finset.card_pos]
    exact ⟨xiFirstZeroCopy ρ, mem_xiZeroCopyFiber.mpr rfl⟩
  have hm : 0 < ((xiZeroCopyFiber ρ).card : ℝ) := by exact_mod_cast hmNat
  constructor
  · intro hRH P
    let v : XiWeilCarrier :=
      xiWeilFiberIndicatorLp (xiSpectralPointSupport ρ)
    let w : XiWeilCarrier := P.evaluation
    have hwfac : FactorsThroughSpectral w := by
      dsimp only [w, XiSeparatedContinuedCauchyPacket.evaluation]
      letI := P.fintypeIndex
      exact factorsThroughSpectral_xiWeilContinuedCauchyPacketLp P.coeff P.pole
    have hcs0 := norm_inner_le_norm (𝕜 := ℂ) v w
    have hcs : Complex.normSq (inner ℂ v w) ≤ ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      calc
        ‖inner ℂ v w‖ ^ 2 ≤ (‖v‖ * ‖w‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hcs0 2
        _ = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by ring
    have hvnorm : ‖v‖ ^ 2 = ((xiZeroCopyFiber ρ).card : ℝ) := by
      exact norm_sq_xiWeilFiberIndicatorLp_eq_card ρ
    have hinner : Complex.normSq (inner ℂ v w) =
        ((xiZeroCopyFiber ρ).card : ℝ) ^ 2 *
          Complex.normSq (w (xiFirstZeroCopy ρ)) := by
      exact normSq_inner_xiWeilFiberIndicatorLp_eq_card_sq_mul ρ w hwfac
    have hJ : xiWeilLineConjLp w = w := by
      apply Subtype.ext
      funext q
      rw [xiWeilLineConjLp_apply,
        xiZeroCopyLineConjEquiv_eq_of_riemannHypothesis hRH q]
    have henergy : P.sourceEnergy = ‖w‖ ^ 2 := by
      rw [P.sourceEnergy_eq_hilbertQuadratic, xiWeilHilbertQuadratic,
        xiWeilLineConjLinearIsometry_apply, hJ]
      change (inner ℂ w w).re = ‖w‖ ^ 2
      exact inner_self_eq_norm_sq (𝕜 := ℂ) w
    rw [hinner, hvnorm, ← henergy] at hcs
    nlinarith
  · intro hall
    by_contra hRH
    obtain ⟨P, hP⟩ :=
      not_riemannHypothesis_iff_exists_xiSeparatedPacket_sourceEnergy_neg.mp hRH
    have hfloor := hall P
    have hnonneg : 0 ≤ ((xiZeroCopyFiber ρ).card : ℝ) *
        Complex.normSq (P.evaluation (xiFirstZeroCopy ρ)) :=
      mul_nonneg hm.le (Complex.normSq_nonneg _)
    linarith

/-- The sampled packet value is the literal finite Cauchy sum at the selected Xi point. -/
theorem XiSeparatedContinuedCauchyPacket.evaluation_firstZeroCopy_eq
    (P : XiSeparatedContinuedCauchyPacket) (ρ : XiDivisorSupport) :
    P.evaluation (xiFirstZeroCopy ρ) =
      Finset.sum (@Finset.univ P.index P.fintypeIndex) (fun i =>
        P.coeff i *
          (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹) := by
  letI := P.fintypeIndex
  change xiWeilContinuedCauchyPacketLp P.coeff P.pole
      (xiFirstZeroCopy ρ) = _
  rw [← xiWeilEvaluationLp_indexedCauchyPacket,
    xiWeilEvaluationLp_apply, xiWeilIndexedCauchyPacket]
  simp only [xiWeilCauchyTest, xiSpectralPoint_eq_support,
    xiFirstZeroCopy_fst]

/-- Source-explicit form of the fixed-fiber criterion: both sides are finite prime--Gamma/Cauchy
expressions attached to the packet. -/
theorem riemannHypothesis_iff_fixedFiber_explicitSourceSamplingFloor
    (ρ : XiDivisorSupport) :
    RiemannHypothesis ↔
      ∀ P : XiSeparatedContinuedCauchyPacket,
        ((xiZeroCopyFiber ρ).card : ℝ) *
            Complex.normSq
              (Finset.sum (@Finset.univ P.index P.fintypeIndex) (fun i =>
                P.coeff i *
                  (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹)) ≤
          P.sourceEnergy := by
  constructor
  · intro hRH P
    have hfloor :=
      (riemannHypothesis_iff_fixedFiber_samplingFloor ρ).mp hRH P
    simpa only [P.evaluation_firstZeroCopy_eq ρ] using hfloor
  · intro hall
    apply (riemannHypothesis_iff_fixedFiber_samplingFloor ρ).mpr
    intro P
    simpa only [P.evaluation_firstZeroCopy_eq ρ] using hall P

/-- False RH is exactly strict failure of the explicit sampling floor at the chosen fiber. -/
theorem not_riemannHypothesis_iff_exists_fixedFiber_explicitSourceSamplingFloor_failure
    (ρ : XiDivisorSupport) :
    ¬RiemannHypothesis ↔
      ∃ P : XiSeparatedContinuedCauchyPacket,
        P.sourceEnergy <
          ((xiZeroCopyFiber ρ).card : ℝ) *
            Complex.normSq
              (Finset.sum (@Finset.univ P.index P.fintypeIndex) (fun i =>
                P.coeff i *
                  (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹)) := by
  have hcriterion := riemannHypothesis_iff_fixedFiber_explicitSourceSamplingFloor ρ
  constructor
  · intro hRH
    have hfail : ¬ ∀ P : XiSeparatedContinuedCauchyPacket,
        ((xiZeroCopyFiber ρ).card : ℝ) *
            Complex.normSq
              (Finset.sum (@Finset.univ P.index P.fintypeIndex) (fun i =>
                P.coeff i *
                  (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹)) ≤
          P.sourceEnergy := by
      exact fun hall => hRH (hcriterion.mpr hall)
    simpa only [not_forall, not_le] using hfail
  · rintro ⟨P, hP⟩ hRH
    exact (not_lt_of_ge (hcriterion.mp hRH P)) hP

/-- Hardy's theorem selects an unconditional critical-line fiber at which the source-explicit
sampling-floor criterion is equivalent to RH. -/
theorem exists_hardyCriticalFiber_explicitSourceSamplingFloor_criterion :
    ∃ ρ : XiDivisorSupport,
      (ρ : ℂ).re = 1 / 2 ∧
        (RiemannHypothesis ↔
          ∀ P : XiSeparatedContinuedCauchyPacket,
            ((xiZeroCopyFiber ρ).card : ℝ) *
                Complex.normSq
                  (Finset.sum (@Finset.univ P.index P.fintypeIndex) (fun i =>
                    P.coeff i *
                      (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹)) ≤
              P.sourceEnergy) := by
  obtain ⟨ρ, hρ⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  exact ⟨ρ, hρ,
    riemannHypothesis_iff_fixedFiber_explicitSourceSamplingFloor ρ⟩

end

end RHTower
