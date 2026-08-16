import GaloisForLFunctions.RHTower.FrankensteinSourceGammaCenteredMonodromyCartier
import GaloisForLFunctions.RHTower.XiDepthSuccessorStokesNormalLayer
import GaloisForLFunctions.HTGeometry.GammaMultiplication

/-!
# Gamma composition no-go and two-orientation scale-zero descent

Gauss multiplication contributes the horizontal character `n⁻ᵗ`.  Its cover-composition law is
`(mn)⁻ᵗ = m⁻ᵗ n⁻ᵗ`, so the two-then-three and three-then-two Gamma squares commute for every real
grade.  At the strict off-line test grade `t = 1/2` this coherence still holds while the prime-two
and prime-three ghosts differ.  Ordinary Gamma multiplication naturality therefore cannot produce
the shared ghost.

The positive survivor is stronger and source-geometric.  Demand coefficient-faithful forward and
reflected centered characters on the *same* scale carrier, each continuous through the collapsed
scale and unital there.  A positive exponent tends to zero at the collapsed scale, contradicting
the retained unit; applying this to `t` and `-t` forces both inequalities and hence `t = 0`.

For every retained Xi divisor this source-zero descent is equivalent to centered log-cover descent,
rational Cartier landing, and existence of the genuine source-natural Gamma reporter.  No descent
or critical-line premise is asserted.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-! ## Ordinary Gamma composition is too weak -/

/-- Horizontal scalar appearing in Gauss multiplication after restriction to real grade. -/
def gammaCoverHorizontalAnomaly (t : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-t)

/-- Gauss cover anomalies compose multiplicatively for every grade. -/
theorem gammaCoverHorizontalAnomaly_mul
    (t : ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    gammaCoverHorizontalAnomaly t (m * n) =
      gammaCoverHorizontalAnomaly t m * gammaCoverHorizontalAnomaly t n := by
  rw [gammaCoverHorizontalAnomaly, gammaCoverHorizontalAnomaly,
    gammaCoverHorizontalAnomaly, Nat.cast_mul]
  exact Real.mul_rpow (by exact_mod_cast hm.le) (by exact_mod_cast hn.le)

/-- The `(2,3)` composition anomaly is the product of the two fitted local Gamma ghosts. -/
theorem gammaCoverHorizontalAnomaly_two_three (t : ℝ) :
    gammaCoverHorizontalAnomaly t 6 =
      primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo *
        primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeThree := by
  rw [show 6 = 2 * 3 by norm_num,
    gammaCoverHorizontalAnomaly_mul t (by norm_num) (by norm_num)]
  rfl

/-- Strict off-line countermodel: composition remains coherent at `t=1/2`, but the two local
ghosts are not one shared scalar. -/
theorem primeGammaLocalInverseOrientedGhost_two_ne_three_half :
    primeGammaLocalInverseOrientedGhost (1 / 2 : ℝ)
        deningerCalderonWittPrimeTwo ≠
      primeGammaLocalInverseOrientedGhost (1 / 2 : ℝ)
        deningerCalderonWittPrimeThree := by
  intro hEq
  have hshared : PrimeGammaTwoThreeSharedInverseOrientedGhostWard (1 / 2 : ℝ) := by
    refine ⟨primeGammaLocalInverseOrientedGhost (1 / 2 : ℝ)
      deningerCalderonWittPrimeTwo,
      primeGammaLocalInverseOrientedGhost_pos _ _,
      primeGammaLocalInverseOrientedGhost_ward _ _, ?_⟩
    rw [hEq]
    exact primeGammaLocalInverseOrientedGhost_ward _ _
  have hzero :=
    (primeGammaTwoThreeSharedInverseOrientedGhostWard_iff (1 / 2 : ℝ)).1 hshared
  norm_num at hzero

/-- Explicit failure of the implication “Gamma cover composition gives a shared ghost”. -/
theorem gammaCoverComposition_coherent_but_not_shared_at_half :
    gammaCoverHorizontalAnomaly (1 / 2 : ℝ) 6 =
        primeGammaLocalInverseOrientedGhost (1 / 2 : ℝ)
            deningerCalderonWittPrimeTwo *
          primeGammaLocalInverseOrientedGhost (1 / 2 : ℝ)
            deningerCalderonWittPrimeThree ∧
      primeGammaLocalInverseOrientedGhost (1 / 2 : ℝ)
          deningerCalderonWittPrimeTwo ≠
        primeGammaLocalInverseOrientedGhost (1 / 2 : ℝ)
          deningerCalderonWittPrimeThree :=
  ⟨gammaCoverHorizontalAnomaly_two_three _,
    primeGammaLocalInverseOrientedGhost_two_ne_three_half⟩

/-! ## Stronger source-selected scale-zero descent -/

/-- Both coefficient-faithful orientations extend continuously through the collapsed scale on one
source carrier and retain its unit.  Functions are part of the witness so no power-function
continuity at zero is assumed. -/
def SourceCenteredTwoOrientationUnitalScaleZeroDescent (t : ℝ) : Prop :=
  ∃ forward reflected : ℝ → ℝ,
    ContinuousAt forward 0 ∧
    ContinuousAt reflected 0 ∧
    forward 0 = 1 ∧
    reflected 0 = 1 ∧
    (∀ x : ℝ, 0 < x → forward x = x ^ t) ∧
    (∀ x : ℝ, 0 < x → reflected x = x ^ (-t))

/-- A unital continuous scale-zero extension of one real character forbids positive exponent. -/
private theorem sourceUnitalScaleZeroExponent_nonpos
    {t : ℝ} {f : ℝ → ℝ}
    (hcont : ContinuousAt f 0) (hzero : f 0 = 1)
    (hchar : ∀ x : ℝ, 0 < x → f x = x ^ t) :
    t ≤ 0 := by
  by_contra ht
  have htpos : 0 < t := lt_of_not_ge ht
  have hpow : Tendsto (fun x : ℝ => x ^ t)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    simpa [Real.zero_rpow htpos.ne'] using
      (Real.continuousAt_rpow_const 0 t (Or.inr htpos.le)).tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 0 from inf_le_left)
  have heq : f =ᶠ[nhdsWithin 0 (Ioi 0)] (fun x : ℝ => x ^ t) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hchar x hx
  have hfzero : Tendsto f (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
    hpow.congr' heq.symm
  have hfone : Tendsto f (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
    simpa [hzero] using hcont.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 0 from inf_le_left)
  have : (0 : ℝ) = 1 := tendsto_nhds_unique hfzero hfone
  norm_num at this

/-- Two retained orientations turn scale-zero regularity into exact neutral-grade selection. -/
theorem sourceCenteredTwoOrientationUnitalScaleZeroDescent_iff (t : ℝ) :
    SourceCenteredTwoOrientationUnitalScaleZeroDescent t ↔ t = 0 := by
  constructor
  · rintro ⟨forward, reflected, hfcont, hrcont, hfzero, hrzero,
      hfchar, hrchar⟩
    have htle : t ≤ 0 :=
      sourceUnitalScaleZeroExponent_nonpos hfcont hfzero hfchar
    have hneg : -t ≤ 0 :=
      sourceUnitalScaleZeroExponent_nonpos hrcont hrzero hrchar
    linarith
  · rintro rfl
    refine ⟨fun _ => 1, fun _ => 1, continuousAt_const, continuousAt_const,
      rfl, rfl, ?_, ?_⟩
    · intro x hx
      simp
    · intro x hx
      simp

/-- Source-zero descent specialized to the actual centered grade of one retained divisor. -/
def FrankensteinXiTwoOrientationUnitalScaleZeroDescendsAt
    (rho : XiDivisorSupport) : Prop :=
  SourceCenteredTwoOrientationUnitalScaleZeroDescent
    (primeDepthBVWoldXiCenteredRate rho)

theorem frankensteinXiTwoOrientationUnitalScaleZeroDescendsAt_iff
    (rho : XiDivisorSupport) :
    FrankensteinXiTwoOrientationUnitalScaleZeroDescendsAt rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [FrankensteinXiTwoOrientationUnitalScaleZeroDescendsAt,
    sourceCenteredTwoOrientationUnitalScaleZeroDescent_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Scale-zero descent constructs the previously missing coefficient-faithful rational Cartier
landing, for every retained prime label. -/
theorem frankensteinXiTwoOrientationUnitalScaleZeroDescendsAt_constructs_cartier
    (rho : XiDivisorSupport)
    (h : FrankensteinXiTwoOrientationUnitalScaleZeroDescendsAt rho)
    (p : Nat.Primes) :
    CCMRationalAdelicPrimeXiRationalCartierLanding p rho := by
  apply (xiCenteredLogCharacterDescends_iff_rationalCartierLanding rho p).1
  apply (xiCenteredLogCharacterDescends_iff_centeredRate_eq_zero rho).2
  exact (sourceCenteredTwoOrientationUnitalScaleZeroDescent_iff _).1 h

/-- Same source-zero witness constructs a genuine source-natural `(2,3)` Gamma reporter rather
than assuming a shared scalar. -/
theorem frankensteinXiTwoOrientationUnitalScaleZeroDescendsAt_constructs_reporter
    (rho : XiDivisorSupport)
    (h : FrankensteinXiTwoOrientationUnitalScaleZeroDescendsAt rho) :
    Nonempty
      (PrimeGammaTwoThreeSourceNaturalReporter
        (primeDepthBVWoldXiCenteredRate rho)) := by
  apply (primeGammaTwoThreeSourceNaturalReporter_nonempty_iff _).2
  apply (primeGammaTwoThreeSourceNaturalInverseGhost_iff _).2
  exact (sourceCenteredTwoOrientationUnitalScaleZeroDescent_iff _).1 h

/-! ## Exact identification with the multiplicity-faithful Xi nearby layer -/

/-- Fixed-fibre equality of the actual source-inverse and analytic-adjoint nearby-cycle profiles.
Unlike equality of orders, norms, or transported reflection fibres, this retains both pole
locations and the full Xi multiplicity. -/
def FrankensteinXiInverseAdjointNearbyCycleDescendsAt
    (rho : XiDivisorSupport) : Prop :=
  depthSuccessorNearbyCycle (-((rho : ℂ) - 1 / 2))
      (analyticOrderAt xi (rho : ℂ)).toNat =
    depthSuccessorNearbyCycle
      ((starRingEnd ℂ) ((rho : ℂ) - 1 / 2))
      (analyticOrderAt xi (rho : ℂ)).toNat

/-- Equality of the two rational normal profiles is exactly critical-line placement. -/
theorem frankensteinXiInverseAdjointNearbyCycleDescendsAt_iff
    (rho : XiDivisorSupport) :
    FrankensteinXiInverseAdjointNearbyCycleDescendsAt rho ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    exact criticalLine_of_inverse_adjoint_nearbyCycle_eq
      (xi_eq_zero_of_mem_divisor_support rho) h
  · intro hline
    have hshift : -((rho : ℂ) - 1 / 2) =
        (starRingEnd ℂ) ((rho : ℂ) - 1 / 2) := by
      apply Complex.ext
      · simp [hline]
      · simp
    unfold FrankensteinXiInverseAdjointNearbyCycleDescendsAt
    rw [hshift]

/-- Cross-corpus identification: source-zero regularity and equality of the two genuine Xi normal
layers are one producer, not merely two conditions with the same global RH endpoint. -/
theorem frankensteinXiTwoOrientationUnitalScaleZeroDescendsAt_iff_nearbyCycle
    (rho : XiDivisorSupport) :
    FrankensteinXiTwoOrientationUnitalScaleZeroDescendsAt rho ↔
      FrankensteinXiInverseAdjointNearbyCycleDescendsAt rho := by
  rw [frankensteinXiTwoOrientationUnitalScaleZeroDescendsAt_iff,
    frankensteinXiInverseAdjointNearbyCycleDescendsAt_iff]

/-- A same-fibre nearby-cycle descent constructs the requested source-natural Gamma reporter. -/
theorem frankensteinXiInverseAdjointNearbyCycleDescendsAt_constructs_reporter
    (rho : XiDivisorSupport)
    (h : FrankensteinXiInverseAdjointNearbyCycleDescendsAt rho) :
    Nonempty
      (PrimeGammaTwoThreeSourceNaturalReporter
        (primeDepthBVWoldXiCenteredRate rho)) := by
  apply frankensteinXiTwoOrientationUnitalScaleZeroDescendsAt_constructs_reporter rho
  exact (frankensteinXiTwoOrientationUnitalScaleZeroDescendsAt_iff_nearbyCycle rho).2 h

def EveryFrankensteinXiTwoOrientationUnitalScaleZeroDescends : Prop :=
  ∀ rho : XiDivisorSupport,
    FrankensteinXiTwoOrientationUnitalScaleZeroDescendsAt rho

/-- Global producer classification. -/
theorem everyFrankensteinXiTwoOrientationUnitalScaleZeroDescends_iff_riemannHypothesis :
    EveryFrankensteinXiTwoOrientationUnitalScaleZeroDescends ↔
      RiemannHypothesis := by
  rw [← everyFrankensteinSourceGammaNaturalSharedGhostDescends_iff_riemannHypothesis]
  unfold EveryFrankensteinXiTwoOrientationUnitalScaleZeroDescends
    EveryFrankensteinSourceGammaNaturalSharedGhostDescends
  apply forall_congr'
  intro rho
  rw [frankensteinXiTwoOrientationUnitalScaleZeroDescendsAt_iff,
    frankensteinSourceGammaNaturalSharedGhostDescendsAt_iff]

end

end RHTower
