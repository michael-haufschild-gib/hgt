import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetHalfLine
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSquareIndexPolarization

/-!
# Cofinal weighted top-row decay for the self-consistent Prouhet packet

The arithmetic Haar polarization leaves one integrated top row at each finite depth.  Every fixed
translate of that row tends to zero.  Since the phase-adapted packet has fixed finite support and
depends affinely on its endpoint, the self-consistent endpoint `tau_N -> 0` preserves this cofinal
decay.  No degree-uniform domination is needed.
-/

open Complex Real Polynomial MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

def xiCTaylorThetaTailCoreDyadicHaarIntegratedTopRowCurrent
    (d : ℕ) (z : ℂ) (k : ℕ) : ℝ :=
  ∫ p : ℝ × ℝ,
    xiCTaylorThetaTailCoreDyadicHaarRemainderKernel d z k p
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))

/-- The coefficient-weighted cofinal top rows.  The critical factor `q^j` is the same one that
normalizes the weighted Haar-prefix mass. -/
def phaseAdaptedProuhetWeightedTopRowCurrent
    (P : ℝ[X]) (q : ℝ) (N d : ℕ) (z : ℂ) : ℂ :=
  realPolynomialComplexCoefficientPairing P fun j =>
    ((((q ^ j) *
      xiCTaylorThetaTailCoreDyadicHaarIntegratedTopRowCurrent d z (N + j) : ℝ)) : ℂ)

theorem phaseAdaptedProuhetWeightedTopRowCurrent_tendsto_zero
    (m : ℕ) (u : ℂ) (q r : ℝ) (tau : ℕ → ℝ)
    (d : ℕ) (z : ℂ) (htau : Tendsto tau atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      phaseAdaptedProuhetWeightedTopRowCurrent
        (phaseAdaptedTwoEndpointProuhetPolynomial m u q r (tau N))
        q N d z) atTop (nhds 0) := by
  let B : ℕ → ℕ → ℂ := fun N j =>
    ((((q ^ j) *
      xiCTaylorThetaTailCoreDyadicHaarIntegratedTopRowCurrent d z (N + j) : ℝ)) : ℂ)
  have htop : Tendsto (fun k : ℕ =>
      xiCTaylorThetaTailCoreDyadicHaarIntegratedTopRowCurrent d z k)
      atTop (nhds 0) := by
    simpa only [xiCTaylorThetaTailCoreDyadicHaarIntegratedTopRowCurrent] using
      tendsto_integral_xiCTaylorThetaTailCoreDyadicHaarRemainderKernel_zero d z
  have hB : ∀ j : ℕ, Tendsto (fun N : ℕ => B N j) atTop (nhds 0) := by
    intro j
    have hshift := htop.comp (tendsto_add_atTop_nat j)
    have hcast : Tendsto (fun N : ℕ =>
        ((xiCTaylorThetaTailCoreDyadicHaarIntegratedTopRowCurrent
          d z (N + j) : ℝ) : ℂ)) atTop (nhds 0) := by
      simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp hshift
    have hmul := (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      (((q ^ j : ℝ) : ℂ))) atTop (nhds ((q ^ j : ℝ) : ℂ))).mul hcast
    simpa only [B, Complex.ofReal_mul, mul_zero] using hmul
  simpa only [phaseAdaptedProuhetWeightedTopRowCurrent, B] using
    phaseAdaptedProuhetCoefficientPairing_tendsto_of_endpoint_tendsto_zero
      m u q r tau B htau hB

/-- The actual fixed-half-line self-consistent endpoint preserves cofinal decay of the complete
finite weighted top row. -/
theorem phaseAdaptedCriticalSelfConsistentWeightedTopRowCurrent_tendsto_zero
    (m d : ℕ) (u : ℂ) (r : ℝ) {z : ℂ} (hz : z.im < 1 / 2)
    (R R' E E' : ℂ)
    (hBq : (phaseAdaptedProuhetBase m u).eval
      dyadicProuhetDecayCharacter ≠ 0)
    (hQ : (E' * (starRingEnd ℂ) E).im ≠ 0) :
    Tendsto (fun N : ℕ =>
      phaseAdaptedProuhetWeightedTopRowCurrent
        (phaseAdaptedTwoEndpointProuhetPolynomial m u
          dyadicProuhetDecayCharacter r
          (phaseAdaptedCriticalSelfConsistentEndpoint
            m N u r z R R' E E'))
        dyadicProuhetDecayCharacter N d z) atTop (nhds 0) := by
  apply phaseAdaptedProuhetWeightedTopRowCurrent_tendsto_zero
  exact phaseAdaptedCriticalSelfConsistentEndpoint_tendsto_zero
    m u r hz R R' E E' hBq hQ

end

end RHTower
