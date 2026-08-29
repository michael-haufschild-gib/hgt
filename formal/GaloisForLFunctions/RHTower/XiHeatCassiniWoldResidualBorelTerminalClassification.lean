import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelSubhalfClassification

/-!
# Exact strict-sector classification of the positive Borel terminal

Finite Abel renormalization leaves the explicit terminal

`|R_N| * exp (y * h_N)`.

The corpus RH-to-Wold estimate makes this terminal vanish at every strict sub-half height.  The
converse is sharper than a formal restatement: terminal decay at a height `c` gives an eventual
exponential residual envelope of rate `c`, which makes every raw edge below `c` absolutely
summable.  Choosing `c` strictly between an arbitrary height and `1/2` opens the whole critical
source strip, where the existing Route-T ODE endpoint forces RH.

Thus, under critical mesh energy, separately removing the terminal throughout the positive Borel
sector is already equivalent to RH.  A noncircular lateral construction must regularize the joint
finite current without first proving independent terminal disappearance.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Under critical mesh energy, vanishing of the exact positive-ray Borel terminal throughout
the strict sub-half sector is equivalent to RH. -/
theorem riemannHypothesis_iff_subhalf_woldResidualBorelTerminalWeight
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    RiemannHypothesis ↔
      ∀ y : ℝ, 0 < y → y < 1 / 2 →
        Tendsto (fun N : ℕ ↦
          |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
            Real.exp (y * xiMassNthPrimeLogHeight N)) atTop (𝓝 0) := by
  constructor
  · intro hRH y hy0 hyHalf
    exact tendsto_woldResidualBorelTerminalWeight_zero_of_riemannHypothesis
      hRH hy0.le hyHalf
  · intro hterminal
    apply riemannHypothesis_of_subhalf_residual_absoluteConvergence_criticalEnergy
      ?_ hcritical
    intro a ha0 haHalf
    let c : ℝ := (a + 1 / 2) / 2
    have hac : a < c := by dsimp only [c]; linarith
    have hc0 : 0 < c := by dsimp only [c]; linarith
    have hcHalf : c < 1 / 2 := by dsimp only [c]; linarith
    have ht := hterminal c hc0 hcHalf
    have hsmall : ∀ᶠ N : ℕ in atTop,
        |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
            Real.exp (c * xiMassNthPrimeLogHeight N) < 1 :=
      ht (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have hrate : ∀ᶠ N : ℕ in atTop,
        |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
          1 * Real.exp (-c * xiMassNthPrimeLogHeight N) := by
      filter_upwards [hsmall] with N hN
      calc
        |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| =
            (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
              Real.exp (c * xiMassNthPrimeLogHeight N)) *
                Real.exp (-c * xiMassNthPrimeLogHeight N) := by
          rw [mul_assoc, ← Real.exp_add]
          ring_nf
          simp
        _ ≤ 1 * Real.exp (-c * xiMassNthPrimeLogHeight N) :=
          mul_le_mul_of_nonneg_right hN.le (Real.exp_nonneg _)
    exact summable_norm_residualAtom_mul_I_of_exp_height_rate
      ha0 (by linarith) hac hrate

/-- Exact finite-current form of the strict-sector terminal classification.  The statement uses
the actual positive-ray Borel integral and finite Wold--mesh--holonomy current, not an auxiliary
coefficient model. -/
theorem riemannHypothesis_iff_subhalf_woldResidualBorelFiniteLanding
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    RiemannHypothesis ↔
      ∀ x y : ℝ, 0 < y → y < 1 / 2 →
        Tendsto (fun N : ℕ ↦
          xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x y N -
            ∫ t : ℝ in Ioi 0,
              ∑ n ∈ Finset.range N,
                xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n t)
          atTop (𝓝 0) := by
  constructor
  · intro hRH x y hy0 hyHalf
    exact
      tendsto_woldResidualBorelFiniteRenormalized_sub_raw_zero_of_riemannHypothesis
        hRH x hy0.le hyHalf
  · intro hlanding
    apply
      (riemannHypothesis_iff_subhalf_woldResidualBorelTerminalWeight
        hcritical).2
    intro y hy0 hyHalf
    have h := hlanding 0 y hy0 hyHalf
    rw [tendsto_xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_sub_edgeIntegral_zero_iff]
      at h
    simpa only [mul_comm] using h

end

end RHTower
