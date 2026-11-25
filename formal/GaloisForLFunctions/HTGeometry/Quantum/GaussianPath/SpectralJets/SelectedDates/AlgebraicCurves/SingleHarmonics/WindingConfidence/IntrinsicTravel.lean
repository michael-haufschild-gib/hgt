import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.WidthFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.PhysicalSpeed.AllDates

/-! # Deterministic affordable lags and crossing separation in full-width turns -/

open Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
open PrescribedTimes WeakBonds LocalPatches LocalPatches.PhysicalSpeed
noncomputable section

private theorem cap_for_lag {n : ℕ} (x : PrefixIndex n→ℝ) (t : ℝ)
    (ht : circuitHamiltonianSpectralWidth (prefixGenerator n x)*|t|≤2*travelProduct (n+2)) :
    ∃ R>(0:ℝ), (∀ i, |x i|≤R) ∧ R*|t|≤travelProduct (n+2) := by
  let g := circuitHamiltonianSpectralWidth (prefixGenerator n x)
  let T := travelProduct (n+2)
  have hcap (i) : |x i| ≤ g/2 := by
    have hc := abs_coord_le_norm (WithLp.toLp 2 x) i
    change |x i|≤coefficientNorm x at hc
    linarith only [hc,twice_coefficientNorm_le_width n x]
  by_cases h : 0<g
  · refine ⟨g/2,half_pos h,hcap,?_⟩
    change g*|t|≤2*T at ht
    linarith only [ht]
  have hT : 0<T := by dsimp [T,travelProduct,localCrossingWidth]; positivity
  let R := T/(1+|t|)
  have hR : 0<R := div_pos hT (by positivity)
  refine ⟨R,hR,fun i => (hcap i).trans ((div_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) zero_le_two).trans hR.le),?_⟩
  exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (b:=|t|) zero_le_one) hR.le).trans_eq
    (div_mul_cancel₀ _ (show 1+|t|≠0 by positivity))

/-- The half-budget simulator covers every lag of at most
travelProduct/π spectral turns on every path, without any bound on
its couplings or any condition on its spectrum. -/
theorem spectral_increment {n : ℕ} (hn : 128≤(n+2).sqrt) (x : PrefixIndex n→ℝ) (t : ℝ)
    (ht : circuitHamiltonianSpectralWidth (prefixGenerator n x)*|t|≤2*travelProduct (n+2)) :
    pathGateDistance n (nearHilbertContinuousCircuitBudget (n+2)/2) x t≤1/100 := by
  obtain ⟨R,hR,hcap,hshort⟩ := cap_for_lag x t ht
  exact capped_increment x t hn hR hcap hshort

/-- Every robust crossing, however selected, is separated from every
affordable visit by more than travelProduct/π full-width turns. -/
theorem spectral_separation {n : ℕ} (hn : 128≤(n+2).sqrt) (x : PrefixIndex n→ℝ) :
    let P := nearHilbertContinuousCircuitBudget (n+2)
    ∀ {σ t : ℝ}, 9/80≤pathGateDistance n P x σ →
      ∀ s ≤ P/2, pathGateDistance n s x t≤1/10 →
        travelProduct (n+2)/π<circuitHamiltonianSpectralWidth (prefixGenerator n x)*|σ-t|/(2*π) := by
  intro P σ t hσ s hs hfit
  apply (div_lt_div_iff₀ pi_pos two_pi_pos).mpr
  have hlarge : 2*travelProduct (n+2)<circuitHamiltonianSpectralWidth (prefixGenerator n x)*|σ-t| := by
    by_contra! hshort
    obtain ⟨R,hR,hcap,ht⟩ := cap_for_lag x (σ-t) hshort
    exact (all_dates_travel x hn hR hcap (by norm_num : (1/10:ℝ)+1/100<9/80) hσ hs hfit).not_ge ht
  linarith only [mul_lt_mul_of_pos_right hlarge pi_pos]

#print axioms spectral_increment
#print axioms spectral_separation
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
