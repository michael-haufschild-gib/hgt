import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.FirstCrossing
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.PhysicalSpeed.AllDates

/-! # Deterministic affordable lags and crossing separation in full-width turns -/

open Real MeasureTheory Filter Set
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
    dsimp only [g]
    linarith only [hc,twice_coefficientNorm_le_width n x]
  by_cases h : 0<g
  · refine ⟨g/2,half_pos h,hcap,?_⟩
    change g*|t|≤2*T at ht
    linarith only [ht]
  have hT : 0<T := by dsimp [T,travelProduct,localCrossingWidth]; positivity
  let R := T/(1+|t|)
  have hR : 0<R := div_pos hT (by positivity)
  refine ⟨R,hR,fun i => (hcap i).trans ((div_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) zero_le_two).trans hR.le),?_⟩
  have hsum : |t|≤1+|t| := le_add_of_nonneg_left (zero_le_one (α:=ℝ))
  exact (mul_le_mul_of_nonneg_left hsum hR.le).trans_eq
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

/-- On one frozen chain the deterministic separation applies to the
canonical crossing from the identity and to every ensuing first wait,
including the largest admissible return budget. -/
theorem gaussian_intrinsic_first_travel :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let x := fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
      travelProduct (k+3)/π<firstCrossingTurns n P x ∧
        ∀ s≤P/2, travelProduct (k+3)/π<firstWaitTurns n P s x := by
  filter_upwards [gaussian_first_crossing_local_width] with ω hf
  filter_upwards [hf,eventually_ge_atTop (128*128)] with k hk hsize
  intro n P x
  let u := pathPauliDisorderShell ω n
  let H := prefixGenerator n x
  let g := circuitHamiltonianSpectralWidth H
  let σ := crossingOrigin n P (9/80) x
  have hd (s : ℕ) (t : ℝ) : pathGateDistance n s x t =
      orbitCircuitDistance (⟨_,isSelfAdjoint_pathHamiltonian u⟩) s t := by
    unfold pathGateDistance orbitCircuitDistance
    rw [show numberedGenerator n x=pathHamiltonian u from numberedGenerator_shell u]
  obtain ⟨τ,hτ,he,hpre,_⟩ := hk
  have hτ₀ : 0≤τ := (show 0≤localCrossingWidth (k+3) by dsimp [localCrossingWidth]; positivity).trans hτ.le
  have hσ : σ=τ := crossingOrigin_eq_of_first hτ₀ ((hd P τ).trans he)
    (fun t ht => (hd P t).trans_lt (hpre t ht))
  have hfar : 9/80≤pathGateDistance n P x σ := by rw [hσ,hd,he]
  have hn : 128≤(n+2).sqrt := Nat.le_sqrt.mpr (by dsimp only [n]; omega)
  have hz := spectral_increment hn x 0 (by rw [abs_zero,mul_zero]; dsimp [travelProduct,localCrossingWidth]; positivity)
  have hstart := spectral_separation hn x hfar (P/2) le_rfl (hz.trans (by norm_num))
  have hσ₀ : 0≤σ := by rwa [hσ]
  rw [sub_zero,abs_of_nonneg hσ₀] at hstart
  refine ⟨?_,?_⟩
  · change travelProduct (k+3)/π<σ*g/(2*π)
    rw [mul_comm σ g]
    exact hstart
  intro s hs
  let Δ := crossingWait n P s x
  obtain ⟨t,ht,hcheap⟩ := (crossingWait_le_iff n P s x Δ).mp le_rfl
  have hgap := spectral_separation hn x hfar s hs hcheap
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr ht.1)] at hgap
  have htime : t-σ≤Δ := by linarith only [ht.2]
  change travelProduct (k+3)/π<Δ*g/(2*π)
  rw [mul_comm Δ g]
  exact hgap.trans_le (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htime
    (circuitHamiltonianSpectralWidth_nonneg H)) two_pi_pos.le)

#print axioms gaussian_intrinsic_first_travel
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
