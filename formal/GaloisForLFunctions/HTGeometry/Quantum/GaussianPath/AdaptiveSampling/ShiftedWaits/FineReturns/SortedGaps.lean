import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ShiftedWaits.RadialTransfer
import GaloisForLFunctions.HTGeometry.QubitPathRecurrenceCollisionCapstone
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw

/-! # Fine spectral recurrence on shifted first-wait clocks -/

open Set Filter MeasureTheory Metric Topology Real
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
open PrescribedTimes
noncomputable section

/-- The unit-time first simultaneous return has the full relative-phase
exponent almost everywhere on the entire coefficient space. -/
theorem discrete_gap_rate (k : ℕ) :
    ∀ᵐ x ∂volume, Tendsto (fun r : ℝ => log (firstHit (qubitPathDiscreteFrequency k x) r)/log (1/r))
      (𝓝[>] (0:ℝ)) (𝓝 ((2^(k+3)-1:ℕ):ℝ)) := by
  classical
  let hP := chainPauliFin_isHermitian (k+3)
  let U := simpleEnsembleLocus hP
  have hu : IsOpen U := isOpen_simpleEnsembleLocus hP
  choose r hr hsub using fun y : U => Metric.isOpen_iff.mp hu y.val y.property
  let B (y : U) := ball y.val (r y)
  have hcov : U ⊆ ⋃ y : U, B y := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (hr _)⟩
  have hl : IsLindelof U := isLindelof_iff_lindelofSpace.mpr inferInstance
  obtain ⟨s,hs,hsU⟩ := hl.elim_countable_subcover B (fun _ => isOpen_ball) hcov
  letI : Countable ↥s := hs.to_subtype
  have H (j : s) := qubitPath_everyChart_sameDraw_recurrenceCollisionLaw k
    (U:=B j.val) isOpen_ball isPreconnected_ball ⟨j.val.val,mem_ball_self (hr _)⟩ (hsub j.val)
  have Hs : ∀ᵐ x ∂volume, MaximallyProjectiveEnergy (qubitPathEnergy k x) :=
    ae_iff.mpr (volume_notMaximallyProjective_chain_eq_zero k)
  filter_upwards [Hs,ae_all_iff.mpr H] with x hx hchart
  have hxU : x∈U := hx.injective
  obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp (hsU hxU)
  exact (hchart ⟨j,hj⟩ hxj).2.1

/-- Positive rescaling multiplies every sorted anchored frequency by
the same factor. -/
theorem discrete_frequency_smul (k : ℕ) (x : PrefixIndex (k+1) → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    qubitPathDiscreteFrequency k (τ • x)=fun i => τ*qubitPathDiscreteFrequency k x i := by
  funext i
  change ((qubitPathSortedEnergy k (fun j => τ*x j) _)-qubitPathSortedEnergy k (fun j => τ*x j) _)/(2*π)=_
  simp only [qubitPathSortedEnergy,qubitPathDiscreteFrequency,anchoredGapMap,
    sortedEnsembleSpectrum_const_mul _ hτ]
  ring

/-- For every prefix and all choices of the two gate budgets, shifting
the first wait by a prescribed nonzero amount gives the generic D−1
exponent for simultaneous approximation of all relative energies. -/
theorem gaussian_shifted_gap_rate (h : ℕ → ℝ) (hh : ∀ k, h k≠0) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k j s : ℕ,
      let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      let τ := crossingWait (k+1) j s x+h k
      0<τ → Tendsto (fun r : ℝ => log (firstHit (fun i => τ*qubitPathDiscreteFrequency k x i) r)/log (1/r))
        (𝓝[>] (0:ℝ)) (𝓝 ((2^(k+3)-1:ℕ):ℝ)) := by
  apply ae_all_iff.mpr
  intro k
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro s
  let o := crossingWait (k+1) j s
  have hrad := radial_shift_volume o (measurable_crossingWait _ _ _) (fun _ hr => smul_crossingWait _ _ _ hr) (hh k)
  have hg : centredProductGaussian (PrefixIndex (k+1)) 1 ≪ volume :=
    productGaussian_absolutelyContinuous _ one_ne_zero _
  have ht := (gaussian_pauli_prefix_coordinates_law (k+1)).quasiMeasurePreserving.ae
    (hg.ae_le (hrad.ae (discrete_gap_rate k)))
  filter_upwards [ht] with ω hω
  intro x τ hτ
  rw [←discrete_frequency_smul k x hτ]
  exact hω

#print axioms gaussian_shifted_gap_rate
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
