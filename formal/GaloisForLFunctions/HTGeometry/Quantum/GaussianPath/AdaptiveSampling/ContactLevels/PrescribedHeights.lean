import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactLevels.SelectedCouplings

/-! # Full discrete recurrence exponent on first-visit clocks at prescribed errors -/

open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels
open AccuracyScales.MaximumIntervals PrescribedTimes ShiftedWaits PrecisionReturns ResonantReturns
noncomputable section

private abbrev Point (k : ℕ) := PrefixIndex (k+1) → ℝ

private theorem prescribed_offsets (b : ∀ k : ℕ, ℕ → Point k → ℝ) (hb : ∀ k l, Measurable (b k l)) :
    ∀ᵐ e : ℝ ∂volume, ∀ᵐ ω ∂pathPauliDisorderLaw, 0 < e → ∀ (k l s : ℕ) (a : ℝ),
      let H := chainGenerator ω k
      let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      e < orbitCircuitDistance H s a → let τ := firstVisit H a s e-b k l x
        0 < τ → ∀ j : ℕ, j+1 < k+3 →
          Tendsto (fun ε => log (firstIndex H τ j ε)/log (1/ε))
            (𝓝[>] (0:ℝ)) (𝓝 ((2^(k+3)-1:ℕ):ℝ)) := by
  let Z (k : ℕ) := {x : Point k | ¬ Tendsto
    (fun r => log (firstHit (qubitPathDiscreteFrequency k x) r)/log (1/r)) (𝓝[>] (0:ℝ)) (𝓝 ((2^(k+3)-1:ℕ):ℝ))}
  have hZ (k : ℕ) : volume (Z k)=0 := ae_iff.mp (discrete_gap_rate k)
  have hc (k l s : ℕ) := selected_couplings_avoid (k+1) s (b k l) (hb k l) (Z k) (hZ k)
  filter_upwards [ae_all_iff.mpr fun k => ae_all_iff.mpr fun l => ae_all_iff.mpr (hc k l)] with e he
  have hh (k l s : ℕ) := (gaussian_pauli_prefix_coordinates_law (k+1)).quasiMeasurePreserving.ae
    ((show centredProductGaussian (PrefixIndex (k+1)) 1 ≪ volume from
      productGaussian_absolutelyContinuous _ one_ne_zero _).ae_le (he k l s))
  filter_upwards [ae_all_iff.mpr fun k => ae_all_iff.mpr fun l => ae_all_iff.mpr (hh k l),
    gaussian_sorted_index_comparison] with ω hω hcmp hpos k l s a
  intro H x hout τ hτ
  have hg : prefixGenerator (k+1) x=H := Subtype.ext (numberedGenerator_shell (pathPauliDisorderShell ω (k+1)))
  have h := hω k l s hpos a
  change e < orbitCircuitDistance (prefixGenerator (k+1) x) s a →
    (firstVisit (prefixGenerator (k+1) x) a s e-b k l x) • x ∉ Z k at h
  rw [hg] at h
  have hv : Tendsto (fun r => log (firstHit (qubitPathDiscreteFrequency k (τ • x)) r)/log (1/r))
      (𝓝[>] (0:ℝ)) (𝓝 ((2^(k+3)-1:ℕ):ℝ)) := by
    by_contra hn
    exact h hout hn
  rw [discrete_frequency_smul k x hτ] at hv
  exact hcmp k τ _ hv

/-- Choose the coarse tolerance before the Gaussian draw. At almost
every such tolerance, every first visit from outside, timed from zero
or from an actual robust crossing, gives the full D−1 exponent for the
first positive fine-precision tick at every disconnected budget. -/
theorem gaussian_prescribed_first_visit_index :
    ∀ᵐ e : ℝ ∂volume, ∀ᵐ ω ∂pathPauliDisorderLaw, 0 < e → ∀ (k l s : ℕ) (a : ℝ),
      let H := chainGenerator ω k
      let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      e < orbitCircuitDistance H s a → let v := firstVisit H a s e
        ∀ o ∈ ({0,crossingOrigin (k+1) l (9/80) x} : Set ℝ), o < v →
          ∀ j : ℕ, j+1 < k+3 → Tendsto (fun ε => log (firstIndex H (v-o) j ε)/log (1/ε))
            (𝓝[>] (0:ℝ)) (𝓝 ((2^(k+3)-1:ℕ):ℝ)) := by
  have hz := prescribed_offsets (fun _ _ _ => 0) (fun _ _ => measurable_const)
  have hc := prescribed_offsets (fun k l => crossingOrigin (k+1) l (9/80))
    (fun k l => measurable_crossingOrigin (k+1) l (9/80))
  filter_upwards [hz,hc] with e he hcross
  filter_upwards [he,hcross] with ω h₀ hσ hp k l s a
  intro H x hout v o ho hv j hj
  rcases ho with h | h
  · subst o
    exact h₀ hp k l s a hout (sub_pos.mpr hv) j hj
  · have heq : o=crossingOrigin (k+1) l (9/80) x := h
    subst o
    exact hσ hp k l s a hout (sub_pos.mpr hv) j hj

#print axioms gaussian_prescribed_first_visit_index
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels
