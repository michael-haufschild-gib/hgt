import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ShiftedWaits.SortedPhases
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.GaussianOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.SpectralTargets.NullBoundary
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.InitialDeadline

/-! # Gate-count occupation on clocks through the actual first physical dip -/

open Set Filter MeasureTheory Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
open PrescribedTimes SharpOccupation
noncomputable section

/-- Pulling a null-boundary phase target back to any sampled time sequence preserves its limiting frequency. -/
theorem sampled_fraction {d : ℕ} (w : Fin d → ℝ) (t : ℕ → ℝ)
    (ht : Tendsto (integerClockPrefixLaw (fun j => finiteClockPhasePoint w (t j))) atTop
      (𝓝 (finiteTorusHaarProbabilityMeasure (Fin d))))
    (A : Set (UnitAddTorus (Fin d))) (hm : MeasurableSet A) (hb : volume (frontier A)=0) :
    Tendsto (fun M => (integerClockPrefixLaw t M : Measure ℝ).real (finiteClockPhasePoint w ⁻¹' A))
      atTop (𝓝 (volume.real A)) := by
  have hb' : (finiteTorusHaarProbabilityMeasure (Fin d) : Measure _) (frontier A)=0 := by
    rwa [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
  have hz := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht hb'
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at hz
  apply ((ENNReal.tendsto_toReal (measure_ne_top volume A)).comp hz).congr
  intro M
  change ((integerClockPrefixLaw (fun j => finiteClockPhasePoint w (t j)) M : Measure _) A).toReal=_
  simp only [Measure.real,integerClockPrefixLaw,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply (measurable_of_finite _) hm,
    Measure.map_apply (measurable_of_finite _) (hm.preimage (finiteClockPhasePoint_continuous w).measurable)]
  rfl

/-- Shift the observation origin into the first excursion by a prescribed
amount in (0,1]. The first dip is still one step away. Every prescribed
injective integer subsequence of this clock reproduces continuous-time
gate occupation, for every translate, gate budget and observation error. -/
theorem gaussian_shifted_first_wait_gate_law (b : ℕ → ℕ → ℤ) (hb : ∀ k, Function.Injective (b k))
    (h : ℕ → ℝ) (hh : ∀ k, h k ∈ Ioc (0:ℝ) 1) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∀ s ≤ P/2, ∃ v > σ+h k, IsLeast {t | σ ≤ t ∧ t ∈ visitSet H s (1/10)} v ∧
          ∀ (l : ℕ) (ε : ℝ), ∃ p : ℝ,
            (∀ u : ℝ → ℝ, Tendsto (fun T => visitFraction H l ε (u T) (u T+T)) atTop (𝓝 p)) ∧
            ∀ a : ℝ, Tendsto (fun M => (integerClockPrefixLaw
              (fun i => a+(b k i:ℝ)*(v-(σ+h k))) M : Measure ℝ).real (visitSet H l ε)) atTop (𝓝 p) := by
  obtain ⟨_,hfirst⟩ := ReturnExcursions.gaussian_initial_crossing_short_return_tradeoff
  have hsamp := gaussian_shifted_phase_law b hb (fun k => -h k) (fun k => neg_ne_zero.mpr (hh k).1.ne')
  filter_upwards [hfirst,hsamp,gaussian_path_all_prefixes_maximally_projective] with ω hf hw hspec
  filter_upwards [hf] with k hk
  intro N H P
  let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let B := (2:ℝ)^(N-10*N.sqrt)
  have hB : 1≤B := one_le_pow₀ (by norm_num)
  obtain ⟨σ,hσ,he,hbefore,_,hvisit⟩ := hk
  have hpos : 0<σ := zero_lt_one.trans (hB.trans_lt hσ)
  have hgen : numberedGenerator (k+1) x=H.val := numberedGenerator_shell _
  have hd (t : ℝ) : pathGateDistance (k+1) P x t=orbitCircuitDistance H P t := by
    rw [pathGateDistance,hgen]; rfl
  have ho := crossingOrigin_eq_of_first hpos.le ((hd σ).trans he) (fun t ht => (hd t).trans_lt (hbefore t ht))
  obtain ⟨e,hclock⟩ := hw k
  refine ⟨σ,hpos,he,hbefore,?_⟩
  intro s hsp
  obtain ⟨v,hv,hmin,_,_⟩ := hvisit s hsp
  have hv' : σ+h k<v := (add_le_add_right ((hh k).2.trans hB) σ).trans_lt hv
  have hwait : crossingWait (k+1) P s x=v-σ := by
    change firstCircuitVisit (prefixGenerator (k+1) x) s (crossingOrigin (k+1) P (9/80) x) -
      crossingOrigin (k+1) P (9/80) x = v-σ
    rw [ho]
    apply congrArg (fun t : ℝ => t-σ)
    unfold firstCircuitVisit
    change sInf {t | σ≤t ∧ HasProjectiveCircuitApproximation _ _ _ (unitaryEvolution (numberedGenerator _ x) t)}=v
    rw [hgen]
    exact hmin.csInf_eq
  refine ⟨v,hv',hmin,?_⟩
  intro l ε
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let E := H.2.isHermitian.eigenvalues ∘ e.symm
  let w := RHTower.zeroProjectiveFrequency E
  let A := projectiveContinuousCircuitCaptureTarget e V l ε
  have hmax : MaximallyProjectiveEnergy E := (hspec k).comp_equiv e.symm
  have hm := (isClosed_projectiveContinuousCircuitCaptureTarget e V l ε).measurableSet
  have hn := PhaseBoundary.spectral_target_null e V E hmax l ε
  have ha : finiteClockPhasePoint w ⁻¹' A=visitSet H l ε :=
    Set.ext fun t => (physical_circuit_approximation_iff_spectral_capture e H l ε t).symm
  refine ⟨volume.real A,fun u => ?_,fun a => ?_⟩
  · have ht := PhaseBoundary.uniform_phase_fraction w
      (RHTower.maximallyProjectiveEnergy_zeroProjectiveFrequency_independent E hmax) A hm hn u
    simpa only [ha,visitFraction,add_sub_cancel_left] using ht
  · have ht := hclock P s
    change 0<crossingWait (k+1) P s x+ -h k → ∀ a : ℝ,
      Tendsto (integerClockPrefixLaw (fun i => finiteClockPhasePoint w
        (a+(b k i:ℝ)*(crossingWait (k+1) P s x+ -h k)))) atTop _ at ht
    rw [hwait,←sub_eq_add_neg,sub_sub] at ht
    rw [←ha]
    exact sampled_fraction w _ (ht (sub_pos.mpr hv') a) A hm hn

#print axioms gaussian_shifted_first_wait_gate_law
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
