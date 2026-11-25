import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactLevels.CrossingHeights.PhysicalPeriods
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.GateLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.VisitIndices.Counting
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FirstCrossing

/-! # Sharp gate occupation on clocks through first positive-budget returns -/

open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels.CrossingHeights
open SharpOccupation EntrySensitivity.PrescribedCharacters VisitIndices
noncomputable section

private theorem clock_spacing {N d : ℕ} (H : selfAdjoint (Register N)) (e : (Fin N → Bool) ≃ Fin (d+1))
    (j : ℕ) (ε Δ L B : ℝ) (hl : 0<L)
    (hi : MaximallyProjectiveEnergy (H.2.isHermitian.eigenvalues ∘ e.symm))
    (hn : FreeAtStep (RHTower.zeroProjectiveFrequency (H.2.isHermitian.eigenvalues ∘ e.symm)) Δ)
    (hh : ∀ᶠ t : ℝ in atTop, L<visitFraction H j ε 0 t ∧ visitFraction H j ε 0 t<B) :
    ∃ p∈Icc L B, ∀ a : ℝ, let A := visitSet H j ε
      let hit (n : ℕ) := a+(n:ℝ)*Δ∈A
      Tendsto (fun M => (timeLaw a Δ M).real A) atTop (𝓝 p) ∧
        Tendsto (fun i : ℕ => (Nat.nth hit i:ℝ)/i) atTop (𝓝 p⁻¹) := by
  let E := H.2.isHermitian.eigenvalues ∘ e.symm
  let w := RHTower.zeroProjectiveFrequency E
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  have hE : MaximallyProjectiveEnergy E := hi
  let A := projectiveContinuousCircuitCaptureTarget e V j ε
  let T := visitSet H j ε
  have ha : finiteClockPhasePoint w ⁻¹' A=T := Set.ext fun t =>
    (physical_circuit_approximation_iff_spectral_capture e H j ε t).symm
  have hclosed : IsClosed A := isClosed_projectiveContinuousCircuitCaptureTarget e V j ε
  have hnull := PhaseBoundary.spectral_target_null e V E hE j ε
  have ht : Tendsto (fun t => visitFraction H j ε 0 t) atTop (𝓝 (volume.real A)) := by
    have hh := PhaseBoundary.uniform_phase_fraction w (RHTower.maximallyProjectiveEnergy_zeroProjectiveFrequency_independent E hE)
      A hclosed.measurableSet hnull (fun _ => 0)
    simpa only [ha,visitFraction,zero_add,sub_zero,T] using hh
  have hlo : L≤volume.real A := le_of_tendsto_of_tendsto tendsto_const_nhds ht (hh.mono fun _ h => h.1.le)
  have hhi : volume.real A≤B := le_of_tendsto_of_tendsto ht tendsto_const_nhds (hh.mono fun _ h => h.2.le)
  refine ⟨volume.real A,⟨hlo,hhi⟩,?_⟩
  intro a A' hit
  have h := free_step_fraction w a Δ hn A hclosed hnull
  rw [ha] at h
  have hm : MeasurableSet T := by
    rw [←ha]
    exact hclosed.measurableSet.preimage (finiteClockPhasePoint_continuous w).measurable
  exact ⟨h,(return_index_spacing (fun n : ℕ => a+(n:ℝ)*Δ) T hm (hl.trans_le hlo) h).2⟩


private theorem step_from_outside {N : ℕ} (H : selfAdjoint (Register N)) {s P : ℕ} (hs : s≤P)
    {ε σ : ℝ} (hε : 0<ε) (hfar : ε<orbitCircuitDistance H P σ) :
    ε<orbitCircuitDistance H s σ ∧ 0<PrecisionReturns.firstVisit H σ s ε-σ := by
  have hout : ε<orbitCircuitDistance H s σ := by
    by_contra! hh
    obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ s ε).mpr hh
    exact hfar.not_ge ((hasProjectiveCircuitApproximation_iff_infDist _ P ε).mp ⟨z,hz,C,hC.trans hs,he⟩)
  have hv := PrecisionReturns.firstVisit_isLeast H σ s hε
  refine ⟨hout,sub_pos.mpr (lt_of_le_of_ne hv.1.1 ?_)⟩
  intro he
  rw [he] at hout
  exact hout.not_ge ((hasProjectiveCircuitApproximation_iff_infDist _ s ε).mp hv.1.2)

/-- At all but countably many prescribed robust crossing heights, use
the actual first wait for any budget through P as the tick duration.
At error one tenth these clocks have the sharp continuous-time gate
occupation exponent and its reciprocal mean spacing in ticks. -/
theorem gaussian_unshifted_first_wait_sharp_spacing :
    ∃ B : Set ℝ, B.Countable ∧ ∀ r ∈ Ioc (1/10:ℝ) (1/8), r∉B →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ S : ℕ → ℕ, subcriticalBudget S →
        ∀ l b : ℝ, 0<l → l<physicalArc (1/10) → physicalArc (1/10)<b →
        ∀ᶠ k : ℕ in atTop, let N := k+3
          let D := 2^N
          let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
          let P := nearHilbertContinuousCircuitBudget N
          ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=r ∧ (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<r) ∧
            ∀ s≤P, let Δ := PrecisionReturns.firstVisit H σ s (1/10)-σ
              0<Δ ∧ ∀ j≤S N, ∃ p∈Icc (l^D) (b^D), ∀ a : ℝ,
                let A := visitSet H j (1/10)
                let hit (n : ℕ) := a+(n:ℝ)*Δ∈A
                Tendsto (fun M => (timeLaw a Δ M).real A) atTop (𝓝 p) ∧
                  Tendsto (fun i : ℕ => (Nat.nth hit i:ℝ)/i) atTop (𝓝 p⁻¹) := by
  obtain ⟨B,hB,hfree⟩ := gaussian_fixed_return_error_free_waits (1/10) (by norm_num)
  obtain ⟨c,hfinite⟩ := gaussian_finite_interval_occupation
  have htol : (1/10:ℝ)∈Ioo 0 (Real.sqrt 2) := ⟨by norm_num,
    by nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]⟩
  refine ⟨B,hB,?_⟩
  intro r hr hgood
  filter_upwards [hfree r hgood,hfinite,gaussian_physical_return_rates,
    gaussian_path_all_prefixes_maximally_projective] with ω hw hfin hrate hmax S hS l b hl hlx hxb
  filter_upwards [hfin,hrate S hS (1/10) htol l b hl hlx hxb] with k hocc hbound
  intro N D H P
  have hP : P≤D/(16*(N+1)) := by
    apply Nat.div_le_div_left <;> dsimp [P,D,nearHilbertContinuousCircuitBudget,N] <;> omega
  have hD : D≠0 := by dsimp [D]; positivity
  have hp := pow_lt_one₀ (by norm_num : (0:ℝ)≤3/8) (by norm_num) hD
  obtain ⟨σ,hσ,hc,hb,_⟩ := dated_crossing_of_occupation H (j:=P) (η:=r) (ε:=1/8)
    (p:=(3/8:ℝ)^D) (G:=(2:ℝ)^(D^c))
    ((by norm_num : (0:ℝ)<1/10).trans hr.1) hr.2 (pow_nonneg (by norm_num : (0:ℝ)≤3/8) D) hp
    (by positivity) (fun T hT => by simpa only [zero_add] using hocc P hP 0 T hT)
  obtain ⟨e,hf⟩ := hw k
  refine ⟨σ,hσ,hc,hb,?_⟩
  intro s hs Δ
  obtain ⟨hout,hpos⟩ := step_from_outside H hs (by norm_num : (0:ℝ)<1/10) (hr.1.trans_eq hc.symm)
  exact ⟨hpos,fun j hj => clock_spacing H e j (1/10) Δ (l^D) (b^D) (pow_pos hl D)
    ((hmax k).comp_equiv e.symm) (hf s P σ σ hout hc) (hbound j hj 0).1⟩

#print axioms gaussian_unshifted_first_wait_sharp_spacing
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels.CrossingHeights
