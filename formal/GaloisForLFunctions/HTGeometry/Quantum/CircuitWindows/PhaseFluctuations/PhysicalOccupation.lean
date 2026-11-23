import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseFluctuations.MaximumMean
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.GaussianOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.GaussianMaximumQuantiles

/-! # Fluctuations of physical gate counts about their long-time mean -/
open Matrix MeasureTheory Set Filter ProbabilityTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseFluctuations
open DiagonalSynthesis SharpOccupation
noncomputable section
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

private theorem haar_tails {n d : ℕ} (hn : 2 ≤ n) (e : (Fin n → Bool) ≃ Fin (d+1))
    (V : unitaryGroup (Fin n → Bool) ℂ) {ε u : ℝ} (hε : 0≤ε) (hu : 0≤u) (s : ℕ) :
    let p := volume.real (projectiveContinuousCircuitCaptureTarget e V s ε)
    let m := meanCost hn e V hε
    let q := exp (-u^2/(2*((d:ℝ)*((eigenphaseCost n:ℝ)/2)^2)))
    ((s:ℝ)+u ≤ m → p ≤ q) ∧ (m+u ≤ (s:ℝ)+1 → 1-p ≤ q) := by
  intro p m q
  let A := projectiveContinuousCircuitCaptureTarget e V s ε
  let f := phaseCost hn e V hε
  have hmem (x) : x ∈ A ↔ f x ≤ s :=
    (mem_projectiveContinuousCircuitCaptureTarget_iff e V s ε x).trans (phaseCost_le hn e V hε x).symm
  have h := phaseCost_moment hn e V hε
  constructor
  · intro hlo
    have hsub : A ⊆ {x | u ≤ -((f x:ℝ)-m)} := by
      intro x hx
      have hh : (f x:ℝ) ≤ s := Nat.cast_le.mpr ((hmem x).mp hx)
      change u ≤ -((f x:ℝ)-m)
      linarith only [hh,hlo]
    apply (measureReal_mono (μ:=volume) hsub (measure_ne_top _ _)).trans
    simpa only [Pi.neg_apply,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_div,
      NNReal.coe_natCast,NNReal.coe_ofNat] using h.neg.measure_ge_le hu
  · intro hhi
    have hprob : volume.real Aᶜ=1-p := by
      rw [measureReal_compl (isClosed_projectiveContinuousCircuitCaptureTarget e V s ε).measurableSet,probReal_univ]
    have hsub : Aᶜ ⊆ {x | u ≤ (f x:ℝ)-m} := by
      intro x hx
      have hh : (s:ℝ)+1 ≤ (f x:ℝ) := by
        exact_mod_cast Nat.lt_of_not_ge (fun h => hx ((hmem x).mpr h))
      change u ≤ (f x:ℝ)-m
      linarith only [hh,hhi]
    rw [←hprob]
    apply (measureReal_mono (μ:=volume) hsub (measure_ne_top _ _)).trans
    simpa only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_ofNat] using h.measure_ge_le hu

/-- On every typical frozen prefix and at every nonnegative error, gate
counts concentrate about the Haar mean on its physical eigenbasis. The
limiting fractions are uniform in the observation origin. -/
theorem gaussian_gate_count_fluctuations :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let H : selfAdjoint (DiagonalSynthesis.Register N) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
      let V := hermitianEigenbasisUnitary H.2.isHermitian
      ∀ (ε : ℝ) (hε : 0 ≤ ε) (s : ℕ), ∃ p : ℝ,
        (∀ a : ℝ → ℝ, Tendsto (fun T => visitFraction H s ε (a T) (a T+T)) atTop (𝓝 p)) ∧
        ∀ u : ℝ, 0≤u →
          let m := meanCost (by dsimp [N]; omega) e V hε
          let q := exp (-u^2/(2*(((2^N-1:ℕ):ℝ)*((eigenphaseCost N:ℝ)/2)^2)))
          ((s:ℝ)+u ≤ m → p ≤ q) ∧ (m+u ≤ (s:ℝ)+1 → 1-p ≤ q) := by
  filter_upwards [PhaseBoundary.gaussian_uniform_affordable_fraction] with ω hw k
  intro N H e V ε hε s
  refine ⟨_,fun a => hw k s ε a,?_⟩
  exact fun u hu => haar_tails (by dsimp [N]; omega) e V hε hu s

#print axioms gaussian_gate_count_fluctuations

/-- At error one tenth, budgets below half the actual one-fifth-error
maximum minus u have an exponentially bounded lower tail. -/
theorem gaussian_half_maximum_tail :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let H : selfAdjoint (DiagonalSynthesis.Register N) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∃ m > nearHilbertContinuousCircuitBudget N, IsRecurrentOrbitCircuitMaximumAt H (1/5) m ∧
        ∀ s : ℕ, ∃ p : ℝ,
          (∀ a : ℝ → ℝ, Tendsto (fun T => visitFraction H s (1/10) (a T) (a T+T)) atTop (𝓝 p)) ∧
          ∀ u : ℝ, 0≤u → (s:ℝ)+u ≤ (m:ℝ)/2 →
            p ≤ exp (-u^2/(2*(((2^N-1:ℕ):ℝ)*((eigenphaseCost N:ℝ)/2)^2))) := by
  filter_upwards [gaussian_gate_count_fluctuations,gaussian_pauli_prefix_maximum_and_occupation_quantiles]
    with ω hf hmax
  filter_upwards [hmax] with k hk
  intro N H
  obtain ⟨m,hm,hr,_⟩ := hk (1/5) (by constructor <;> norm_num)
  refine ⟨m,hm,hr,?_⟩
  intro s
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  have hn : 2 ≤ N := by dsimp [N]; omega
  have hε : (0:ℝ)≤1/10 := by norm_num
  have hμ : (m:ℝ) ≤ meanCost hn e V hε+meanCost hn e V hε :=
    orbitMaximum_le_sum_means hn e H hε hε (by
      rw [show (1/10:ℝ)+1/10=1/5 by norm_num]
      exact hr)
  obtain ⟨p,hp,hbound⟩ := hf k (1/10) hε s
  refine ⟨p,hp,fun u hu h => (hbound u hu).1 ?_⟩
  change (s:ℝ)+u ≤ meanCost hn e V hε
  linarith only [h,hμ]

#print axioms gaussian_half_maximum_tail
end
end GaloisForLFunctions.HTGeometry.PhaseFluctuations
