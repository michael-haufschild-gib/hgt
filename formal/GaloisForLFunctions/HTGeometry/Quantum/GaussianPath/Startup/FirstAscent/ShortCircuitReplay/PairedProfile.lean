import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ShortCircuitReplay.BoundedHorizon
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralArcs.PhysicalMinimax

/-! # Best simultaneous circuit error on a bounded physical lag interval -/

open Real Set Filter MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
open SpectralArcs EnergyMesh ThermodynamicEdges
noncomputable section

private theorem empty_origin {N : ℕ} (H : selfAdjoint (Register N)) : orbitCircuitDistance H 0 0 = 0 := by
  have h := orbitCircuitDistance_zeroGate_eq_spectralArc H
    ⟨0,by simpa only [abs_zero,zero_mul] using pi_pos.le⟩
  simpa only [abs_zero,zero_mul,sin_zero,mul_zero] using h

private theorem clipped_half {x : ℝ} (hx : 0≤x) :
    clippedChord x ∈ Icc (0:ℝ) 2 ∧ halfChord (clippedChord x)=2*sin (min x (2*π)/8) := by
  let y := min x (2*π)/4
  have h₀ : 0≤y := div_nonneg (le_min hx two_pi_pos.le) (by norm_num)
  have hh : y≤π/2 := by dsimp only [y]; linarith only [min_le_right x (2*π)]
  have hsin := sin_nonneg_of_nonneg_of_le_pi h₀ (by linarith only [hh,pi_pos])
  refine ⟨⟨mul_nonneg zero_le_two hsin,by change 2*sin y≤2; linarith only [sin_le_one y]⟩,?_⟩
  change 2*sin (arcsin (2*sin y/2)/2)=_
  rw [show 2*sin y/2=sin y by ring,arcsin_sin (by linarith only [h₀,pi_pos]) hh]
  dsimp only [y]; congr 2; ring

/-- Minimizing the worse of two endpoint errors over future origins gives
the bisected limiting chord, uniformly in all bounded nonnegative lags.
Both endpoints may have draw-dependent sublinear gate budgets. -/
theorem gaussian_paired_profile :
    ∃ w : ℝ, 0<w ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      let N := fun n : ℕ => ((n+2:ℕ):ℝ)
      let H := fun n => shellOperator (pathPauliDisorderShell ω n)
      Tendsto (fun n => physicalWidth ω n/N n) atTop (𝓝 w) ∧
      ∀ i j : ℕ→ℕ, Tendsto (fun n => ((i n+j n:ℕ):ℝ)/N n) atTop (𝓝 0) →
        ∀ T η : ℝ, 0<η → ∀ᶠ n in atTop, ∀ a : ℝ, ∀ t∈Icc (0:ℝ) T,
          |pairError (H n) (i n) (j n) a t-2*sin (min (N n*t*w) (2*π)/8)| ≤ η := by
  obtain ⟨w,hw,hg⟩ := gaussian_bounded_gate_replay
  refine ⟨w,hw,?_⟩
  filter_upwards [hg,gaussian_path_all_prefixes_maximally_projective] with ω hh hmax
  intro N H
  refine ⟨hh.1,?_⟩
  intro i j hs T η hη
  have hc : Continuous halfChord := by unfold halfChord; fun_prop
  obtain ⟨δ,hδ,hu⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (s:=Icc (0:ℝ) 2) hc.continuousOn) η hη
  let z := fun _ : ℕ => (0:ℕ)
  let s := fun n => i n+j n
  have hz : Tendsto (fun n => (z n:ℝ)/N n) atTop (𝓝 0) := by simp only [z,Nat.cast_zero,zero_div]; exact tendsto_const_nhds
  have hz₀ (k : ℕ→ℕ) : ∀ᶠ n in atTop, z n ≤ k n := .of_forall fun _ => Nat.zero_le _
  filter_upwards [hh.2 z s (hz₀ s) hs T δ hδ,hh.2 z z (hz₀ z) hz T δ hδ,eventually_ge_atTop 1] with n hsum hzero hn
  intro a t ht
  let x := N n*t*w
  have hx : 0≤x := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ht.1) hw.le
  have hch := clipped_half hx
  have control (k : ℕ) (h : |orbitCircuitDistance (H n) k t-clippedChord x| ≤ δ) :
      |halfChord (orbitCircuitDistance (H n) k t)-halfChord (clippedChord x)| ≤ η := by
    have hmem : orbitCircuitDistance (H n) k t∈Icc (0:ℝ) 2 := ⟨Metric.infDist_nonneg,
      (budget_antitone _ (Nat.zero_le _) _).trans (orbitCircuitDistance_zeroGate_lt_two _ _).le⟩
    exact hu _ hmem _ hch.1 h
  have h₁ := control (s n) (by simpa only [z,empty_origin,zero_add] using hsum 0 t ht)
  have h₂ := control 0 (by simpa only [z,empty_origin,zero_add] using hzero 0 t ht)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  let S := k+3
  have hp : 0<(2:ℕ)^S := by positivity
  let e := (qubitConfigFin S).trans (finCongr (show 2^S=2^S-1+1 by omega))
  have hbounds := joint_bounds e (H (k+1)) (hmax k) (i (k+1)) (j (k+1)) a t
  rw [←hch.2]
  exact abs_le.mpr ⟨by linarith only [(abs_le.mp h₁).1,hbounds.1],by linarith only [(abs_le.mp h₂).2,hbounds.2]⟩

#print axioms gaussian_paired_profile
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
