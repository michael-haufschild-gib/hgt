import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralArcs.CoordinateHits
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralArcs.PairedFits

/-! # Simultaneous empty visits at a prescribed time difference -/

open Set Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralArcs
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
private def phase (u : ℝ) : ℂ := Complex.exp ((u:ℂ)*Complex.I)
private theorem norm_phase (u : ℝ) : ‖phase u‖=1 := by simp [phase,Complex.norm_exp]
private theorem phase_add (x y : ℝ) : phase (x+y)=phase x*phase y := by
  rw [phase,Complex.ofReal_add,add_mul,Complex.exp_add]; rfl
private theorem physical_phase {I : Type*} (E : I → ℝ) (i : I) (t : ℝ) :
    anchorPhase E i t=phase (-(t*E i)) := by unfold anchorPhase phase; congr 1; push_cast; ring

private theorem scalar_bound {n : ℕ} (H : selfAdjoint (Reg n)) (t : ℝ) {z : ℂ} (hz : ‖z‖=1)
    {e : ℝ} (he : ∀ j, ‖anchorPhase H.2.isHermitian.eigenvalues j t-z‖≤e) :
    orbitCircuitDistance H 0 t ≤ e := by
  apply (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp
  refine ⟨z,hz,TwoQubitCircuit.one _,le_rfl,?_⟩
  rw [TwoQubitCircuit.one_eval]
  change ‖unitaryEvolution H.val t-z • (1 : Reg n)‖≤e
  rw [norm_evolution_sub_scalar,pi_norm_le_iff_of_nonempty]
  exact he

/-- At every tolerance strictly above the half-arc chord, pairs of physical
empty visits separated by the given lag occur with bounded gaps. -/
theorem syndetic_pair_above_half_arc {n d : ℕ} (e : (Fin n→Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n)) (hm : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (t ε : ℝ) (he : 2*sin (orbitSpectralEnclosingArcLength H t/8)<ε) :
    ∃ G : ℝ, 0≤G ∧ ∀ a : ℝ, ∃ v∈Icc a (a+G),
      orbitCircuitDistance H 0 v < ε ∧ orbitCircuitDistance H 0 (v+t) < ε := by
  let E := H.2.isHermitian.eigenvalues
  let θ := fun j => -(t*E j)
  let L := spectralEnclosingArcLength θ
  let r := 2*sin (L/8)
  have hL := spectralEnclosingArcLength_nonneg θ
  have hL' := spectralEnclosingArcLength_lt_two_pi θ
  have hr : r<ε := he
  let η := (ε-r)/2
  have hη : 0<η := half_pos (sub_pos.mpr hr)
  obtain ⟨ψ,c,hc⟩ := split_arc θ (r:=1/2) (by constructor <;> norm_num)
  have chord {x y : ℝ} (h : circDist x y ≤ L/4) : ‖phase x-phase y‖ ≤ r := by
    rw [phase,phase,norm_expI_sub_eq_sin_circDist]
    apply mul_le_mul_of_nonneg_left _ zero_le_two
    have hl : 0 ≤ circDist x y := circDist_nonneg .. 
    have hu : L < 2*π := hL'
    have hz : 0 ≤ L := hL
    apply monotoneOn_sin <;> first | exact ⟨by linarith only [hl,pi_pos],by linarith only [h,hu,pi_pos]⟩ |
      exact ⟨by linarith only [hz,pi_pos],by linarith only [hu,pi_pos]⟩ | linarith only [h]
  have hψ (j) := chord (x:=ψ j) (y:=0) (by linarith only [(hc j).1])
  have hχ (j) := chord (x:=ψ j+θ j) (y:=c) (by linarith only [(hc j).2])
  obtain ⟨G,hG,hh⟩ := coordinate_hits e H hm (fun j => phase (ψ j)) (fun j => norm_phase _) hη
  refine ⟨G,hG,fun a => ?_⟩
  obtain ⟨v,hv,z,hz,hv'⟩ := hh a
  have he' : η+r<ε := by dsimp only [η]; linarith only [hr]
  refine ⟨v,hv,(scalar_bound H v hz fun j => ?_).trans_lt he',?_⟩
  · have h₁ := hψ j
    rw [show phase 0=1 by simp [phase]] at h₁
    have h₂ := norm_sub_le_norm_sub_add_norm_sub (anchorPhase E j v) (z*phase (ψ j)) z
    have heq : z*phase (ψ j)-z=z*(phase (ψ j)-1) := by ring
    rw [heq,norm_mul,hz,one_mul] at h₂
    exact h₂.trans (add_le_add (hv' j).le h₁)
  · apply (scalar_bound H (v+t) (z:=z*phase c) (by rw [norm_mul,hz,norm_phase,mul_one]) _).trans_lt he'
    intro j
    let p := phase (θ j)
    have hp : ‖p‖=1 := norm_phase _
    have hx : anchorPhase E j (v+t)=anchorPhase E j v*p := by
      rw [physical_phase,physical_phase,add_mul,neg_add,phase_add]
    have hdiff : (anchorPhase E j v)*p-z*phase c=
        (anchorPhase E j v-z*phase (ψ j))*p+z*(phase (ψ j+θ j)-phase c) := by
      rw [phase_add]; dsimp only [p]; ring
    rw [hx,hdiff]
    exact (norm_add_le ..).trans (by rw [norm_mul,norm_mul,hz,hp,mul_one,one_mul]; exact add_le_add (hv' j).le (hχ j))

#print axioms syndetic_pair_above_half_arc
end
end GaloisForLFunctions.HTGeometry.SpectralArcs
