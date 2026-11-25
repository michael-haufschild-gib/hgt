import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ResonantOccupation.ClockBasis
import GaloisForLFunctions.HTGeometry.PhaseOrbitClosureSubtorus
import GaloisForLFunctions.HTGeometry.SingleOrbitPlateauWindow

/-! # Phase parametrizations on the residue classes of a sampled spectrum -/

open Finset Real
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ResonantOccupation
noncomputable section

/-- On each residue class, the sampled phase is a translate of an
integer torus image with fully equidistributed input frequencies. -/
theorem exists_residue_phases {I : Type} [Fintype I] (w : I → ℝ) (a τ : ℝ) :
    ∃ (L : ℕ) (_ : 0<L) (k : ℕ) (γ : Fin k → ℝ) (M : I → Fin k → ℤ),
      FreeAtStep γ 1 ∧ ∀ b n : ℕ, finiteClockPhasePoint w (a+((L*n+b:ℕ):ℝ)*τ) =
        finiteClockPhasePoint w (a+(b:ℝ)*τ)+torusIntegerHom M (finiteClockPhasePoint γ n) := by
  classical
  obtain ⟨L,hL,k,γ,M,h,hf,hr⟩ := exists_free_clock_basis (fun i => τ*w i)
  refine ⟨L,hL,k,γ,M,hf,fun b n => ?_⟩
  let u (i : I) := ∑ j, (M i j:ℝ)*γ j
  rw [←finiteClockPhasePoint_eq_torusIntegerHom u γ M (fun _ => rfl)]
  have ht : a+((L*n+b:ℕ):ℝ)*τ=(a+(b:ℝ)*τ)+(n:ℝ)*((L:ℝ)*τ) := by push_cast; ring
  rw [ht,finiteClockPhasePoint_add]
  congr 1
  funext i
  have hj := hr i
  change (L:ℝ)*(τ*w i)=(h i:ℝ)*(2*π)+u i at hj
  have hx : ((n:ℝ)*((L:ℝ)*τ))*w i/(2*π) = (((n:ℤ)*h i:ℤ):ℝ)+(n:ℝ)*u i/(2*π) := by
    rw [show ((n:ℝ)*((L:ℝ)*τ))*w i=(n:ℝ)*((L:ℝ)*(τ*w i)) by ring,hj]
    push_cast
    field_simp [pi_ne_zero]
  change ((((n:ℝ)*((L:ℝ)*τ))*w i/(2*π):ℝ):UnitAddCircle) = _
  have hz (m : ℤ) : ((m:ℝ):UnitAddCircle)=0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨m,by simp⟩
  rw [hx,AddCircle.coe_add,hz,zero_add]
  rfl

#print axioms exists_residue_phases
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ResonantOccupation
