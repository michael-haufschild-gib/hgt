import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.ScalarTail
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AngularError.UnitaryChord

/-! # Angular cost of sparse spectral phases with spectator wires -/

open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.SparsePhases
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- If fewer eigenvalues move than there are spectator copies, every
supported fit is at least as close to identity as it is to the target.
A rank approximation of the spectral tail allows an additive error. -/
theorem identity_le_fit {N : ℕ} {S : Finset (Fin N)} {U V B : Reg N}
    (hV : IsSiteSupported S V) (hr : B.rank < 2^(N-S.card)) :
    ‖1-V‖ ≤ ‖U-V‖ + ‖(1-U)-B‖ := by
  by_contra! h
  apply hr.not_ge (supported_scalar_rank hV B ?_)
  have he : (1-V)-B = (U-V)+((1-U)-B) := by abel
  rw [he]
  exact (norm_add_le ..).trans_lt h

/-- Two short chords meeting at the same supported fit give a doubled
angular radius. At the semicircle this improves the ordinary triangle
inequality from a rank-one reflection floor of one to sqrt(2). -/
theorem doubled_angle {N : ℕ} {S : Finset (Fin N)} {U V : Reg N}
    (hU : U ∈ unitary (Reg N)) (hV : V ∈ unitary (Reg N))
    (hs : IsSiteSupported S V) (hr : (1-U).rank < 2^(N-S.card))
    {θ : ℝ} (hθ : 0 ≤ θ) (hcap : 2*θ ≤ π/2) (hfit : ‖U-V‖ ≤ 2*sin θ) :
    ‖U-1‖ ≤ 2*sin (2*θ) := by
  have h := identity_le_fit (U:=U) hs hr
  rw [sub_self,norm_zero,add_zero] at h
  exact AngularError.common_unitary_chord hU hV (Submonoid.one_mem _) hθ hcap hfit (h.trans hfit)

/-- A spectral displacement with chord 2 sin(a) costs at least the
half-angle chord even when the active unitary can act in any basis. -/
theorem half_angle_floor {N : ℕ} {S : Finset (Fin N)} {U V : Reg N}
    (hU : U ∈ unitary (Reg N)) (hV : V ∈ unitary (Reg N))
    (hs : IsSiteSupported S V) (hr : (1-U).rank < 2^(N-S.card))
    {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ π/2) (hfar : 2*sin a ≤ ‖U-1‖) :
    2*sin (a/2) ≤ ‖U-V‖ := by
  by_contra! h
  let θ := arcsin (‖U-V‖/2)
  have h₀ : 0 ≤ ‖U-V‖/2 := half_nonneg (norm_nonneg _)
  have hlt : ‖U-V‖/2 < sin (a/2) := by linarith only [h]
  have hh : ‖U-V‖/2 ≤ 1 := hlt.le.trans (sin_le_one _)
  have he : sin θ = ‖U-V‖/2 := sin_arcsin (by linarith only [h₀]) hh
  have hθ : 0 ≤ θ := arcsin_nonneg.mpr h₀
  have hθ' : θ < a/2 := by
    apply (strictMonoOn_sin.lt_iff_lt (Set.mem_Icc.mpr ⟨neg_pi_div_two_le_arcsin _,arcsin_le_pi_div_two _⟩)
      (Set.mem_Icc.mpr ⟨by linarith only [ha,pi_pos],by linarith only [ha',pi_pos]⟩)).mp
    rwa [he]
  have h₂ : 2*θ < a := by linarith only [hθ']
  have hh' := doubled_angle hU hV hs hr hθ (h₂.le.trans ha') (by rw [he]; linarith)
  have hstrict := strictMonoOn_sin (show 2*θ ∈ Set.Icc (-(π/2)) (π/2) from
    ⟨by linarith only [hθ,pi_pos],h₂.le.trans ha'⟩)
    (show a ∈ Set.Icc (-(π/2)) (π/2) from ⟨by linarith only [ha,pi_pos],ha'⟩) h₂
  linarith only [hh',hfar,hstrict]

#print axioms half_angle_floor
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.SparsePhases
