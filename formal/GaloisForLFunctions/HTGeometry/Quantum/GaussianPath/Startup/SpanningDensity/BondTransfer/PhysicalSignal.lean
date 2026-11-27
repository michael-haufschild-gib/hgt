import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.IncidentCommutators
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutErasure
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.Calibration.Longitudinal

/-! # Relative short-time transfer on a physical bond of the full chain -/

open Matrix Finset RHTower GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open LocalPatches FixedHorizon
noncomputable section
variable {n : ℕ}
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance signalAlgebra (N : ℕ) : CStarAlgebra (Reg N) where

private theorem signal_transport (H Y B : Reg (n+2)) (t : ℝ) :
    signal H Y B t=((Fintype.card (Fin (n+2)→Bool):ℂ)⁻¹*
      (transported ((-Complex.I) • H) t Y*B).trace).re := by
  simp only [signal,transported,unitaryEvolution,smul_neg,neg_smul]

/-- The normalized two-site transfer differs from twice time times the
longitudinal coupling by at most a quadratic error proportional to
the norm of this bond and to the Pauli mass at its two endpoints. -/
theorem bond_signal_relative (u : PathShell n) (e : Fin (n+1)) (t : ℝ) (ht : 0≤t) :
    let S : Finset (Fin (n+2)) := {e.castSucc,e.succ}
    let E := ∑ l∈S.biUnion pathIncidentLabels, |u l|
    |bondSignal e u t-2*t*u (bondLabel e)|≤4*t^2*‖edgePart u e‖*(2*E+‖edgePart u e‖) := by
  intro S E
  let Y := bondOutput e
  let B := bondInput e
  let j := (-Complex.I) • edgePart u e
  let k := (-Complex.I) • pathHamiltonian u
  let p := bracketStep j Y
  let X := transported k t Y
  let Z := transported (k-j) t Y
  let d : ℂ := Fintype.card (Fin (n+2)→Bool)
  have hY : IsSiteSupported S Y := bond_output_supported (mem_insert_self ..)
  have hJ : IsSiteSupported S (edgePart u e) := by
    unfold edgePart
    apply Finset.sum_induction _ _ (fun _ _ h₁ h₂ => IsSiteSupported.add h₁ h₂) (IsSiteSupported.zero S)
    intro ab _
    apply IsSiteSupported.complex_smul
    apply finitePauliMatrix_isSiteSupported_of_eq_none
    intro i hi
    have h₁ : i≠e.castSucc := fun h => hi (h ▸ mem_insert_self ..)
    have h₂ : i≠e.succ := fun h => hi (h ▸ mem_insert_of_mem (mem_singleton_self ..))
    simp only [couplingWord,if_neg h₁,if_neg h₂]
  have hj : j∈skewAdjoint (Reg (n+2)) := by
    change star ((-Complex.I) • edgePart u e)=-((-Complex.I) • edgePart u e)
    rw [star_smul,(isSelfAdjoint_edgePart u e).star_eq,star_neg,Complex.star_def,Complex.conj_I,neg_neg,neg_smul,neg_neg]
  have estimate := local_erasure u S Y j hY (IsSiteSupported.complex_smul _ hJ) hj t ht
  change ‖X-Z-t • p‖≤t^2*(4*‖Y‖*‖j‖*(2*E+‖j‖)) at estimate
  have htrace (W : Reg (n+2)) : |(d⁻¹*(W*B).trace).re|≤‖W‖ := calc
    _ ≤ ‖d⁻¹*(W*B).trace‖ := Complex.abs_re_le_norm _
    _ ≤ ‖W*B‖ := by simpa only [Matrix.trace_zero,mul_zero,sub_zero] using
      norm_normalizedTrace_sub_le_l2OpNorm (W*B) 0
    _ ≤ _ := (norm_mul_le _ _).trans
      ((mul_le_mul_of_nonneg_left (bond_input_norm e) (norm_nonneg W)).trans_eq (mul_one ‖W‖))
  have htX : bondSignal e u t=(d⁻¹*(X*B).trace).re := signal_transport _ _ _ _
  have htZ : (d⁻¹*(Z*B).trace).re=0 := by
    have h := erased_transfer_zero u e t
    rw [signal_transport] at h
    simpa only [pathHamiltonianCut,smul_sub] using h
  have hd : d=(2:ℂ)^(n+2) := by simp [d]
  have hp : d⁻¹*(p*B).trace=2*((u (bondLabel e):ℝ):ℂ) := by
    rw [show (p*B).trace=_ from longitudinal_transfer u e,hd,←mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℂ)≠0)),one_mul]
  have he : (d⁻¹*((X-Z-t • p)*B).trace).re=bondSignal e u t-2*t*u (bondLabel e) := by
    rw [sub_mul,sub_mul,Matrix.smul_mul,Matrix.trace_sub,Matrix.trace_sub,Matrix.trace_smul,
      mul_sub,mul_sub,Complex.real_smul,←mul_assoc d⁻¹, mul_comm d⁻¹ (t:ℂ),mul_assoc, hp,
      Complex.sub_re,Complex.sub_re,←htX,htZ,sub_zero]
    simp only [←Complex.ofReal_ofNat,←Complex.ofReal_mul,Complex.ofReal_re]
    ring
  rw [←he]
  apply (htrace _).trans (estimate.trans_eq ?_)
  rw [show ‖Y‖=1 from norm_finitePauliMatrix _,show ‖j‖=‖edgePart u e‖ by
    dsimp only [j]; rw [norm_smul,norm_neg,Complex.norm_I,one_mul]]
  ring

#print axioms bond_signal_relative
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
