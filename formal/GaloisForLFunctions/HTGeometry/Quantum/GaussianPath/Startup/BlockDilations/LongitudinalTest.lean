import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.SparseFlip
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.PairChord

/-! # Testing independent local dilations by the longitudinal fields -/

open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Once the aligned longitudinal fields span a half turn, a fit before
and after a local dilation must pay through its error or its packet wires.
Fields outside the packet do not enter the bound. -/
theorem longitudinal_flip_cost {n : ℕ} (R : Finset (Fin (n+2))) (u : PathShell n)
    (W : Reg (n+2)) (r : ℕ) (t ε : ℝ) :
    let v := pathShellOnSites R u
    let V := unitaryEvolution (pathHamiltonianOnSites R u) t
    π ≤ 2*t*∑ i : Fin (n+2), |v (.inl (i,2))| →
    packetFit R r ε W → packetFit R r ε (V*W) →
    1 ≤ 2*ε+t*‖v‖*(sqrt 21+2+2*sqrt (21*(2*(r:ℝ)))) := by
  intro v V hm h₁ h₂
  have ht : 0<t := by
    by_contra! h
    have hh := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos zero_le_two h)
      (Finset.sum_nonneg fun (i : Fin (n+2)) _ => abs_nonneg (v (.inl (i,2))))
    exact pi_pos.not_ge (hm.trans hh)
  let U : unitaryGroup (Fin (n+2) → Bool) ℂ :=
    ⟨V,unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonianOnSites R u) t⟩
  obtain ⟨S,A,hr,hA,he⟩ := packetFit_relative U W h₁ h₂
  obtain ⟨z,hz⟩ := packet_scalar_comparison R S u A.val hA t
  have hs := ReturnSpacing.PhysicalComponents.paired_angle_scalar_floor v z ht pi_pos.le le_rfl hm
  dsimp only at hs hz
  rw [sin_pi_div_two] at hs
  rw [←pathHamiltonianOnSites_eq_pathHamiltonian_pathShellOnSites R u] at hs
  have hroot : sqrt (21*((R∩S).card:ℝ))≤sqrt (21*(2*(r:ℝ))) :=
    sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by exact_mod_cast hr) (by norm_num))
  have hpen := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hroot (norm_nonneg v))
    (mul_nonneg zero_le_two ht.le)
  rw [abs_of_pos ht] at hz
  change ‖V-A.val‖≤2*ε at he
  change ‖V-z • (1 : Reg (n+2))‖ ≤ ‖V-A.val‖+2*t*(sqrt (21*((R∩S).card:ℝ))*‖v‖) at hz
  calc
    1 ≤ ‖V-z • (1 : Reg (n+2))‖+(sqrt 21+2)*t*‖v‖ := hs
    _ ≤ (2*ε+2*t*(sqrt (21*(2*(r:ℝ)))*‖v‖))+(sqrt 21+2)*t*‖v‖ :=
      add_le_add (hz.trans (add_le_add he hpen)) le_rfl
    _ = _ := by ring

#print axioms longitudinal_flip_cost
end
end GaloisForLFunctions.HTGeometry.BlockDilations
