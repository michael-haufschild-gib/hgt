import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.BlockCommutators
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.Commutator

/-! # The error of a local time change comes only from its boundary -/

open Matrix Finset NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations
open LocalPatches
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance (N : ℕ) : CStarAlgebra (Reg N) where
variable {n : ℕ}

/-- Only pairs of overlapping Pauli words with one changed and one
unchanged coefficient enter the commutator of a local time change. -/
def boundaryMass (u : PathShell n) (S : Finset (PathLabel n)) : ℝ :=
  ∑ q ∈ Sᶜ, ∑ l ∈ S∩pathOverlaps q, 2*|u q|*|u l|

private theorem subset_commutator (u : PathShell n) (S : Finset (PathLabel n)) :
    let A := ∑ l ∈ S, pathTermGenerator u l
    let H := ∑ q, pathTermGenerator u q
    ‖A*H-H*A‖≤boundaryMass u S := by
  intro A H
  let X := pathTermGenerator u
  let B := ∑ q ∈ Sᶜ, X q
  have hsum : A+B=H := sum_add_sum_compl S X
  have he : A*H-H*A=A*B-B*A := by rw [←hsum]; noncomm_ring
  rw [he,norm_sub_rev]
  apply (LocalErrors.norm_commutator_sums Sᶜ S X X).trans
  apply sum_le_sum
  intro q _
  have hzero (l) (hl : l∉pathOverlaps q) : ‖X q*X l-X l*X q‖=0 := by
    have hd : Disjoint (labelSupport (pathWord q)) (labelSupport (pathWord l)) :=
      Classical.byContradiction (fun hn => hl (mem_pathOverlaps.mpr hn))
    have hh := commute_finitePauliMatrix_of_disjoint hd
    have hc : Commute (X q) (X l) :=
      (((hh.smul_left (u q:ℂ)).smul_left (-Complex.I)).smul_right (u l:ℂ)).smul_right (-Complex.I)
    rw [hc.eq,sub_self,norm_zero]
  rw [←sum_subset (inter_subset_left (s₂:=pathOverlaps q)) (fun l hl hn =>
    hzero l (fun hy => hn (mem_inter.mpr ⟨hl,hy⟩)))]
  apply sum_le_sum
  intro l _
  calc
    _ ≤ ‖X q‖*‖X l‖+‖X l‖*‖X q‖ :=
      (norm_sub_le ..).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ = _ := by rw [(pathTerm_properties u q).1,(pathTerm_properties u l).1]; ring

/-- Dilating selected coefficients by 1+a can be compared to a
packet rotation before the original orbit at every positive time.
Internal commutators cancel exactly. -/
theorem subset_dilation_error (u : PathShell n) (S : Finset (PathLabel n))
    {t a : ℝ} (ht : 0≤t) (ha : 0≤a) :
    let A := ∑ l ∈ S, pathTermGenerator u l
    let H := ∑ q, pathTermGenerator u q
    ‖exp (t • (a • A+H))-exp ((t*a) • A)*exp (t • H)‖ ≤
      t^2*a*boundaryMass u S := by
  intro A H
  have hA : A∈skewAdjoint (Reg (n+2)) := (skewAdjoint _).sum_mem fun l _ => (pathTerm_properties u l).2.1
  have hH : H∈skewAdjoint (Reg (n+2)) := (skewAdjoint _).sum_mem fun l _ => (pathTerm_properties u l).2.1
  have hh := norm_lie_pair_error_le_commutator (a • A) H (skewAdjoint.smul_mem a hA) hH t ht
  rw [smul_smul,smul_mul_assoc,mul_smul_comm,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg ha] at hh
  rw [norm_sub_rev]
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (subset_commutator u S) ha) (sq_nonneg t)).trans_eq (mul_assoc ..).symm)

#print axioms subset_dilation_error
end
end GaloisForLFunctions.HTGeometry.BlockDilations
