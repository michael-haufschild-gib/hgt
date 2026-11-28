import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.NormalForm
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelDephasingInverse
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelProbeStability
import GaloisForLFunctions.HTGeometry.Quantum.PathPauliSpectralWidth

/-! # Operator-norm control by a field filtered at finite energy resolution -/

open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.EnergyWindows
open private energyCoordinates_hamiltonian from GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.CommutatorGreen
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- The zero-centered Abel filter preserves Hermitian fields. -/
theorem filtered_hermitian {H G : Mat I} (hH : H.IsHermitian) (hG : G.IsHermitian) (η : Ioi (0:ℝ)) :
    (hamiltonianDampedGapResponse hH 0 η G).IsHermitian := by
  let Y := hamiltonianDampedGapResponse hH 0 η G
  have hz : star (hamiltonianAbelShift η) = -hamiltonianAbelShift η := by
    apply Complex.ext <;> simp [hamiltonianAbelShift]
  have hs : star (H*Y-Y*H) = -(H*star Y-star Y*H) := by
    rw [star_sub,star_mul,star_mul,hH.isSelfAdjoint.star_eq,neg_sub]
  have hinv := congrArg star (hamiltonianAbelInverse_leftInverse hH η G)
  change star (hamiltonianAbelInverse H η Y)=star G at hinv
  rw [hamiltonianAbelInverse_eq_sub,star_sub,star_smul,star_inv₀,hz,inv_neg,hs,smul_neg,
    neg_smul,neg_neg,hG.isSelfAdjoint.star_eq] at hinv
  have he : hamiltonianAbelInverse H η (star Y)=G := by
    rwa [hamiltonianAbelInverse_eq_sub]
  exact ((dampedGapResponse_zero_eq_iff_abelInverse_eq hH η G (star Y)).mpr he).symm

/-- Every eigenvalue of the filtered field is a diagonal expectation of
the original field in that eigenvector. In particular its norm contracts. -/
theorem filtered_norm_le [Nonempty I] {H G : Mat I} (hH : H.IsHermitian) (hG : G.IsHermitian)
    (η : Ioi (0:ℝ)) : ‖hamiltonianDampedGapResponse hH 0 η G‖ ≤ ‖G‖ := by
  let Y := hamiltonianDampedGapResponse hH 0 η G
  have hY : Y.IsHermitian := filtered_hermitian hH hG η
  have hi := hamiltonianAbelInverse_leftInverse hH η G
  change hamiltonianAbelInverse H η Y=G at hi
  rw [hamiltonianAbelInverse_eq_sub,show H*Y-Y*H= -(Y*H-H*Y) by abel] at hi
  have hj (j : I) : (hY.eigenvalues j:ℂ) = hamiltonianEnergyCoordinates hY G j j := by
    have hh := congrArg (fun X : Mat I => hamiltonianEnergyCoordinates hY X j j) hi
    change hamiltonianEnergyCoordinates hY (Y-_ • -(Y*H-H*Y)) j j=_ at hh
    rw [map_sub,map_smul,map_neg,Matrix.sub_apply,Matrix.smul_apply,Matrix.neg_apply,
      energyCoordinates_commutator_apply,hamiltonianGap,sub_self,Complex.ofReal_zero,zero_mul,
      neg_zero,smul_zero,sub_zero,energyCoordinates_hamiltonian,Matrix.diagonal_apply_eq] at hh
    exact hh
  have hf : ‖hamiltonianEnergyCoordinates hY G‖=‖G‖ := by
    rw [hamiltonianEnergyCoordinates,Unitary.conjStarAlgAut_symm_apply,
      CStarRing.norm_mul_mem_unitary _ hY.eigenvectorUnitary.2,
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hY.eigenvectorUnitary.2)]
  change ‖Y‖ ≤ ‖G‖
  conv_lhs => rw [isHermitian_eq_conj_diagonal hY]
  rw [l2_opNorm_unitary_conj_eq hY.eigenvectorUnitary.2,Matrix.l2_opNorm_diagonal,
    pi_norm_le_iff_of_nonempty]
  intro j
  change ‖(hY.eigenvalues j:ℂ)‖ ≤ ‖G‖
  rw [hj j]
  exact (norm_entry_le_l2_opNorm _ j j).trans_eq hf

/-- At every date the filtered field gives an operator-norm approximation
with error independent of dimension and of the smallest energy gap. -/
theorem abel_field_evolution [Nonempty I] (H G : selfAdjoint (Mat I)) (η : Ioi (0:ℝ)) (b t : ℝ) :
    let Y := hamiltonianDampedGapResponse H.2.isHermitian 0 η G.val
    ‖unitaryEvolution (H.val+b • G.val) t-unitaryEvolution (H.val+b • Y) t‖ ≤
      2*|b| *‖G.val‖*(1+|t| *|b| *‖G.val‖)/(η:ℝ) := by
  letI : CStarAlgebra (Mat I) := {}
  intro Y
  let z := hamiltonianAbelShift η
  let X := (-z⁻¹) • Y
  have hi := hamiltonianAbelInverse_leftInverse H.2.isHermitian η G.val
  change hamiltonianAbelInverse H.val η Y=G.val at hi
  rw [hamiltonianAbelInverse_eq_sub] at hi
  have hx : H.val*X-X*H.val=G.val-Y := by
    rw [←hi]
    dsimp only [X,z]
    rw [Matrix.mul_smul,Matrix.smul_mul,←smul_sub,neg_smul]
    abel
  have hy := filtered_norm_le H.2.isHermitian G.2.isHermitian η
  change ‖Y‖ ≤ ‖G.val‖ at hy
  have hxn : ‖X‖ ≤ ‖G.val‖/(η:ℝ) := by
    rw [show ‖X‖=‖-z⁻¹‖*‖Y‖ from norm_smul ..,norm_neg,norm_inv,norm_hamiltonianAbelShift]
    exact (mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr η.2.le)).trans_eq (by ring)
  have hm : ‖X*Y-G.val*X‖ ≤ 2*(‖G.val‖/(η:ℝ))*‖G.val‖ := by
    apply (norm_sub_le _ _).trans
    calc
      _ ≤ ‖X‖*‖Y‖+‖G.val‖*‖X‖ := add_le_add (norm_mul_le ..) (norm_mul_le ..)
      _ ≤ _ := (add_le_add (mul_le_mul hxn hy (norm_nonneg _) (div_nonneg (norm_nonneg _) η.2.le))
        (mul_le_mul_of_nonneg_left hxn (norm_nonneg _))).trans_eq (by ring)
  apply (field_evolution_bound H.val G.val Y X H.2 G.2
    (filtered_hermitian H.2.isHermitian G.2.isHermitian η).isSelfAdjoint hx b t).trans
  apply (add_le_add (mul_le_mul_of_nonneg_left hxn (by positivity : 0 ≤ 2*|b|))
    (mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ |t| *b^2))).trans_eq
  rw [←sq_abs b]
  ring

#print axioms abel_field_evolution
end
end GaloisForLFunctions.HTGeometry.Dephasing.EnergyWindows
