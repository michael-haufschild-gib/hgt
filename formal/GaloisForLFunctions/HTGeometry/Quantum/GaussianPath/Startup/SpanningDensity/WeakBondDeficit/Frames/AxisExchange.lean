import GaloisForLFunctions.HTGeometry.TwoReplicaPauliRelativeParityInverse

/-! # A one-qubit unitary exchanging any Pauli axis with Z -/

open Matrix
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
private abbrev P := finiteQubitPauli

/-- The sign is negative exactly on the axis perpendicular to both
distinct exchanged axes. -/
def axisSign (a b : Fin 3) : ℝ := if a=2 ∨ b=2 ∨ b=a then 1 else -1

theorem axisSign_sq (a b : Fin 3) : axisSign a b^2=1 := by unfold axisSign; split <;> norm_num

private def invRootTwo : ℂ := ((Real.sqrt 2)⁻¹:ℝ)

private theorem root_pair : invRootTwo*invRootTwo=(2:ℂ)⁻¹ := by
  have hr : (Real.sqrt 2)⁻¹*(Real.sqrt 2)⁻¹=(2:ℝ)⁻¹ := by
    rw [←_root_.mul_inv_rev,←sq,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  simpa only [invRootTwo,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_ofNat] using
    congrArg (fun x : ℝ => (x:ℂ)) hr

private theorem twice_basis {a : Fin 3} (ha : a≠2) :
    (P a+P 2)*(P a+P 2)=(2:ℂ) • (1 : Matrix Bool Bool ℂ) := by
  rw [add_mul,mul_add,mul_add,finiteQubitPauli_mul_self,finiteQubitPauli_mul_self,
    finiteQubitPauli_mul_eq_neg_mul_of_ne ha]
  rw [two_smul]
  abel

/-- For unequal axes, (Pₐ+Z)/√2 is its own inverse and exchanges
them by conjugation. The identity serves when a is Z. -/
def axisFrame (a : Fin 3) : Matrix.unitaryGroup Bool ℂ := by
  by_cases ha : a=2
  · exact 1
  · let W := invRootTwo • (P a+P 2)
    have hstar : Wᴴ=W := by
      simp only [W,Matrix.conjTranspose_smul,Matrix.conjTranspose_add,
        (finiteQubitPauli_isHermitian _).eq,invRootTwo,Complex.star_def,Complex.conj_ofReal]
    refine ⟨W,Matrix.mem_unitaryGroup_iff.mpr ?_⟩
    change W*Wᴴ=1
    rw [hstar]
    change (invRootTwo • (P a+P 2))*(invRootTwo • (P a+P 2))=_
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,root_pair,twice_basis ha,smul_smul,
      inv_mul_cancel₀ (by norm_num : (2:ℂ)≠0),one_smul]

/-- Exact signed permutation effected by the local basis change. -/
theorem axisFrame_pauli (a b : Fin 3) :
    (axisFrame a).val*P b*(axisFrame a).valᴴ=
      (axisSign a b:ℂ) • P ((Equiv.swap a 2) b) := by
  by_cases ha : a=2
  · subst a
    simp [axisFrame,axisSign]
  have hframe : (axisFrame a).val=invRootTwo • (P a+P 2) := by simp [axisFrame,ha]
  let W := (axisFrame a).val
  let k := (Equiv.swap a 2) b
  have hinter : W*P b=(axisSign a b:ℂ) • (P k*W) := by
    dsimp only [W]
    rw [hframe,Matrix.smul_mul,Matrix.mul_smul,smul_comm]
    apply congrArg (invRootTwo • ·)
    by_cases hb : b=a
    · subst b
      simp [k,axisSign,add_mul,mul_add,finiteQubitPauli_mul_self,add_comm]
    by_cases hz : b=2
    · subst b
      simp [k,axisSign,add_mul,mul_add,finiteQubitPauli_mul_self,add_comm]
    · rw [show k=b from Equiv.swap_apply_of_ne_of_ne hb hz]
      rw [axisSign,if_neg (by simp [ha,hz,hb]),Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul,
        add_mul,mul_add,finiteQubitPauli_mul_eq_neg_mul_of_ne (Ne.symm hb : a≠b),
        finiteQubitPauli_mul_eq_neg_mul_of_ne (Ne.symm hz : (2:Fin 3)≠b)]
      abel
  change W*P b*Wᴴ=_
  rw [hinter,Matrix.smul_mul,mul_assoc,show W*Wᴴ=1 from (Unitary.mem_iff.mp (axisFrame a).2).2,mul_one]

#print axioms axisFrame_pauli
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
