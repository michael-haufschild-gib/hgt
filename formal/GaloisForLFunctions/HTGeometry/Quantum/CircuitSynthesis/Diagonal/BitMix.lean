import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.PhaseCircuit

/-! # Mixing the amplitudes of one physical qubit -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis
noncomputable section

/-- The single-site Hadamard acts independently on each edge parallel to i. -/
def bitMix {n : ℕ} (i : Fin n) : Register n := fun x y =>
  if ∀ j, j ≠ i → x j = y j then boolHadamardMatrix (x i) (y i) else 0

theorem bitMix_circuit {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : Realizes 1 (bitMix i) := by
  classical
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j,hj⟩ := exists_ne i
  let h := hj.symm
  let U := Quantum.tensorGate boolHadamard (1 : unitaryGroup Bool ℂ)
  let G := scalarSpecialUnitaryRepresentative U
  let a := scalarSpecialUnitaryPhase U
  have ha : star a*a=1 := scalarSpecialUnitaryPhase_unitary U
  have hnrm : ‖a‖=1 := by
    have he := congrArg norm ha
    rw [norm_mul,norm_star,norm_one] at he
    nlinarith only [he,norm_nonneg a]
  have he : (twoQubitLift i j h G : Register n) = a • bitMix i := by
    ext x y
    rw [twoQubitLift,unitaryGroupReindex_coe]
    simp only [Equiv.symm_symm,Quantum.tensorGate_val,Matrix.smul_apply]
    let R := {k : Fin n // k ≠ i ∧ k ≠ j}
    let X : R → Bool := fun k => x k.1
    let Y : R → Bool := fun k => y k.1
    change (G : Matrix (Bool × Bool) (Bool × Bool) ℂ) (x i,x j) (y i,y j) * (1 : Matrix (R → Bool) (R → Bool) ℂ) X Y = a * bitMix i x y
    rw [scalarSpecialUnitaryRepresentative_coe]
    simp only [U,Quantum.tensorGate_val,Matrix.smul_apply,Matrix.kronecker_apply,smul_eq_mul]
    change (a*(boolHadamardMatrix (x i) (y i)*(1:Matrix Bool Bool ℂ) (x j) (y j))) * (1 : Matrix (R → Bool) (R → Bool) ℂ) X Y = _
    by_cases hxy : ∀ k, k ≠ i → x k = y k
    · have hr : X=Y := funext fun k => hxy k k.2.1
      rw [bitMix,if_pos hxy,hxy j hj,hr,Matrix.one_apply_eq,Matrix.one_apply_eq,mul_one,mul_one]
    · by_cases hj' : x j=y j
      · have hr : X ≠ Y := by
          intro eq
          apply hxy
          intro k hk
          by_cases hjk : k=j
          · simpa only [hjk] using hj'
          · exact congrFun eq ⟨k,hk,hjk⟩
        simp [bitMix,hxy,Matrix.one_apply,hr]
      · simp [bitMix,hxy,Matrix.one_apply,hj']
  refine ⟨star a,by rwa [norm_star],TwoQubitCircuit.singleOn i j h G,le_rfl,?_⟩
  rw [TwoQubitCircuit.singleOn_eval,he,smul_smul,ha,one_smul]

/-- The two entries entering a Hadamard pair differ only at its chosen site. -/
theorem bitMix_mulVec {n : ℕ} (i : Fin n) (v : (Fin n → Bool) → ℂ) (x : Fin n → Bool) :
    (bitMix i *ᵥ v) x = boolHadamardMatrix (x i) false * v (Function.update x i false) +
      boolHadamardMatrix (x i) true * v (Function.update x i true) := by
  classical
  let x₀ := Function.update x i false
  let x₁ := Function.update x i true
  have hne : x₀ ≠ x₁ := by
    intro h
    simpa [x₀,x₁] using congrFun h i
  have hbit (b : Bool) : ∀ j, j ≠ i → x j = Function.update x i b j :=
    fun j hj => (Function.update_of_ne hj _ _).symm
  have hu (b : Bool) : bitMix i x (Function.update x i b) = boolHadamardMatrix (x i) b := by
    rw [bitMix,if_pos (hbit b),Function.update_self]
  have term (y : Fin n → Bool) : bitMix i x y * v y =
      (if y=x₀ then boolHadamardMatrix (x i) false * v x₀ else 0) +
      (if y=x₁ then boolHadamardMatrix (x i) true * v x₁ else 0) := by
    by_cases h₀ : y=x₀
    · subst y; rw [if_pos rfl,if_neg hne,add_zero,hu false]
    by_cases h₁ : y=x₁
    · subst y; rw [if_neg h₀,if_pos rfl,zero_add,hu true]
    have h : ¬ ∀ j, j ≠ i → x j=y j := by
      intro hoff
      have he : y=Function.update x i (y i) := by
        funext j
        by_cases hj : j=i
        · subst j; simp
        · rw [Function.update_of_ne hj]; exact (hoff j hj).symm
      cases hy : y i
      · exact h₀ (by simpa only [x₀,hy] using he)
      · exact h₁ (by simpa only [x₁,hy] using he)
    simp [bitMix,h,h₀,h₁]
  change (∑ y, bitMix i x y*v y) = _
  simp_rw [term]
  simp [Finset.sum_add_distrib,x₀,x₁]

#print axioms bitMix_circuit
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis
