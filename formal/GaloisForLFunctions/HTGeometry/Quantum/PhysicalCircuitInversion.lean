import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw

/-! # Reversing physical circuits at fixed projective error -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Reverse the gate order and replace each two-site gate by its adjoint. -/
def TwoQubitCircuit.adjoint {n : ℕ} (C : TwoQubitCircuit n) : TwoQubitCircuit n where
  gateCount := C.gateCount
  architecture := { sites := fun r => C.architecture.sites r.rev,
                    distinct := fun r => C.architecture.distinct r.rev }
  gates := fun r => (C.gates r.rev)⁻¹

private theorem gateLift_inv {n : ℕ} (a b : Fin n) (h : a ≠ b)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    twoQubitLift a b h U⁻¹ = (twoQubitLift a b h U)⁻¹ := by
  let e := (splitTwoQubitConfig a b h).symm
  apply Subtype.ext
  change Matrix.reindex e e (Matrix.kronecker U.valᴴ 1) =
    (Matrix.reindex e e (Matrix.kronecker U.val 1))ᴴ
  simp only [Matrix.kronecker,Matrix.conjTranspose_reindex,Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]

private theorem ofFn_rev {α : Type*} {r : ℕ} (f : Fin r → α) :
    List.ofFn (fun i => f i.rev) = (List.ofFn f).reverse := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  rw [List.getElem_ofFn,List.getElem_reverse,List.getElem_ofFn]
  apply congrArg f
  apply Fin.ext
  simp only [Fin.rev,List.length_ofFn]
  omega

theorem TwoQubitCircuit.adjoint_eval {n : ℕ} (C : TwoQubitCircuit n) :
    C.adjoint.eval = C.eval⁻¹ := by
  let g (i) := C.architecture.gateLift i (C.gates i)
  have h i : C.adjoint.architecture.gateLift i (C.adjoint.gates i) = (g i.rev)⁻¹ :=
    gateLift_inv _ _ _ _
  change (List.ofFn fun i => C.adjoint.architecture.gateLift i (C.adjoint.gates i)).reverse.prod =
    (List.ofFn g).reverse.prod⁻¹
  simp only [h,List.prod_inv_reverse,List.map_reverse,List.reverse_reverse,List.map_ofFn,Function.comp_def]
  let f (i : Fin C.gateCount) := (g i)⁻¹
  change (List.ofFn (fun i => f i.rev)).reverse.prod = (List.ofFn f).prod
  rw [ofFn_rev f,List.reverse_reverse]

/-- A gate approximation at time t gives one of equal cost and error at −t. -/
theorem HasProjectiveCircuitApproximation.neg_time {n P : ℕ} {ε t : ℝ}
    (H : selfAdjoint (Reg n)) (h : HasProjectiveCircuitApproximation n ε P
      (unitaryEvolution H.val t)) :
    HasProjectiveCircuitApproximation n ε P (unitaryEvolution H.val (-t)) := by
  obtain ⟨z,hz,C,hC,he⟩ := h
  let U (s : ℝ) : Matrix.unitaryGroup (Fin n → Bool) ℂ :=
    ⟨unitaryEvolution H.val s,unitaryEvolution_mem_unitary H.2 s⟩
  have hprod : U (-t) * U t = 1 := by
    apply Subtype.ext
    change unitaryEvolution H.val (-t) * unitaryEvolution H.val t = 1
    simpa only [zero_sub,unitaryEvolution,zero_smul,NormedSpace.exp_zero] using
      unitaryEvolution_sub_mul H 0 t
  have hinv : U (-t) = (U t)⁻¹ := eq_inv_of_mul_eq_one_left hprod
  have ht : unitaryEvolution H.val (-t) = star (unitaryEvolution H.val t) :=
    congrArg Subtype.val hinv
  refine ⟨star z,by simpa only [norm_star] using hz,C.adjoint,hC,?_⟩
  rw [ht,TwoQubitCircuit.adjoint_eval]
  change ‖star (unitaryEvolution H.val t) - star z • star (C.eval : Reg n)‖ ≤ ε
  rwa [← star_smul,← star_sub,norm_star]

#print axioms HasProjectiveCircuitApproximation.neg_time
end
end GaloisForLFunctions.HTGeometry
