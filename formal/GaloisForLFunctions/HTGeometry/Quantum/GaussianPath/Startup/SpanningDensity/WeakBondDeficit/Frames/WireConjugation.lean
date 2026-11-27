import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.ProductInputs.ArbitraryBases
import GaloisForLFunctions.HTGeometry.HaferkampLiftedPauliTransport
import GaloisForLFunctions.HTGeometry.HaferkampExactCircuitComplexity

/-! # Product basis changes preserve every gate location -/

open Matrix
open scoped Kronecker
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section

/-- Tensor the local basis changes on an arbitrary finite set of wires. -/
def localFrame {Q : Type*} [Fintype Q] [DecidableEq Q] (F : Q→Matrix.unitaryGroup Bool ℂ) :
    Matrix.unitaryGroup (Q→Bool) ℂ := by
  refine ⟨finiteLocalMatrix (fun v => (F v).val),?_⟩
  rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,finiteLocalMatrix_conjTranspose,finiteLocalMatrix_mul]
  have h (i : Q) : (F i).val*(F i).valᴴ=1 := (Unitary.mem_iff.mp (F i).2).2
  simp only [h,finiteLocalMatrix_one]

private theorem split_frame {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : Q→Matrix.unitaryGroup Bool ℂ) (a b : Q) (hab : a≠b) :
    unitaryGroupReindex (splitTwoQubitConfig a b hab) (localFrame F)=
      Quantum.tensorGate (Quantum.tensorGate (F a) (F b))
        (localFrame fun q : {i : Q // i≠a ∧ i≠b} => F q.val) := by
  apply Subtype.ext
  ext x y
  rcases x with ⟨xlocal,xrest⟩
  rcases y with ⟨ylocal,yrest⟩
  change (∏ q, (F q).val ((splitTwoQubitConfig a b hab).symm (xlocal,xrest) q)
    ((splitTwoQubitConfig a b hab).symm (ylocal,yrest) q))=_
  rw [prod_split_two a b hab]
  change _ = (F a).val xlocal.1 ylocal.1 * (F b).val xlocal.2 ylocal.2 *
    ∏ q : {i : Q // i≠a ∧ i≠b}, (F q.val).val (xrest q) (yrest q)
  simp [splitTwoQubitConfig,hab.symm]
  left
  apply Finset.prod_congr rfl
  intro q _
  simp [q.property.1,q.property.2]

private def conjugateLocal {Q : Type*} [Fintype Q] [DecidableEq Q] (W : Matrix.unitaryGroup Q ℂ)
    (G : Matrix.specialUnitaryGroup Q ℂ) : Matrix.specialUnitaryGroup Q ℂ := by
  let g : Matrix.unitaryGroup Q ℂ := ⟨G.val,(mem_specialUnitaryGroup_iff.mp G.2).1⟩
  refine ⟨(W*g*W⁻¹).val,mem_specialUnitaryGroup_iff.mpr ⟨(W*g*W⁻¹).2,?_⟩⟩
  change (W.val*G.val*(W⁻¹).val).det=1
  rw [det_mul,det_mul,(mem_specialUnitaryGroup_iff.mp G.2).2,mul_one,←det_mul]
  change ((W*W⁻¹).val).det=1
  rw [mul_inv_cancel,show (1:Matrix.unitaryGroup Q ℂ).val=1 from rfl,det_one]

/-- Even the architecture is fixed by a site-dependent change of
basis. Each two-qubit gate is conjugated only on its own two wires. -/
theorem conjugate_architecture {n m : ℕ} (F : Fin n→Matrix.unitaryGroup Bool ℂ)
    (A : TwoQubitArchitecture n m) (G : Fin m→Matrix.specialUnitaryGroup (Bool×Bool) ℂ) :
    ∃ T : Fin m→Matrix.specialUnitaryGroup (Bool×Bool) ℂ,
      A.contraction T=localFrame F * A.contraction G * (localFrame F)⁻¹ := by
  let T (i : Fin m) := conjugateLocal (Quantum.tensorGate (F (A.sites i).1) (F (A.sites i).2)) (G i)
  let Φ := MulAut.conj (localFrame F)
  have hgate (i : Fin m) : Φ (A.gateLift i (G i))=A.gateLift i (T i) := by
    let a := (A.sites i).1
    let b := (A.sites i).2
    let e := splitTwoQubitConfig a b (A.distinct i)
    let P := Quantum.tensorGate (F a) (F b)
    let R := localFrame fun q : {j : Fin n // j≠a ∧ j≠b} => F q.val
    apply Subtype.ext
    apply (Matrix.reindexAlgEquiv ℂ ℂ e).injective
    change Matrix.reindex e e ((localFrame F).val*(twoQubitLift a b _ (G i)).val*(localFrame F).valᴴ)=_
    rw [reindex_conjugation,show unitaryGroupReindex e (localFrame F)=Quantum.tensorGate P R from split_frame ..]
    have hlift (g : Matrix.specialUnitaryGroup (Bool×Bool) ℂ) :
        Matrix.reindex e e (twoQubitLift a b (A.distinct i) g).val=Matrix.kronecker g.val 1 := by
      change (unitaryGroupReindex e (unitaryGroupReindex e.symm _)).val=_
      rw [unitaryGroupReindex_apply_symm]
      rfl
    change _ = Matrix.reindex e e (twoQubitLift a b _ (T i)).val
    rw [hlift,hlift,finiteTensorGate_conjugation P R (G i).val 1,mul_one,
      show R.val*R.valᴴ=1 from (Unitary.mem_iff.mp R.2).2]
    rfl
  refine ⟨T,?_⟩
  change _ = Φ ((List.ofFn fun i => A.gateLift i (G i)).reverse.prod)
  rw [map_list_prod,List.map_reverse,List.map_ofFn]
  exact congrArg (fun l : List (Matrix.unitaryGroup (Fin n→Bool) ℂ) => l.reverse.prod)
    (congrArg List.ofFn (funext fun i => (hgate i).symm))

#print axioms conjugate_architecture
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
