import GaloisForLFunctions.HTGeometry.ConstraintRelativity.BipartiteMatrixDecomposition
import GaloisForLFunctions.HTGeometry.LocalMatrixTensorFactorization
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.DisconnectedSpectra.Factorization

/-! # The mixed component of an operator is equivariant across a circuit cut -/
open Matrix
open scoped Kronecker Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DisconnectedReturns
noncomputable section
open _root_.HTGeometry.ConstraintRelativity
variable {a b : Type*} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]
private abbrev M (i : Type*) := Matrix i i ℂ

omit [Nonempty a] in
private theorem center_conj (A : (M a)ˣ) (X : M a) :
    traceCenter (A.val*X*A.inv)=A.val*traceCenter X*A.inv := by
  have ht : (A.val*X*A.inv).trace=X.trace := by
    rw [Matrix.trace_mul_comm,←mul_assoc,A.inv_val,one_mul]
  simp only [traceCenter,ht,mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    mul_one,A.val_inv]

private def conjugate (A B : M a) : M a →ₗ[ℂ] M a :=
  (LinearMap.mulRight ℂ B).comp (LinearMap.mulLeft ℂ A)

/-- The mixed part transforms by conjugation under every invertible
product matrix. On a simple tensor this says that subtracting normalized
trace from each factor commutes with change of basis. -/
theorem cross_conjugation (A : (M a)ˣ) (B : (M b)ˣ) (X : M (a×b)) :
    crossMatrixPart ((A.val ⊗ₖ B.val)*X*(A.inv ⊗ₖ B.inv)) =
      (A.val ⊗ₖ B.val)*crossMatrixPart X*(A.inv ⊗ₖ B.inv) := by
  let F := crossMatrixPartLinear (m:=a) (n:=b)
  let G := conjugate (A.val ⊗ₖ B.val) (A.inv ⊗ₖ B.inv)
  have he : F.comp G=G.comp F := by
    apply (Matrix.stdBasis ℂ (a×b) (a×b)).ext
    rintro ⟨⟨i,j⟩,⟨k,l⟩⟩
    rw [Matrix.stdBasis_eq_single,←_root_.HTGeometry.ConstraintRelativity.single_kronecker_single]
    let P := Matrix.single i k (1:ℂ)
    let Q := Matrix.single j l (1:ℂ)
    change crossMatrixPart ((A.val ⊗ₖ B.val)*(P ⊗ₖ Q)*(A.inv ⊗ₖ B.inv))=
      (A.val ⊗ₖ B.val)*crossMatrixPart (P ⊗ₖ Q)*(A.inv ⊗ₖ B.inv)
    simp only [←mul_kronecker_mul,crossMatrixPart_kronecker,center_conj]
  exact LinearMap.congr_fun he X

private def split {N : ℕ} (S : Finset (Fin N)) := configurationSplitEquiv (fun _ : Fin N => Bool) S

/-- On the original register this projection retains terms with a
traceless factor on both sides of the chosen bipartition. -/
def cutProjection {N : ℕ} (S : Finset (Fin N)) :
    M (Fin N→Bool) →ₗ[ℂ] M (Fin N→Bool) :=
  let e := Matrix.reindexAlgEquiv ℂ ℂ (split S)
  e.symm.toLinearMap.comp (crossMatrixPartLinear.comp e.toLinearMap)

/-- Conjugation by a gate-respecting circuit preserves the mixed component. -/
theorem cutProjection_circuit {N : ℕ} (C : TwoQubitCircuit N) (S : Finset (Fin N))
    (hcut : ∀ i : Fin C.gateCount, (C.architecture.sites i).1∈S ↔ (C.architecture.sites i).2∈S)
    (X : M (Fin N→Bool)) :
    cutProjection S (C.eval.val*X*star C.eval.val)=C.eval.val*cutProjection S X*star C.eval.val := by
  classical
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ (split S)
  obtain ⟨A,B,hAB⟩ := DisconnectedSpectra.factor_on_cut C S hcut
  change Φ C.eval.val=A ⊗ₖ B at hAB
  have hu := (Unitary.mem_iff.mp C.eval.property)
  have h1 : Φ C.eval.val*Φ (star C.eval.val)=1 := by rw [←map_mul,hu.2,map_one]
  have hi : IsUnit (A ⊗ₖ B) := by
    rw [←hAB]
    exact (show IsUnit C.eval.val from ⟨⟨_,_,hu.2,hu.1⟩,rfl⟩).map Φ
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hi
  rw [Matrix.det_kronecker] at hdet
  have hd := isUnit_iff_ne_zero.mp hdet
  have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr
    (fun ha => hd (by simp [ha])))
  have hB : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr
    (fun hb => hd (by simp [hb])))
  let a := hA.unit
  let b := hB.unit
  have hQ : Φ (star C.eval.val)=a.inv ⊗ₖ b.inv := by
    have hleft : (a.inv ⊗ₖ b.inv)*Φ C.eval.val=1 := by
      rw [hAB]
      change (a.inv ⊗ₖ b.inv)*(a.val ⊗ₖ b.val)=1
      rw [←mul_kronecker_mul,a.inv_val,b.inv_val,Matrix.one_kronecker_one]
    calc
      _ = ((a.inv ⊗ₖ b.inv)*Φ C.eval.val)*Φ (star C.eval.val) := by rw [hleft,one_mul]
      _ = _ := by rw [mul_assoc,h1,mul_one]
  have hproj (Y : M (Fin N→Bool)) : Φ (cutProjection S Y)=crossMatrixPart (Φ Y) := Φ.apply_symm_apply _
  apply Φ.injective
  rw [hproj,map_mul,map_mul,map_mul,map_mul,hproj,hAB,hQ]
  exact cross_conjugation a b _

end
end GaloisForLFunctions.HTGeometry.DisconnectedReturns
