import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.BondHamiltonians
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.BondCoordinates
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.ShortWord
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitDeletionBound

/-! # Compiling a layer of disjoint physical bond evolutions -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
noncomputable section
abbrev Register (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance (N : ℕ) : CStarAlgebra (Register N) where
local instance (N : ℕ) : NormedAlgebra ℚ (Register N) := .restrictScalars ℚ ℂ _

/-- A lifted matrix acts only on its two designated wires. -/
private theorem lift_supported {N : ℕ} (a b : Fin N) (h : a ≠ b)
    (B : BondCoordinates.LocalMatrix) :
    IsSiteSupported {a,b} (twoQubitLiftMatrix a b h B) := by
  let I := {i : Fin N // i ≠ a ∧ i ≠ b}
  let rest (x : Fin N→Bool) := fun i : I => x i.val
  have entry (x y : Fin N→Bool) : twoQubitLiftMatrix a b h B x y=
      B (x a,x b) (y a,y b)*(1 : Matrix (I→Bool) _ ℂ) (rest x) (rest y) := rfl
  constructor
  · rintro x y ⟨i,hi,hxy⟩
    have he : rest x ≠ rest y := fun h => hxy (congrFun h ⟨i,by simpa using hi⟩)
    rw [entry,Matrix.one_apply_ne he,mul_zero]
  · intro x y x' y' hx hy ho ho'
    have hr (v w : Fin N→Bool) (h : ∀ i, i ∉ ({a,b} : Finset (Fin N)) → v i=w i) :
        rest v=rest w := funext fun i => h i.val (by simpa using i.property)
    rw [entry,entry,hr x y ho,hr x' y' ho',Matrix.one_apply_eq,Matrix.one_apply_eq,
      hx a (by simp),hx b (by simp),hy a (by simp),hy b (by simp)]

/-- The skew-adjoint generator of one lifted bond. -/
def generator {n : ℕ} (e : Fin (n+1)) (B : selfAdjoint BondCoordinates.LocalMatrix) : Register (n+2) :=
  (-Complex.I) • twoQubitLiftMatrix e.castSucc e.succ (endpoints_ne e) B.val

theorem generator_skew {n : ℕ} (e : Fin (n+1)) (B : selfAdjoint BondCoordinates.LocalMatrix) :
    generator e B ∈ skewAdjoint (Register (n+2)) := by
  have hh : IsSelfAdjoint (twoQubitLiftMatrix e.castSucc e.succ (endpoints_ne e) B.val) := by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mp
    dsimp only [twoQubitLiftMatrix]
    apply Matrix.IsHermitian.reindex
    rw [Matrix.IsHermitian]
    unfold Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker,B.property.isHermitian.eq,Matrix.conjTranspose_one]
  rw [skewAdjoint.mem_iff]
  simp only [generator,star_smul,hh.star_eq,star_neg,Complex.star_def,Complex.conj_I,neg_neg,neg_smul]

private theorem generator_commute {n : ℕ} {e f : Fin (n+1)} (hne : e ≠ f)
    (h : e.val%2=f.val%2) (B D : selfAdjoint BondCoordinates.LocalMatrix) :
    Commute (generator e B) (generator f D) := by
  have hv : e.val ≠ f.val := fun he => hne (Fin.ext he)
  have dis : Disjoint ({e.castSucc,e.succ} : Finset (Fin (n+2))) {f.castSucc,f.succ} := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with rfl|rfl <;> rcases hj with hj|hj <;>
      have he := congrArg Fin.val hj <;> simp only [Fin.val_castSucc,Fin.val_succ] at he <;> omega
  exact ((commute_of_isSiteSupported_disjoint dis (lift_supported _ _ (endpoints_ne e) B.val)
    (lift_supported _ _ (endpoints_ne f) D.val)).smul_left _).smul_right _

/-- A same-parity bond layer compiles exactly at one gate per member. -/
theorem compile_layer {n : ℕ} (B : Fin (n+1)→selfAdjoint BondCoordinates.LocalMatrix)
    (S : Finset (Fin (n+1))) (hp : ∀ i∈S, ∀ j∈S, i.val%2=j.val%2) (t : ℝ) :
    HasProjectiveCircuitApproximation (n+2) 0 S.card (exp (t • ∑ e∈S, generator e (B e))) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1,norm_one,TwoQubitCircuit.one _,by simp [TwoQubitCircuit.one],?_⟩
    simp [TwoQubitCircuit.one_eval]
  | @insert e S he ih =>
    have hinc (i) (hi : i ∈ S) : i ∈ insert e S := Finset.mem_insert_of_mem hi
    have htail := ih (fun i hi j hj => hp i (hinc i hi) j (hinc j hj))
    have hcomm : Commute (generator e (B e)) (∑ f∈S, generator f (B f)) :=
      Commute.sum_right _ _ _ fun f hf => generator_commute (e:=e) (f:=f) (by rintro rfl; exact he hf)
        (hp e (Finset.mem_insert_self ..) f (hinc f hf)) _ _
    have hsk := (skewAdjoint (Register (n+2))).sum_mem fun f (_ : f ∈ S) => generator_skew f (B f)
    have hu := exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hsk)
    obtain ⟨z,hz,C,hC,hflow⟩ := BondCoordinates.lifted_flow e (B e) t
    have hsingle : HasProjectiveCircuitApproximation (n+2) 0 1 (exp (t • generator e (B e))) :=
      ⟨z,hz,C,hC.le,by rw [show exp (t • generator e (B e))=z • C.eval.val from hflow,sub_self,norm_zero]⟩
    have hh := LocalPatches.approx_product hu hsingle htail
    rw [Finset.sum_insert he,smul_add,exp_add_of_commute ((hcomm.smul_left t).smul_right t),Finset.card_insert_of_notMem he]
    simpa only [zero_add,Nat.add_comm 1] using hh

end
end GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
