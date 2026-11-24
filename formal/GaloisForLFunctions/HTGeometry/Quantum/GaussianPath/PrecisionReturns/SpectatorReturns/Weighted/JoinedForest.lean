import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.Weighted.GaussianForms

/-! # Independent gap characters after joining two packet representatives -/

open Finset
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The balanced integer character of an oriented energy gap. -/
def edge (x y j : I) : ℤ := (if x=j then 1 else 0)-(if y=j then 1 else 0)

theorem edge_balanced (x y : I) : SpectralCharacterBalanced (edge x y) := by
  simp [SpectralCharacterBalanced,edge,sum_sub_distrib]

theorem edge_action (x y : I) (E : I→ℝ) : action (edge x y) E=E x-E y := by
  classical
  simp [action,edge,Int.cast_sub,sub_mul,sum_sub_distrib,ite_mul]

omit [Fintype I] in
private theorem leaf_sum {m : ℕ} (l r : Fin m→I) (hi : Function.Injective l)
    (hd : ∀ i j, r i≠l j) (c : Fin m→ℝ) (j : Fin m) :
    (∑ i, c i*(edge (l i) (r i) (l j):ℝ))=c j := by
  simp [edge,hi.eq_iff,hd,mul_ite]

/-- First read a within-packet edge as clock, then the joining edge,
then all remaining within-packet edges. -/
def joinedRows {n : ℕ} (l r : Fin (n+1)→I) (x y : I) : Fin (n+1+1)→I→ℤ :=
  Fin.cons (edge (l 0) (r 0)) (Fin.cons (edge x y) (fun i => edge (l i.succ) (r i.succ)))

theorem joined_balanced {n : ℕ} (l r : Fin (n+1)→I) (x y : I) :
    ∀ i, SpectralCharacterBalanced (joinedRows l r x y i) :=
  Fin.cases (edge_balanced ..) (Fin.cases (edge_balanced ..) (fun _ => edge_balanced ..))

omit [Fintype I] in
theorem joined_independent {n : ℕ} (l r : Fin (n+1)→I) (hi : Function.Injective l)
    (hd : ∀ i j, r i≠l j) {x y : I} (hxy : x≠y) (hx : ∀ i, x≠l i) (hy : ∀ i, y≠l i) :
    IndependentRows (joinedRows l r x y) := by
  classical
  intro c hz
  let d := Fin.cons (α:=fun _ => ℝ) (c 0) (fun i : Fin n => c i.succ.succ)
  have he (j : I) : (∑ i, d i*(edge (l i) (r i) j:ℝ))+c (0:Fin (n+1)).succ*(edge x y j:ℝ)=0 := by
    have h := hz j
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ] at h
    rw [Fin.sum_univ_succ]
    change c 0*(edge (l 0) (r 0) j:ℝ)+(∑ i : Fin n, c i.succ.succ*(edge (l i.succ) (r i.succ) j:ℝ))+
      c (0:Fin (n+1)).succ*(edge x y j:ℝ)=0
    change c 0*(edge (l 0) (r 0) j:ℝ)+(c (0:Fin (n+1)).succ*(edge x y j:ℝ)+
      ∑ i : Fin n, c i.succ.succ*(edge (l i.succ) (r i.succ) j:ℝ))=0 at h
    linarith only [h]
  have hzero : d=0 := funext fun i => by
    change d i=0
    have h := he (l i)
    rw [leaf_sum l r hi hd] at h
    simpa only [edge,if_neg (hx i),if_neg (hy i),sub_self,Int.cast_zero,mul_zero,add_zero] using h
  have hjoin := he x
  simp [hzero,edge,hxy.symm] at hjoin
  funext i
  change c i=0
  exact Fin.cases (congrFun hzero 0) (Fin.cases hjoin (fun j => congrFun hzero j.succ)) i

#print axioms joined_independent
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
