import GaloisForLFunctions.HTGeometry.Lattices.IntegralNormTwoCoordinates

/-!
# The integral Cartan forms of a path and a fork

Boundary differences identify the integral path lattice with vectors of
coordinate sum zero. Splitting the two terminal arms identifies the fork
lattice with vectors of even coordinate sum. The norm-one counts follow
from the norm-two shells in Euclidean coordinates.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.ClassicalCartan
open IntegralZeroSum
variable {n : ℕ}

/- Both tuple operations use the constant family of integers. -/
local notation "consℤ" => Fin.cons (α := fun _ => ℤ)
local notation "snocℤ" => Fin.snoc (α := fun _ => ℤ)

/-- Differences of consecutive coefficients padded by zero at the two ends. -/
def boundary (a : Fin n → ℤ) (i : Fin (n+1)) := snocℤ a 0 i-consℤ 0 a i

private def read (y : Fin (n+1) → ℤ) (k : ℕ) := if h : k<n+1 then y ⟨k,h⟩ else 0

private def acc (y : Fin (n+1) → ℤ) (k : ℕ) := ∑ j ∈ range k, read y j

def integrate (y : Fin (n+1) → ℤ) (i : Fin n) := acc y (i.val+1)

theorem sum_boundary (a : Fin n → ℤ) : ∑ i, boundary a i=0 := by
  simp only [boundary,sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (snocℤ a 0),Fin.sum_univ_succ (consℤ 0 a)]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,Fin.cons_zero,Fin.cons_succ,zero_add,add_zero,sub_self]

private theorem cons_integrate (y : Fin (n+1) → ℤ) (i : Fin (n+1)) :
    consℤ 0 (integrate y) i=acc y i.val := by
  refine Fin.cases (by simp [acc]) (fun j => ?_) i
  simp only [Fin.cons_succ,Fin.val_succ,integrate]

private theorem acc_total (y : Fin (n+1) → ℤ) : acc y (n+1)=∑ j,y j := by
  rw [acc,← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun j _ => by simp [read,j.isLt]

private theorem boundary_integrate (y : Fin (n+1) → ℤ) (hy : (∑ j,y j)=0) :
    boundary (integrate y)=y := by
  have left (i : Fin (n+1)) : snocℤ (integrate y) 0 i=acc y (i.val+1) := by
    refine Fin.lastCases (by simp [acc_total,hy]) (fun j => ?_) i
    simp only [Fin.snoc_castSucc,Fin.val_castSucc,integrate]
  funext i
  rw [boundary,left,cons_integrate]
  have rd : read y i.val=y i := by unfold read; rw [dif_pos i.isLt]
  simp [acc,sum_range_succ,rd]

private theorem integrate_boundary (a : Fin n → ℤ) : integrate (boundary a)=a := by
  have acc_before (i : Fin (n+1)) : acc (boundary a) i.val=consℤ 0 a i := by
    refine Fin.induction (by simp [acc]) (fun j ih => ?_) i
    rw [Fin.val_succ,acc,sum_range_succ]
    change acc (boundary a) j.castSucc.val+read (boundary a) j.val=_
    rw [ih]
    change _+ (if h : j.val<n+1 then boundary a ⟨j.val,h⟩ else 0)=_
    rw [dif_pos (Nat.lt_succ_of_lt j.isLt)]
    change consℤ 0 a j.castSucc+(snocℤ a 0 j.castSucc-consℤ 0 a j.castSucc)=consℤ 0 a j.succ
    simp [Fin.snoc_castSucc,Fin.cons_succ]
  funext i
  exact (acc_before i.succ).trans (Fin.cons_succ _ _ _)

/-- Integer lattice isomorphism at the level of coordinates, including
the zero-dimensional path. -/
def pathCoordinates (n : ℕ) : (Fin n → ℤ) ≃ {y : Fin (n+1) → ℤ // (∑ j,y j)=0} where
  toFun a := ⟨boundary a,sum_boundary a⟩
  invFun y := integrate y.val
  left_inv := integrate_boundary
  right_inv y := Subtype.ext (boundary_integrate _ y.property)

/-- The product of the two padded coordinates counts each path edge once. -/
def pathEnergy (a : Fin n → ℤ) :=
  (∑ i,(a i)^2)-∑ i : Fin (n+1), snocℤ a 0 i*consℤ 0 a i

/-- The parent of an index is its predecessor, with no parent at zero. -/
def previous (i : Fin n) : Option (Fin n) :=
  if i.val=0 then none else some ⟨i.val-1,by omega⟩

theorem previous_eq (i j : Fin n) : previous i=some j ↔ j.val+1=i.val := by
  by_cases h : i.val=0
  · simp [previous,h]
  · rw [previous,if_neg h,Option.some.injEq,Fin.ext_iff]
    change i.val-1=j.val ↔ j.val+1=i.val
    omega

/-- Each predecessor contributes the product of two consecutive
coordinates in the padded boundary-difference form. -/
theorem path_parent_energy (a : Fin n → ℤ) :
    (∑ i,(a i)^2)-(∑ i,(previous i).elim 0 (fun j => a i*a j))=pathEnergy a := by
  unfold pathEnergy
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,zero_mul,add_zero]
  apply sum_congr rfl
  intro i _
  by_cases h : i.val=0
  · have hi : i.castSucc=0 := Fin.ext h
    simp [previous,h,hi]
  · let j : Fin n := ⟨i.val-1,by omega⟩
    have hi : j.succ=i.castSucc := Fin.ext (by change i.val-1+1=i.val; omega)
    rw [(previous_eq i j).mpr (by change i.val-1+1=i.val; omega),← hi,Fin.cons_succ]
    rfl

theorem boundary_energy (a : Fin n → ℤ) : energy (boundary a)=2*pathEnergy a := by
  have L : (∑ i : Fin (n+1), (snocℤ a 0 i)^2)=∑ i,(a i)^2 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc,Fin.snoc_last,zero_pow (by decide : 2≠0),add_zero]
  have R : (∑ i : Fin (n+1), (consℤ 0 a i)^2)=∑ i,(a i)^2 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_succ,Fin.cons_zero,zero_pow (by decide : 2≠0),zero_add]
  unfold energy pathEnergy boundary
  simp only [sub_sq,sum_add_distrib,sum_sub_distrib,mul_assoc,← mul_sum,L,R]
  ring

def pathRootEquiv (n : ℕ) : {a : Fin n → ℤ // pathEnergy a=1} ≃ ZeroShell (Fin (n+1)) where
  toFun a := ⟨boundary a.val,sum_boundary _,by rw [boundary_energy,a.property]; norm_num⟩
  invFun y := ⟨integrate y.val,by have h := boundary_energy (integrate y.val); rw [boundary_integrate _ y.property.1,y.property.2] at h; omega⟩
  left_inv a := Subtype.ext (integrate_boundary _)
  right_inv y := Subtype.ext (boundary_integrate _ y.property.1)

theorem path_root_count (n : ℕ) : Nat.card {a : Fin n → ℤ // pathEnergy a=1}=(n+1)*n := by
  rw [Nat.card_congr (pathRootEquiv n),card_zeroShell,Fintype.card_fin,Nat.add_sub_cancel]

abbrev Fork (n : ℕ) := (Fin n → ℤ) × ℤ × ℤ

private def adjust (y : Fin (n+1) → ℤ) (c : ℤ) (i : Fin (n+1)) :=
  y i+if i=Fin.last n then c else 0

private theorem sum_adjust (y : Fin (n+1) → ℤ) (c : ℤ) : ∑ i, adjust y c i=(∑ i,y i)+c := by
  simp [adjust,sum_add_distrib]

private theorem adjust_undo (y : Fin (n+1) → ℤ) (c : ℤ) : adjust (adjust y c) (-c)=y := by
  funext i
  by_cases h : i=Fin.last n <;> simp [adjust,h]

/-- The total sum after adjoining the fork is twice its last terminal coefficient. -/
def forkVector (a : Fork n) : Fin (n+2) → ℤ :=
  snocℤ (adjust (boundary a.1) (a.2.1+a.2.2)) (a.2.2-a.2.1)

private theorem sum_fork (a : Fork n) : (∑ i,forkVector a i)=2*a.2.2 := by
  rw [Fin.sum_univ_castSucc]
  simp only [forkVector,Fin.snoc_castSucc,Fin.snoc_last,sum_adjust,sum_boundary,zero_add]
  ring

private def forkEnds (y : Fin (n+2) → ℤ) : ℤ × ℤ :=
  let v := (∑ i,y i)/2
  (v-y (Fin.last (n+1)),v)

private def forkInverse (y : Fin (n+2) → ℤ) : Fork n :=
  let uv := forkEnds y
  (integrate (adjust (fun i => y i.castSucc) (-(uv.1+uv.2))),uv)

/-- The fork coefficient lattice fills the entire integral even-sum lattice. -/
def forkCoordinates (n : ℕ) : Fork n ≃ {y : Fin (n+2) → ℤ // Even (∑ i,y i)} where
  toFun a := ⟨forkVector a,⟨a.2.2,by rw [sum_fork,two_mul]⟩⟩
  invFun y := forkInverse y.val
  left_inv a := by
    obtain ⟨a,u,v⟩ := a
    have ends : forkEnds (forkVector (a,u,v))=(u,v) := by
      unfold forkEnds
      rw [sum_fork]
      simp only [forkVector,Fin.snoc_last]
      apply Prod.ext <;> dsimp <;> omega
    change forkInverse (forkVector (a,u,v))=(a,u,v)
    simp only [forkInverse,ends]
    simp only [forkVector,Fin.snoc_castSucc,adjust_undo,integrate_boundary]
  right_inv y := by
    obtain ⟨y,k,hk⟩ := y
    let u := (forkEnds y).1
    let v := (forkEnds y).2
    have hv : v=k := by change (∑ i,y i)/2=k; omega
    have hu : u=v-y (Fin.last (n+1)) := rfl
    let z := fun i : Fin (n+1) => y i.castSucc
    have hz : (∑ i,z i)=k+k-y (Fin.last (n+1)) := by
      have e := hk
      rw [Fin.sum_univ_castSucc] at e
      change (∑ i,z i)+y (Fin.last (n+1))=k+k at e
      omega
    have hs : ∑ i,adjust z (-(u+v)) i=0 := by rw [sum_adjust,hz,hu,hv]; ring
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change snocℤ _ (v-u) (Fin.last (n+1))=_
      rw [Fin.snoc_last,hu]; ring
    · change snocℤ (adjust (boundary (integrate (adjust z (-(u+v))))) (u+v)) _ j.castSucc=_
      rw [Fin.snoc_castSucc,boundary_integrate _ hs]
      by_cases eq : j=Fin.last n
      · simp [adjust,eq,z]
        abel
      · simp [adjust,eq,z]

private def tip (a : Fin n → ℤ) := consℤ 0 a (Fin.last n)

def forkEnergy (a : Fork n) := pathEnergy a.1+a.2.1^2+a.2.2^2-tip a.1*(a.2.1+a.2.2)

private theorem energy_adjust (y : Fin (n+1) → ℤ) (c : ℤ) :
    energy (adjust y c)=energy y+2*y (Fin.last n)*c+c^2 := by
  unfold energy
  rw [Fin.sum_univ_castSucc (fun i => (adjust y c i)^2),Fin.sum_univ_castSucc (fun i => (y i)^2)]
  simp only [adjust,Fin.castSucc_ne_last,if_false,add_zero,if_true]
  ring

theorem fork_energy (a : Fork n) : energy (forkVector a)=2*forkEnergy a := by
  change (∑ i,(snocℤ (adjust (boundary a.1) (a.2.1+a.2.2)) (a.2.2-a.2.1) i)^2)=_
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]
  change energy (adjust (boundary a.1) (a.2.1+a.2.2))+(a.2.2-a.2.1)^2=_
  rw [energy_adjust,boundary_energy]
  simp only [boundary,Fin.snoc_last,zero_sub,tip,forkEnergy]
  ring

private theorem shell_even (y : TwoShell (Fin (n+2))) : Even (∑ i,y.val i) := by
  obtain ⟨k,h⟩ := IntegralZeroSum.energy_sub_sum_even y.val
  rw [y.property] at h
  exact ⟨1-k,by omega⟩

/-- Every signed pair occurs on the fork, including the equal-sign pairs. -/
def forkRootEquiv (n : ℕ) : {a : Fork n // forkEnergy a=1} ≃ TwoShell (Fin (n+2)) where
  toFun a := ⟨forkVector a.val,by rw [fork_energy,a.property]; norm_num⟩
  invFun y := ⟨(forkCoordinates n).symm ⟨y.val,shell_even y⟩,by
    let b := (forkCoordinates n).symm ⟨y.val,shell_even y⟩
    have hv : forkVector b=y.val := congrArg (fun z : {z : Fin (n+2) → ℤ // Even (∑ i,z i)} => z.val)
      ((forkCoordinates n).apply_symm_apply ⟨y.val,shell_even y⟩)
    have e := fork_energy b
    rw [hv,y.property] at e
    change forkEnergy b=1
    omega⟩
  left_inv a := Subtype.ext ((forkCoordinates n).symm_apply_apply a.val)
  right_inv y := Subtype.ext (congrArg (fun z : {z : Fin (n+2) → ℤ // Even (∑ i,z i)} => z.val)
    ((forkCoordinates n).apply_symm_apply ⟨y.val,shell_even y⟩))

theorem fork_root_count (n : ℕ) : Nat.card {a : Fork n // forkEnergy a=1}=4*(n+2).choose 2 := by
  rw [Nat.card_congr (forkRootEquiv n),card_twoShell,Fintype.card_fin]

/-- Contribution of a single arm, with its inner endpoint adjacent to
the prescribed center t. Coordinates start at the center's neighbor. -/
def armPiece (t : ℤ) (f : Fin n → ℤ) :=
  (∑ i,(f i)^2)-∑ i,f i*consℤ t f i.castSucc

private theorem pad_differences (t : ℤ) (f : Fin n → ℤ) :
    (∑ i : Fin (n+1), (snocℤ f 0 i-consℤ t f i)^2)=2*armPiece t f+t^2 := by
  have L : (∑ i : Fin (n+1), (snocℤ f 0 i)^2)=∑ i,(f i)^2 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc,Fin.snoc_last,zero_pow (by decide : 2≠0),add_zero]
  have R : (∑ i : Fin (n+1), (consℤ t f i)^2)=t^2+∑ i,(f i)^2 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_succ,Fin.cons_zero]
  have E : (∑ i : Fin (n+1), snocℤ f 0 i*consℤ t f i)=∑ i,f i*consℤ t f i.castSucc := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc,Fin.snoc_last,zero_mul,add_zero]
  simp only [armPiece,sub_sq,sum_add_distrib,sum_sub_distrib,mul_assoc,← mul_sum,L,R,E]
  ring

/-- The integral ramp has a constant difference on every edge, including
the final edge to the pinned exterior zero. -/
theorem ramp_piece (b : ℤ) :
    let t := ((n:ℤ)+1)*b
    let f := fun i : Fin n => t-((i.val:ℤ)+1)*b
    2*armPiece t f=((n:ℤ)+1)*b^2-t^2 := by
  intro t f
  have left (i : Fin (n+1)) : snocℤ f 0 i=t-((i.val:ℤ)+1)*b := by
    refine Fin.lastCases (by simp [t]) (fun j => ?_) i
    exact Fin.snoc_castSucc _ _ _
  have right (i : Fin (n+1)) : consℤ t f i=t-(i.val:ℤ)*b := by
    refine Fin.cases (by simp) (fun j => ?_) i
    simp [f]
  have h := pad_differences t f
  have eq (i : Fin (n+1)) : snocℤ f 0 i-consℤ t f i= -b := by rw [left,right]; ring
  simp only [eq,neg_sq,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at h
  linarith only [h]

/-- Adjoining the center as the first coordinate turns an arm into an
ordinary path. -/
theorem path_cons_arm (t : ℤ) (f : Fin n → ℤ) :
    pathEnergy (consℤ t f)=t^2+armPiece t f := by
  rw [←path_parent_energy,Fin.sum_univ_succ (fun i => (consℤ t f i)^2),
    Fin.sum_univ_succ (fun i => (previous i).elim 0 (fun j => consℤ t f i*consℤ t f j))]
  simp only [Fin.cons_zero,Fin.cons_succ]
  have zero : previous (0 : Fin (n+1))=none := by simp [previous]
  have succ (i : Fin n) : previous i.succ=some i.castSucc :=
    (previous_eq i.succ i.castSucc).mpr rfl
  simp only [zero,succ,Option.elim,armPiece,sub_eq_add_neg,zero_add]
  ring

/-- Reversal commutes with path energy because it reverses and negates
the entire boundary-difference vector. -/
theorem path_reversal (f : Fin n → ℤ) : pathEnergy (fun i => f i.rev)=pathEnergy f := by
  have L (i : Fin (n+1)) : snocℤ (fun j => f j.rev) 0 i=consℤ 0 f i.rev :=
    (Fin.cons_rev 0 f i).symm
  have R (i : Fin (n+1)) : consℤ 0 (fun j => f j.rev) i=snocℤ f 0 i.rev :=
    (Fin.snoc_rev 0 f i).symm
  have e (i : Fin (n+1)) : boundary (fun j => f j.rev) i= -boundary f i.rev := by
    rw [boundary,L,R,boundary,neg_sub]
  have energyEq : energy (boundary (fun i => f i.rev))=energy (boundary f) := by
    simp only [energy,e,neg_sq]
    simpa only [Fin.revPerm_apply] using Equiv.sum_comp (Fin.revPerm (n:=n+1))
      (fun i : Fin (n+1) => (boundary f i)^2)
  rw [boundary_energy,boundary_energy] at energyEq
  omega

/-- By reversing the trunk, the two leaves can equally be attached at
its first coordinate. -/
theorem fork_head_energy (g : Fin (n+1) → ℤ) (u v : ℤ) :
    forkEnergy (fun i => g i.rev,u,v)=pathEnergy g+u^2+v^2-g 0*(u+v) := by
  simp only [forkEnergy,path_reversal,tip,Fin.cons_last,Fin.rev_last]


#print axioms ramp_piece
#print axioms fork_head_energy
#print axioms pathCoordinates
#print axioms path_root_count
#print axioms forkCoordinates
#print axioms fork_root_count
end GaloisForLFunctions.HTGeometry.ClassicalCartan
