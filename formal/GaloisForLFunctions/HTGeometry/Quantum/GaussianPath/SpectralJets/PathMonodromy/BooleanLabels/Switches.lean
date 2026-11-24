import GaloisForLFunctions.HTGeometry.BooleanHypercubeTranspositionLaw

/-! # Controlled flips of Boolean eigenvalue labels -/

open Finset Equiv
namespace GaloisForLFunctions.HTGeometry.PathMonodromy.BooleanLabels
noncomputable section
variable {I : Type*} [DecidableEq I]

/-- The Boolean product of the control bits. -/
def active (S : Finset I) (x : I→Bool) : Bool := decide (∀ i∈S, x i=true)

theorem active_insert (i : I) (S : Finset I) (x : I→Bool) :
    active (insert i S) x = (x i && active S x) := by
  cases h : x i <;> simp [active,h]

theorem active_singleton (i : I) (x : I→Bool) : active {i} x=x i := by
  cases h : x i <;> simp [active,h]

private def changeBit (S : Finset I) (p : I) (x : I→Bool) (i : I) : Bool :=
  if i=p then x i ^^ active S x else x i

private theorem active_change {T : Finset I} {p : I} (hp : p∉T)
    (S : Finset I) (x : I→Bool) : active T (changeBit S p x)=active T x := by
  unfold active
  apply decide_eq_decide.mpr
  exact forall_congr' fun i => forall_congr' fun hi => by
    simp only [changeBit,if_neg (ne_of_mem_of_not_mem hi hp)]

private theorem twice (S : Finset I) {p : I} (hp : p∉S) (x : I→Bool) :
    changeBit S p (changeBit S p x)=x := by
  funext i
  by_cases he : i=p
  · subst i
    rw [changeBit,if_pos rfl,active_change hp,changeBit,if_pos rfl]
    cases x p <;> cases active S x <;> rfl
  simp only [changeBit,if_neg he]

/-- Flip a specified bit if all prescribed control bits are one. -/
def flip (S : Finset I) (p : I) (hp : p∉S) : Perm (I→Bool) where
  toFun := changeBit S p
  invFun := changeBit S p
  left_inv := twice S hp
  right_inv := twice S hp

theorem flip_self (S : Finset I) (p : I) (hp : p∉S) (x : I→Bool) :
    flip S p hp x p=x p ^^ active S x := if_pos rfl

theorem flip_other (S : Finset I) {p i : I} (hp : p∉S) (hi : i≠p) (x : I→Bool) :
    flip S p hp x i=x i := if_neg hi

theorem active_flip {T : Finset I} {p : I} (hp : p∉T)
    (S : Finset I) (hs : p∉S) (x : I→Bool) :
    active T (flip S p hs x)=active T x := active_change hp S x

end
end GaloisForLFunctions.HTGeometry.PathMonodromy.BooleanLabels
