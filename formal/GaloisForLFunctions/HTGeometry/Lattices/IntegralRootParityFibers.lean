import GaloisForLFunctions.HTGeometry.Lattices.CubicRootLineBound

/-!
# The two sheets of the binary root image

Each occupied parity class of an integral positive quadratic form contains
exactly two norm-one vectors. Choosing one lift per class identifies the
root shell with its binary image times a sign. The cardinal bound for cubic
interpolation consequently bounds the entire shell, including rank zero.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.IntegralRootShell
variable {J : Type*}

abbrev Occupied (Q : Form J) := Set.range (fun x : Root Q => parity x.val)

def lift (Q : Form J) (a : Occupied Q) : Root Q := a.property.choose

theorem parity_lift (Q : Form J) (a : Occupied Q) : parity (lift Q a).val=a.val :=
  a.property.choose_spec

def antipode (Q : Form J) (x : Root Q) : Root Q := ⟨-x.val,by rw [Q.map_neg,x.property]⟩

private theorem antipode_ne (Q : Form J) (x : Root Q) : antipode Q x≠x := by
  intro e
  have he : x.val=0 := by
    funext i
    have h := congrArg (fun z : Root Q => z.val i) e
    change -x.val i=x.val i at h
    change x.val i=0
    omega
  have h := x.property
  rw [he,Q.map_zero] at h
  exact zero_ne_one h

private theorem antipode_parity (Q : Form J) (hQ : Q.PosDef) (x : Root Q) :
    parity (antipode Q x).val=parity x.val :=
  (root_parity_iff Q hQ _ _).mpr (Or.inr rfl)

/-- A Boolean sign and an occupied binary class parametrize the whole root shell. -/
def parityEquiv (Q : Form J) (hQ : Q.PosDef) : Occupied Q × Bool ≃ Root Q := by
  classical
  let f (p : Occupied Q × Bool) := if p.2 then antipode Q (lift Q p.1) else lift Q p.1
  have key (a : Occupied Q) (b : Bool) : parity (f (a,b)).val=a.val := by
    cases b <;> simp only [f,Bool.false_eq_true,if_false,if_true,antipode_parity Q hQ,parity_lift]
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨a,b⟩ ⟨c,d⟩ e
    have h : a=c := Subtype.ext ((key a b).symm.trans
      ((congrArg (fun x : Root Q => parity x.val) e).trans (key c d)))
    subst c
    cases b <;> cases d
    · rfl
    · exact (antipode_ne Q _ e.symm).elim
    · exact (antipode_ne Q _ e).elim
    · rfl
  · intro x
    let a : Occupied Q := ⟨parity x.val,x,rfl⟩
    rcases (root_parity_iff Q hQ (lift Q a) x).mp (parity_lift Q a) with e|e
    · exact ⟨(a,false),Subtype.ext e⟩
    · exact ⟨(a,true),Subtype.ext (by change -(lift Q a).val=x.val; rw [e,neg_neg])⟩

variable [Fintype J]

theorem card_roots (Q : Form J) (hQ : Q.PosDef) :
    Nat.card (Root Q)=2*Nat.card (Occupied Q) := by
  classical
  letI : Finite (Occupied Q) := inferInstanceAs (Finite (Set.range (fun x : Root Q => parity x.val)))
  rw [← Nat.card_congr (parityEquiv Q hQ),Nat.card_prod,
    Nat.card_eq_fintype_card (α:=Bool),Fintype.card_bool,Nat.mul_comm]

/-- The sharp symmetric-cube bound applies to the actual binary image. -/
theorem occupied_card_le (Q : Form J) (hQ : Q.PosDef) :
    Nat.card (Occupied Q) ≤ (Fintype.card J+2).choose 3 := by
  classical
  letI := Fintype.ofFinite (Occupied Q)
  rw [Nat.card_eq_fintype_card]
  apply cubic_line_bound Q hQ (lift Q)
  intro a b h
  exact Subtype.ext ((parity_lift Q a).symm.trans
    (((root_parity_iff Q hQ _ _).mpr h).trans (parity_lift Q b)))

theorem root_card_le (Q : Form J) (hQ : Q.PosDef) :
    Nat.card (Root Q) ≤ 2*(Fintype.card J+2).choose 3 := by
  rw [card_roots Q hQ]
  exact Nat.mul_le_mul_left 2 (occupied_card_le Q hQ)

#print axioms parityEquiv
#print axioms card_roots
#print axioms root_card_le
end GaloisForLFunctions.HTGeometry.IntegralRootShell
