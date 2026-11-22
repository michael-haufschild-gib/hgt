import GaloisForLFunctions.HTGeometry.HaferkampExactCircuitComplexity

/-! # A circuit cut separating many bonds of the physical path -/
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
noncomputable section

variable {n : ℕ}
private abbrev Config (n : ℕ) := Fin (n+1) → Bool

private def parity {V : Type*} (x : V→Bool) (a b : V) := xor (x a) (x b)

private def gateCode (C : TwoQubitCircuit (n+1)) (x : Config n) : Fin C.gateCount→Bool :=
  fun i => parity x (C.architecture.sites i).1 (C.architecture.sites i).2

/-- Colorings for which no gate joins the two color classes. -/
def Cut (C : TwoQubitCircuit (n+1)) := {x : Config n // gateCode C x=(fun _ => false)}

private def plus (x y : Config n) : Config n := fun j => xor (x j) (y j)

private theorem parity_plus (x y : Config n) (a b : Fin (n+1)) :
    parity (plus x y) a b=xor (parity x a b) (parity y a b) := by
  have swap (p q r s : Bool) : xor (xor p q) (xor r s)=xor (xor p r) (xor q s) := by
    cases p <;> cases q <;> cases r <;> cases s <;> rfl
  exact swap .. 

private theorem cut_plus {C : TwoQubitCircuit (n+1)} (x y : Cut C) :
    gateCode C (plus x.val y.val)=(fun _ => false) := by
  funext i
  exact (parity_plus ..).trans (by change xor (gateCode C x.val i) (gateCode C y.val i)=false; rw [x.2,y.2]; rfl)

private instance (C : TwoQubitCircuit (n+1)) : Fintype (Cut C) := by
  unfold Cut
  exact Fintype.ofFinite _
private instance (C : TwoQubitCircuit (n+1)) : Nonempty (Cut C) :=
  ⟨⟨fun _ => false,rfl⟩⟩

/-- A bond is flexible when some circuit cut crosses it. -/
def flexible (C : TwoQubitCircuit (n+1)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ∃ x : Cut C, parity x.val i.castSucc i.succ=true

private theorem gate_fiber {C : TwoQubitCircuit (n+1)} (x y : Config n) (h : gateCode C x=gateCode C y) :
    gateCode C (plus x y)=(fun _ => false) := by
  funext i
  rw [gateCode,parity_plus]
  change xor (gateCode C x i) (gateCode C y i)=false
  rw [h]; cases gateCode C y i <;> rfl

/-- The gate parities determine at most one bit per gate. All other
degrees of freedom are present among the path bond parities and a
single reference bit. -/
theorem flexible_card (C : TwoQubitCircuit (n+1)) : n ≤ C.gateCount+(flexible C).card := by
  classical
  let rep (b : Fin C.gateCount→Bool) : Config n :=
    if h : ∃ x, gateCode C x=b then h.choose else fun _ => false
  have hrep (x : Config n) : gateCode C (rep (gateCode C x))=gateCode C x := by
    have hx : ∃ y, gateCode C y=gateCode C x := ⟨x,rfl⟩
    simpa only [rep,dif_pos hx] using hx.choose_spec
  let diff (x : Config n) : Cut C := ⟨plus x (rep (gateCode C x)),gate_fiber _ _ (hrep x).symm⟩
  let code (x : Config n) := (gateCode C x,(diff x).val 0,
    fun i : flexible C => parity (diff x).val i.val.castSucc i.val.succ)
  have hinj : Function.Injective code := by
    intro x y h
    have hc : gateCode C x=gateCode C y := congrArg Prod.fst h
    have hr : (diff x).val 0=(diff y).val 0 := congrArg (fun z => z.2.1) h
    have he (i : Fin n) : parity (diff x).val i.castSucc i.succ=parity (diff y).val i.castSucc i.succ := by
      by_cases hi : i∈flexible C
      · exact congrArg (fun z => z.2.2 ⟨i,hi⟩) h
      · have ha (u : Cut C) : parity u.val i.castSucc i.succ=false := by
          cases hh : parity u.val i.castSucc i.succ with
          | false => rfl
          | true => exact (hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,hh⟩)).elim
        rw [ha,ha]
    have hd (j : Fin (n+1)) : (diff x).val j=(diff y).val j := by
      induction j using Fin.induction with
      | zero => exact hr
      | succ i ih =>
        have hh := he i
        unfold parity at hh
        rw [ih] at hh
        have cancel (a b c : Bool) : xor a b=xor a c → b=c := by
          cases a <;> cases b <;> cases c <;> simp
        exact cancel _ _ _ hh
    funext j
    have hh := hd j
    change xor (x j) (rep (gateCode C x) j)=xor (y j) (rep (gateCode C y) j) at hh
    rw [hc] at hh
    have cancel (a b c : Bool) : xor b a=xor c a → b=c := by
      cases a <;> cases b <;> cases c <;> simp
    exact cancel _ _ _ hh
  have h := Fintype.card_le_of_injective code hinj
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Fintype.card_prod,Fintype.card_coe] at h
  by_contra! hh
  have hp := Nat.pow_lt_pow_right (by decide : 1<2) (show C.gateCount+(flexible C).card+1<n+1 by omega)
  rw [pow_succ,pow_add] at hp
  exact hp.not_ge (by simpa only [Config,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,
    Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h)

/-- The set of physical bonds cut by this gate-respecting coloring. -/
def crossed {C : TwoQubitCircuit (n+1)} (x : Cut C) : Finset (Fin n) :=
  Finset.univ.filter fun i => parity x.val i.castSucc i.succ=true

theorem Cut.gate_agrees {C : TwoQubitCircuit (n+1)} (x : Cut C) (i : Fin C.gateCount) :
    x.val (C.architecture.sites i).1 = x.val (C.architecture.sites i).2 := by
  have hh := congrFun x.property i
  have eq_of_zero (a b : Bool) : xor a b=false → a=b := by cases a <;> cases b <;> simp
  exact eq_of_zero _ _ hh

theorem mem_crossed_iff {C : TwoQubitCircuit (n+1)} (x : Cut C) (i : Fin n) :
    i∈crossed x ↔ x.val i.castSucc ≠ x.val i.succ := by
  simp only [crossed,Finset.mem_filter,Finset.mem_univ,true_and,parity]
  cases x.val i.castSucc <;> cases x.val i.succ <;> simp

/-- Toggling a witness cut pairs the two parity classes at each flexible
edge. Some single cut therefore crosses at least half the flexible edges. -/
theorem many_crossed (C : TwoQubitCircuit (n+1)) :
    ∃ x : Cut C, n ≤ C.gateCount+2*(crossed x).card := by
  classical
  let F := flexible C
  let cuts := Finset.univ (α:=Cut C)
  have half (i : Fin n) (hi : i∈F) :
      cuts.card=2*(cuts.filter fun x => i∈crossed x).card := by
    obtain ⟨w,hw⟩ := (Finset.mem_filter.mp hi).2
    let T (x : Cut C) : Cut C := ⟨plus x.val w.val,cut_plus x w⟩
    have inv (x : Cut C) : T (T x)=x := by
      apply Subtype.ext; funext j
      change xor (xor (x.val j) (w.val j)) (w.val j)=x.val j
      cases x.val j <;> cases w.val j <;> rfl
    have flip (x : Cut C) : i∈crossed (T x) ↔ i∉crossed x := by
      simp only [crossed,Finset.mem_filter,Finset.mem_univ,true_and]
      change parity (plus x.val w.val) _ _=true ↔ _
      rw [parity_plus,hw]; cases parity x.val i.castSucc i.succ <;> simp
    have hbij : (cuts.filter fun x => i∉crossed x).card=(cuts.filter fun x => i∈crossed x).card := by
      apply Finset.card_bij (fun x _ => T x)
      · intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(flip x).mpr (Finset.mem_filter.mp hx).2⟩
      · intro x _ y _ h; exact (inv x).symm.trans ((congrArg T h).trans (inv y))
      · intro y hy
        refine ⟨T y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,inv y⟩
        exact fun h => (flip y).mp h (Finset.mem_filter.mp hy).2
    have hsum := Finset.card_filter_add_card_filter_not (s:=cuts) (fun x => i∈crossed x)
    omega
  obtain ⟨x,hx,hmax⟩ := cuts.exists_max_image (fun x => (crossed x).card) Finset.univ_nonempty
  refine ⟨x,(flexible_card C).trans (Nat.add_le_add_left ?_ _)⟩
  have hcount (y : Cut C) : (F.filter fun i => i∈crossed y).card=(crossed y).card := by
    congr 1
    ext i
    rw [Finset.mem_filter,and_iff_right_iff_imp]
    exact fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,(Finset.mem_filter.mp h).2⟩
  have hsum : F.card*cuts.card ≤ cuts.card*(2*(crossed x).card) := by
    calc _ = ∑ i ∈ F, cuts.card := by simp
         _ = ∑ i ∈ F, 2*(cuts.filter fun y => i∈crossed y).card := Finset.sum_congr rfl half
         _ = ∑ y ∈ cuts, 2*(F.filter fun i => i∈crossed y).card := by
               simp only [Finset.card_filter,Finset.mul_sum]; rw [Finset.sum_comm]
         _ ≤ ∑ _y ∈ cuts, 2*(crossed x).card := Finset.sum_le_sum fun y hy => by
               rw [hcount]; exact Nat.mul_le_mul_left 2 (hmax y hy)
         _ = _ := by simp
  rw [Nat.mul_comm F.card] at hsum
  exact Nat.le_of_mul_le_mul_left hsum (Finset.card_pos.mpr Finset.univ_nonempty)

#print axioms many_crossed
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
