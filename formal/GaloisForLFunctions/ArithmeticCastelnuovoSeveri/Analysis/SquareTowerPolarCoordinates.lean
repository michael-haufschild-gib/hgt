import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Integral fibers of two reciprocal polynomial readings

Synthetic division at b writes P=A+(X−b)R. Applying it again to the
reversed coefficient list of R gives integral coordinates (A,k,z).
For degree at most d, the readings P(b) and bᵈP(1/b) are A and
bᵈA+(1−b²)k. The remaining d−1 coefficients vary freely over ℤ.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SquareTower
open Finset

abbrev Coeff (n : ℕ) := Fin n → ℤ
abbrev Base := {b : ℕ // 2≤b}

def forward {n : ℕ} (b : ℤ) (x : Coeff n) := ∑ i, x i*b^i.val
def backward {n : ℕ} (b : ℤ) (x : Coeff n) := ∑ i, x i*b^i.rev.val

private theorem forward_cons {n : ℕ} (b u : ℤ) (x : Coeff n) :
    forward b (Fin.cons u x)=u+b*forward b x := by
  unfold forward
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.val_zero,pow_zero,mul_one,Fin.cons_succ,Fin.val_succ,pow_succ,mul_sum]
  exact congrArg (u+·) (sum_congr rfl fun i _ => by ring)

private theorem backward_cons {n : ℕ} (b u : ℤ) (x : Coeff n) :
    backward b (Fin.cons u x)=u*b^n+backward b x := by
  unfold backward
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.rev_zero,Fin.val_last,Fin.cons_succ,Fin.rev_succ,Fin.val_castSucc]

private def pack (b : ℤ) (n : ℕ) : ℤ × (ℤ × Coeff n) ≃ ℤ × Coeff (n+1) where
  toFun z := (z.1+b*z.2.1,Fin.cons z.2.1 z.2.2)
  invFun z := (z.1-b*z.2 0,(z.2 0,Fin.tail z.2))
  left_inv := by rintro ⟨u,v,w⟩; simp
  right_inv := by rintro ⟨u,v⟩; simp

/-- Synthetic division records the remainder at b and the coefficients
of the quotient by X−b. All operations preserve the integer lattice. -/
private def division (b : ℤ) : (n : ℕ) → Coeff (n+1) ≃ ℤ × Coeff n
  | 0 => (Fin.consEquiv (fun _ : Fin 1 => ℤ)).symm
  | n+1 => (Fin.consEquiv (fun _ : Fin (n+2) => ℤ)).symm.trans
      (((Equiv.refl ℤ).prodCongr (division b n)).trans (pack b n))

private theorem division_values (b : ℤ) (n : ℕ) (x : Coeff (n+1)) :
    let z := division b n x
    forward b x=z.1 ∧ backward b x=z.1*b^n+(1-b^2)*backward b z.2 := by
  induction n with
  | zero =>
    simp [division,forward,backward,Fin.consEquiv]
  | succ n ih =>
    let T := division b n (Fin.tail x)
    have h : forward b (Fin.tail x)=T.1 ∧
        backward b (Fin.tail x)=T.1*b^n+(1-b^2)*backward b T.2 := ih (Fin.tail x)
    have f := forward_cons b (x 0) (Fin.tail x)
    have g := backward_cons b (x 0) (Fin.tail x)
    rw [Fin.cons_self_tail] at f g
    change forward b x=x 0+b*T.1 ∧ backward b x=(x 0+b*T.1)*b^(n+1)+(1-b^2)*backward b (Fin.cons T.1 T.2)
    constructor
    · rw [f,h.1]
    · rw [g,h.2,backward_cons,pow_succ]
      ring

private def reverse (n : ℕ) : Coeff n ≃ Coeff n where
  toFun x i := x i.rev
  invFun x i := x i.rev
  left_inv x := funext fun i => congrArg x (Fin.rev_rev i)
  right_inv x := funext fun i => congrArg x (Fin.rev_rev i)

private theorem forward_reverse {n : ℕ} (b : ℤ) (x : Coeff n) : forward b (reverse n x)=backward b x := by
  have h := Equiv.sum_comp Fin.revPerm (fun i : Fin n => x i*b^i.rev.val)
  change (∑ i : Fin n, x i.rev*b^i.rev.rev.val)=_ at h
  change (∑ i : Fin n, x i.rev*b^i.val) = ∑ i : Fin n, x i*b^i.rev.val
  simpa only [Fin.rev_rev] using h

/-- Both reciprocal readings in degree at most n+1 use only the first two
coordinates of this integral change of basis. -/
def coordinates (b : ℤ) (n : ℕ) : Coeff (n+2) ≃ ℤ × (ℤ × Coeff n) :=
  (division b (n+1)).trans ((Equiv.refl ℤ).prodCongr ((reverse (n+1)).trans (division b n)))

theorem coordinates_readings (b : ℤ) (n : ℕ) (x : Coeff (n+2)) :
    let z := coordinates b n x
    forward b x=z.1 ∧ backward b x=z.1*b^(n+1)+(1-b^2)*z.2.1 := by
  let T := division b (n+1) x
  have top := division_values b (n+1) x
  have bot := (division_values b n (reverse (n+1) T.2)).1
  change forward b x=T.1 ∧ backward b x=T.1*b^(n+1)+(1-b^2)*(division b n (reverse (n+1) T.2)).1
  rw [←bot,forward_reverse]
  exact top

theorem endpoint_congruence (b : ℤ) (d : ℕ) (x : Coeff (d+1)) :
    ∃ k : ℤ, backward b x=forward b x*b^d+(1-b^2)*k := by
  obtain ⟨f,g⟩ := division_values b d x
  exact ⟨_,by rwa [f]⟩

/-- Every pair satisfying the endpoint congruence occurs at every positive
degree bound. This includes composite bases. -/
theorem attainable_pair (b : ℤ) (n : ℕ) (a c : ℤ) :
    (∃ x : Coeff (n+2), forward b x=a ∧ backward b x=c) ↔
      ∃ k : ℤ, c=a*b^(n+1)+(1-b^2)*k := by
  constructor
  · rintro ⟨x,rfl,rfl⟩
    exact endpoint_congruence b (n+1) x
  · rintro ⟨k,rfl⟩
    let e := coordinates b n
    let x := e.symm (a,k,0)
    exact ⟨x,by simpa only [x,e,Equiv.apply_symm_apply] using coordinates_readings b n x⟩

private theorem multiplier_ne (b : Base) : 1-(b.val:ℤ)^2≠0 := by
  have h : (2:ℤ)≤b.val := by exact_mod_cast b.property
  nlinarith only [h,sq_nonneg ((b.val:ℤ)-2)]

private theorem same_coordinates (b : Base) {n : ℕ} (x y : Coeff (n+2)) :
    let e := coordinates (b.val:ℤ) n
    (forward b.val x=forward b.val y ∧ backward b.val x=backward b.val y) ↔
      ((e x).1=(e y).1 ∧ (e x).2.1=(e y).2.1) := by
  intro e
  obtain ⟨hx,rx⟩ := coordinates_readings b.val n x
  obtain ⟨hy,ry⟩ := coordinates_readings b.val n y
  rw [hx,hy,rx,ry]
  constructor
  · rintro ⟨h,k⟩
    rw [h] at k
    exact ⟨h,mul_left_cancel₀ (multiplier_ne b) (add_left_cancel k)⟩
  · rintro ⟨h,k⟩
    exact ⟨h,by change (e x).1*_+_*(e x).2.1=(e y).1*_+_*(e y).2.1; rw [h,k]⟩

/-- Ordered integral factorizations satisfying the endpoint congruence. -/
def Admissible (b : ℤ) (d : ℕ) (N : ℤ) :=
  {u : ℤ × ℤ // u.1*u.2=N ∧ ∃ k : ℤ, u.2=u.1*b^d+(1-b^2)*k}

/-- A full integral level set splits into its admissible factorizations
and n free integer coefficients. The fiber description includes level zero. -/
noncomputable def levelEquiv (b : Base) (n : ℕ) (N : ℤ) :
    {x : Coeff (n+2) // forward b.val x*backward b.val x=N} ≃ Admissible b.val (n+1) N × Coeff n := by
  let e := coordinates (b.val:ℤ) n
  let f (x : {x : Coeff (n+2) // forward b.val x*backward b.val x=N}) :
      Admissible b.val (n+1) N × Coeff n :=
    (⟨(forward b.val x.val,backward b.val x.val),x.property,endpoint_congruence b.val _ x.val⟩,(e x.val).2.2)
  apply Equiv.ofBijective f
  constructor
  · intro x y eq
    have endpoints := (same_coordinates b x.val y.val).mp
      ⟨congrArg (fun z : Admissible b.val (n+1) N × Coeff n => z.1.val.1) eq,
       congrArg (fun z : Admissible b.val (n+1) N × Coeff n => z.1.val.2) eq⟩
    have tail := congrArg (fun z : Admissible b.val (n+1) N × Coeff n => z.2) eq
    exact Subtype.ext (e.injective (Prod.ext endpoints.1 (Prod.ext endpoints.2 tail)))
  · rintro ⟨⟨⟨a,c⟩,ac,k,hk⟩,v⟩
    let x := e.symm (a,k,v)
    have he : e x=(a,k,v) := e.apply_symm_apply _
    have h : forward b.val x=a ∧ backward b.val x=c := by
      obtain ⟨u,w⟩ := coordinates_readings b.val n x
      change forward b.val x=(e x).1 at u
      change backward b.val x=(e x).1*_+_*(e x).2.1 at w
      rw [he] at u w
      exact ⟨u,w.trans hk.symm⟩
    let z : {x : Coeff (n+2) // forward b.val x*backward b.val x=N} := ⟨x,by rw [h.1,h.2]; exact ac⟩
    exact ⟨z,Prod.ext (Subtype.ext (Prod.ext h.1 h.2)) (congrArg (fun t : ℤ × ℤ × Coeff n => t.2.2) he)⟩

#print axioms coordinates_readings
#print axioms attainable_pair
#print axioms levelEquiv
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SquareTower
