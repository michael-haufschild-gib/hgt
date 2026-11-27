import Mathlib

/-! # Ordered displacements and their sign changes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Upper

open Finset Set

variable {n : ℕ}

/-- Zero displacements may receive either sign. The same convention is used at both ends. -/
def side (A B : Fin (n+1) → ℝ) (i : Fin (n+1)) : ℝ := if B i < A i then 1 else -1

def edges (A B : Fin (n+1) → ℝ) :=
  univ.filter fun j : Fin n => side A B j.castSucc ≠ side A B j.succ

def top (A B : Fin (n+1) → ℝ) (i : Fin (n+1)) := max (A i) (B i)

theorem top_mono {A B : Fin (n+1) → ℝ} (ha : StrictMono A) (hb : StrictMono B) :
    StrictMono (top A B) := by
  intro i j h
  exact max_lt ((ha h).trans_le (le_max_left _ _)) ((hb h).trans_le (le_max_right _ _))

theorem side_sq (A B : Fin (n+1) → ℝ) (i : Fin (n+1)) : side A B i*side A B i=1 := by
  unfold side; split <;> simp

private theorem side_ne {A B : Fin (n+1) → ℝ} {i j : Fin (n+1)}
    (h : side A B i ≠ side A B j) : side A B i*side A B j= -1 := by
  unfold side at h ⊢
  split_ifs at h ⊢ <;> simp_all

/-- Between opposite orientations, both ordered lists leave a common cut. -/
private theorem gap {A B : Fin (n+1) → ℝ} (ha : Monotone A) (hb : Monotone B)
    (j : Fin n) (h : side A B j.castSucc ≠ side A B j.succ) :
    top A B j.castSucc ≤ min (A j.succ) (B j.succ) := by
  by_cases l : B j.castSucc < A j.castSucc
  · have r : ¬B j.succ < A j.succ := fun hr => h (by simp only [side,l,hr,if_true])
    rw [top,max_eq_left l.le,min_eq_left (le_of_not_gt r)]
    exact ha (Fin.castSucc_lt_succ.le)
  · have r : B j.succ < A j.succ := by
      by_contra hr
      exact h (by simp only [side,l,hr,if_false])
    rw [top,max_eq_right (le_of_not_gt l),min_eq_right r.le]
    exact hb (Fin.castSucc_lt_succ.le)

private def weight (s : Fin (n+1) → ℝ) (i : Fin (n+1)) (j : Fin n) :=
  if j.val < i.val then s j.castSucc*s j.succ else 1

/-- Each intermediate orientation occurs twice in the prefix product. -/
private theorem prefix_product (s : Fin (n+1) → ℝ) (sq : ∀ i, s i*s i=1) (i : Fin (n+1)) :
    (∏ j, weight s i j)=s 0*s i := by
  induction i using Fin.induction with
  | zero => simp [weight,sq]
  | succ i ih =>
    have upd (j : Fin n) : weight s i.succ j=weight s i.castSucc j*
        (if j=i then s i.castSucc*s i.succ else 1) := by
      by_cases eq : j=i
      · subst j; simp [weight]
      · have test : (j.val < i.val+1) ↔ j.val < i.val := by
          have h := fun e => eq (Fin.ext e); omega
        simp only [weight,Fin.val_succ,Fin.val_castSucc,test,eq,if_false,mul_one]
        split_ifs <;> rfl
    simp only [upd,prod_mul_distrib,Finset.prod_ite_eq',Finset.mem_univ,if_true,ih]
    calc
      _ = s 0*(s i.castSucc*s i.castSucc)*s i.succ := by ring
      _ = _ := by rw [sq,mul_one]

/-- Everywhere strictly between the two endpoints of a displacement, the cut
polynomial has its orientation up to the single overall sign of the first index. -/
theorem cut_sign {A B : Fin (n+1) → ℝ} (ha : StrictMono A) (hb : StrictMono B)
    (i : Fin (n+1)) {x : ℝ} (hx : x∈Ioo (min (A i) (B i)) (top A B i)) :
    0 < (side A B 0*side A B i)*∏ j ∈ edges A B, (top A B j.castSucc-x) := by
  let s := side A B
  let f (j : Fin n) := if s j.castSucc ≠ s j.succ then top A B j.castSucc-x else 1
  have pos (j : Fin n) : 0 < weight s i j*f j := by
    by_cases flip : s j.castSucc ≠ s j.succ
    · rw [show f j=top A B j.castSucc-x from if_pos flip]
      by_cases lt : j.val < i.val
      · have ord : j.succ ≤ i := lt
        have bound := (gap ha.monotone hb.monotone j flip).trans
          (min_le_min (ha.monotone ord) (hb.monotone ord))
        exact (show 0 < weight s i j*(top A B j.castSucc-x) by
          rw [weight,if_pos lt,show s j.castSucc*s j.succ= -1 from side_ne flip,neg_one_mul,neg_pos]
          exact sub_neg.mpr (bound.trans_lt hx.1))
      · have ord : i ≤ j.castSucc := le_of_not_gt lt
        rw [weight,if_neg lt,one_mul]
        exact sub_pos.mpr (hx.2.trans_le ((top_mono ha hb).monotone ord))
    · have eq := not_ne_iff.mp flip
      rw [show f j=1 from if_neg flip,mul_one]
      simp only [weight,eq,show s j.succ*s j.succ=1 from side_sq A B _,ite_self,zero_lt_one]
  have product := prod_pos (s := univ) fun j _ => pos j
  rw [prod_mul_distrib,prefix_product s (side_sq A B)] at product
  simpa only [edges,prod_filter,f,s] using product

#print axioms cut_sign

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Upper
