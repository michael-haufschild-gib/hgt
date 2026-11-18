import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Reflection of binomial carries at an ordinary prime

A binomial carry at a nonzero residue and its negative has constant
sum, including at primes dividing the slopes or their sum. For the last
quotient class this reflected sum instead takes both values zero and one.
Pairing residues gives sharp absolute-error and one-sided bounds.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- First-level carry for the two summands at residue `x`. -/
def binomialResidueCarry {p : ℕ} (u v x : ZMod p) : ℝ :=
  if p ≤ (u*x).val+(v*x).val then 1 else 0

/-- This carry is the difference of the three factorial exponents at the prime level. -/
theorem binomialResidueCarry_natCast {p : ℕ} (hp : 0 < p) (a b n : ℕ) :
    binomialResidueCarry (p := p) a b n =
      ((((a*n+b*n)/p : ℕ) : ℝ)-((a*n/p : ℕ) : ℝ)-((b*n/p : ℕ) : ℝ)) := by
  rw [binomialResidueCarry,← Nat.cast_mul,← Nat.cast_mul,ZMod.val_natCast,ZMod.val_natCast,
    Nat.add_div hp]
  split <;> push_cast <;> ring

/-- Reflected multiplicity of a residue slope. -/
def nonzeroSlope {p : ℕ} (u : ZMod p) : ℝ := if u=0 then 0 else 1

private theorem val_reflect {p : ℕ} [Fact p.Prime] (u : ZMod p) {x : ZMod p} (hx : x ≠ 0) :
    ((u*x).val : ℝ) + (u*(-x)).val = p*nonzeroSlope u := by
  by_cases hu : u=0
  · simp [hu,nonzeroSlope]
  letI : NeZero (u*x) := ⟨mul_ne_zero hu hx⟩
  rw [mul_neg,ZMod.val_neg_of_ne_zero,Nat.cast_sub (u*x).val_lt.le,
    nonzeroSlope,if_neg hu,mul_one]
  ring

private theorem carry_val_identity {p : ℕ} [NeZero p] (u v x : ZMod p) :
    (p:ℝ)*binomialResidueCarry u v x =
      (u*x).val+(v*x).val-(((u+v)*x).val:ℝ) := by
  rw [binomialResidueCarry,add_mul]
  split
  next h =>
    have he := ZMod.val_add_val_of_le h
    rw [mul_one]
    have hR : ((u*x).val:ℝ)+(v*x).val = (u*x+v*x).val+(p:ℝ) := by exact_mod_cast he
    linarith only [hR]
  next h =>
    rw [ZMod.val_add_of_lt (lt_of_not_ge h),Nat.cast_add,mul_zero,sub_self]

/-- Complementing the residue gives constant total carry. The three possible
values count the nonzero input slopes minus the nonzero output slope. -/
theorem binomialResidueCarry_reflect {p : ℕ} [Fact p.Prime] (u v : ZMod p)
    {x : ZMod p} (hx : x ≠ 0) :
    binomialResidueCarry u v x + binomialResidueCarry u v (-x) =
      nonzeroSlope u+nonzeroSlope v-nonzeroSlope (u+v) := by
  have hp : (p:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply mul_left_cancel₀ hp
  rw [mul_add,carry_val_identity,carry_val_identity]
  linear_combination val_reflect u hx + val_reflect v hx - val_reflect (u+v) hx

/-- A finite signed combination of prime-level binomial carries. -/
def signedBinomialResidues {ι : Type*} {p : ℕ} (s : Finset ι) (w : ι → ℝ)
    (u v : ι → ZMod p) (x : ZMod p) : ℝ :=
  ∑ i ∈ s, w i*binomialResidueCarry (u i) (v i) x

theorem signedBinomialResidues_reflect {ι : Type*} {p : ℕ} [Fact p.Prime]
    (s : Finset ι) (w : ι → ℝ) (u v : ι → ZMod p)
    {x : ZMod p} (hx : x ≠ 0) :
    signedBinomialResidues s w u v x + signedBinomialResidues s w u v (-x) =
      ∑ i ∈ s, w i*(nonzeroSlope (u i)+nonzeroSlope (v i)-nonzeroSlope (u i+v i)) := by
  unfold signedBinomialResidues
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_add,binomialResidueCarry_reflect _ _ hx]

/-- Indicator of the last `h` nonzero residues below `p`. -/
def topResidueWeight (p h r : ℕ) : ℝ := if p ≤ r+h then 1 else 0

/-- At level `m` the last quotient class consists of the last `floor(m/q)`
residues of the base, including the first of those residues. -/
theorem last_quotient_class_iff_top_residue {q m : ℕ} (hq : 0<q) (hm : 0<m) (N : ℕ) :
    q ∣ q*N/m+1 ↔ m ≤ N%m+m/q := by
  have hr := Nat.mod_lt N hm
  have hsplit : q*N = m*(q*(N/m))+q*(N%m) := calc
    _ = q*(N%m+m*(N/m)) := congrArg (q*·) (Nat.mod_add_div N m).symm
    _ = _ := by ring
  rw [hsplit,Nat.mul_add_div hm,add_assoc,Nat.dvd_add_right (Nat.dvd_mul_right q (N/m))]
  have hu := (Nat.div_lt_iff_lt_mul hm).mpr ((Nat.mul_lt_mul_left hq).mpr hr)
  have hd : q ∣ q*(N%m)/m+1 ↔ q-1 ≤ q*(N%m)/m := by
    constructor
    · intro h; have := Nat.le_of_dvd (Nat.zero_lt_succ _) h; omega
    · intro h; rw [show q*(N%m)/m+1=q by omega]
  rw [hd,Nat.le_div_iff_mul_le hm]
  have h1 : (q-1)*m+m=q*m := by rw [← add_one_mul,show q-1+1=q by omega]
  have h2 : (m-N%m)*q+q*(N%m)=q*m := by
    rw [mul_comm (m-N%m),← mul_add,Nat.sub_add_cancel hr.le]
  have h3 := Nat.le_div_iff_mul_le hq (x := m-N%m) (y := m)
  omega

private theorem sum_reflected_pairs (f : ℕ → ℝ) (k : ℕ) :
    ∑ n ∈ range (2*k), f (n+1) = ∑ n ∈ range k, (f (n+1)+f (2*k-n)) := by
  rw [two_mul,Finset.sum_range_add,sum_add_distrib]
  congr 1
  rw [← Finset.sum_range_reflect (fun n => f (k+n+1)) k]
  refine sum_congr rfl fun n hn => ?_
  exact congrArg f (by have := mem_range.mp hn; omega)

private theorem sum_initial (k h : ℕ) (hh : h ≤ k) (a b : ℝ) :
    ∑ n ∈ range k, (if n < h then a else b) = h*a+(k-h : ℕ)*b := by
  conv_lhs => rw [show k=h+(k-h) by omega,Finset.sum_range_add]
  rw [sum_congr rfl (fun n hn => if_pos (mem_range.mp hn)),
    sum_congr rfl (fun n _ => if_neg (show ¬h+n<h by omega))]
  simp

/-- The reflected sums yield a lower bound for the full absolute error in a prime period. -/
theorem topResidue_abs_error_of_reflection {k h : ℕ} (hh : h ≤ k) (K : ℕ → ℝ) (W : ℝ)
    (hK : ∀ n < k, K (n+1)+K (2*k-n)=W) :
    h*|W-1|+(k-h : ℕ)*|W| ≤
      ∑ n ∈ range (2*k), |K (n+1)-topResidueWeight (2*k+1) h (n+1)| := by
  rw [sum_reflected_pairs (fun n => |K n-topResidueWeight (2*k+1) h n|) k,← sum_initial k h hh]
  apply sum_le_sum
  intro n hn
  have hn' := mem_range.mp hn
  have hl : topResidueWeight (2*k+1) h (n+1)=0 := if_neg (by omega)
  have hu : topResidueWeight (2*k+1) h (2*k-n) = if n<h then 1 else 0 := by
    unfold topResidueWeight
    split <;> split <;> first | rfl | omega
  rw [hl,sub_zero,hu]
  by_cases hnh : n<h
  · rw [if_pos hnh,if_pos hnh,← hK n hn',add_sub_assoc]
    exact abs_add_le _ _
  · rw [if_neg hnh,if_neg hnh,sub_zero,← hK n hn']
    exact abs_add_le _ _

private theorem signedBinomialResidues_reflect_nat {ι : Type*} {k : ℕ}
    [Fact (2*k+1).Prime] (s : Finset ι) (w : ι → ℝ) (u v : ι → ZMod (2*k+1))
    (n : ℕ) (hn : n<k) :
    signedBinomialResidues s w u v (n+1 : ℕ) + signedBinomialResidues s w u v (2*k-n : ℕ) =
      ∑ i ∈ s, w i*(nonzeroSlope (u i)+nonzeroSlope (v i)-nonzeroSlope (u i+v i)) := by
  have hp : n+1 < 2*k+1 := by omega
  have hx : ((n+1 : ℕ) : ZMod (2*k+1)) ≠ 0 := by
    intro e
    have he := congrArg ZMod.val e
    rw [ZMod.val_natCast_of_lt hp,ZMod.val_zero] at he
    omega
  have he : ((2*k-n : ℕ) : ZMod (2*k+1)) = -((n+1 : ℕ) : ZMod (2*k+1)) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← Nat.cast_add,show 2*k-n+(n+1)=2*k+1 by omega,ZMod.natCast_self]
  change signedBinomialResidues s w u v _ + signedBinomialResidues s w u v _ = _
  rw [he]
  exact signedBinomialResidues_reflect s w u v hx

/-- No signed combination improves on zero in absolute error if at most a quarter
of the residues are selected. -/
theorem signedBinomialResidues_absolute_error {ι : Type*} {k h : ℕ}
    [Fact (2*k+1).Prime] (hh : 2*h ≤ k)
    (s : Finset ι) (w : ι → ℝ) (u v : ι → ZMod (2*k+1)) :
    (h:ℝ) ≤ ∑ n ∈ range (2*k),
      |signedBinomialResidues s w u v (n+1 : ℕ)-topResidueWeight (2*k+1) h (n+1)| := by
  let K := fun n : ℕ => signedBinomialResidues s w u v n
  let W := ∑ i ∈ s, w i*(nonzeroSlope (u i)+nonzeroSlope (v i)-nonzeroSlope (u i+v i))
  have href := signedBinomialResidues_reflect_nat s w u v
  have hsplit := topResidue_abs_error_of_reflection (by omega : h ≤ k) K W href
  have hab : 1 ≤ |W-1|+|W| := by
    have ht := abs_sub_le (1:ℝ) W 0
    simpa only [sub_zero,abs_one,abs_sub_comm 1 W] using ht
  have hcoef : (h:ℝ) ≤ ((k-h:ℕ):ℝ) := by exact_mod_cast (by omega : h ≤ k-h)
  calc
    _ ≤ h*(|W-1|+|W|) := le_mul_of_one_le_right (Nat.cast_nonneg h) hab
    _ ≤ h*|W-1|+((k-h:ℕ):ℝ)*|W| := by
      rw [mul_add]
      exact add_le_add_right (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)) _
    _ ≤ _ := hsplit

/-- A majorant must pay at least one per reflected pair. Its total excess above
the last `h` residues is therefore at least half the period minus `h`. -/
theorem signedBinomialResidues_majorant_excess {ι : Type*} {k h : ℕ}
    [Fact (2*k+1).Prime] (hh : 0<h) (hk : h≤k)
    (s : Finset ι) (w : ι → ℝ) (u v : ι → ZMod (2*k+1))
    (hcover : ∀ n < 2*k, topResidueWeight (2*k+1) h (n+1) ≤
      signedBinomialResidues s w u v (n+1 : ℕ)) :
    (k:ℝ)-h ≤ ∑ n ∈ range (2*k),
      (signedBinomialResidues s w u v (n+1 : ℕ)-topResidueWeight (2*k+1) h (n+1)) := by
  let K := fun n : ℕ => signedBinomialResidues s w u v n
  let W := ∑ i ∈ s, w i*(nonzeroSlope (u i)+nonzeroSlope (v i)-nonzeroSlope (u i+v i))
  have href : ∀ n < k, K (n+1)+K (2*k-n)=W := signedBinomialResidues_reflect_nat s w u v
  have hW : 1 ≤ W := by
    have hlo := hcover 0 (by omega)
    have hhi := hcover (2*k-1) (by omega)
    rw [show 2*k-1+1=2*k by omega] at hhi
    change topResidueWeight (2*k+1) h 1 ≤ K 1 at hlo
    change topResidueWeight (2*k+1) h (2*k) ≤ K (2*k) at hhi
    rw [topResidueWeight,if_neg (by omega)] at hlo
    rw [topResidueWeight,if_pos (by omega)] at hhi
    simpa only [← href 0 (by omega),Nat.zero_add,Nat.sub_zero,zero_add] using add_le_add hlo hhi
  change _ ≤ ∑ n ∈ range (2*k), (K (n+1)-topResidueWeight (2*k+1) h (n+1))
  rw [sum_reflected_pairs (fun n => K n-topResidueWeight (2*k+1) h n) k]
  calc
    _ = ∑ n ∈ range k, (if n<h then (0:ℝ) else 1) := by
      rw [sum_initial k h hk,Nat.cast_sub hk]; ring
    _ ≤ _ := by
      apply sum_le_sum
      intro n hn
      have hn' := mem_range.mp hn
      have hlo : topResidueWeight (2*k+1) h (n+1) = 0 := if_neg (by omega)
      rw [hlo,sub_zero,topResidueWeight]
      have hw := href n hn'
      by_cases hnH : n<h
      · rw [if_pos hnH,if_pos (by omega)]; linarith only [hw,hW]
      · rw [if_neg hnH,if_neg (by omega),sub_zero]; linarith only [hw,hW]

private theorem sum_topResidueWeight {k h : ℕ} (hh : h≤k) :
    ∑ n ∈ range (2*k), topResidueWeight (2*k+1) h (n+1) = h := by
  have he (n : ℕ) : topResidueWeight (2*k+1) h (n+1) = if n<2*k-h then 0 else 1 := by
    unfold topResidueWeight
    split <;> split <;> first | rfl | omega
  simp_rw [he]
  rw [sum_initial _ _ (Nat.sub_le ..),show 2*k-(2*k-h)=h by omega]
  ring

/-- The zero approximation attains the absolute-error bound. -/
theorem topResidueWeight_absolute_mass {k h : ℕ} (hh : h≤k) :
    ∑ n ∈ range (2*k), |(0:ℝ)-topResidueWeight (2*k+1) h (n+1)| = h := by
  rw [← sum_topResidueWeight hh]
  refine sum_congr rfl fun n _ => ?_
  unfold topResidueWeight
  split <;> norm_num

/-- The ordinary central binomial attains the sharp one-sided bound at every odd prime. -/
theorem centralBinomialResidue_excess {k h : ℕ} (hh : h≤k) :
    (∀ n < 2*k, topResidueWeight (2*k+1) h (n+1) ≤
      binomialResidueCarry (p := 2*k+1) 1 1 (n+1 : ℕ)) ∧
    ∑ n ∈ range (2*k), (binomialResidueCarry (p := 2*k+1) 1 1 (n+1 : ℕ)-
      topResidueWeight (2*k+1) h (n+1)) = (k:ℝ)-h := by
  have he (n : ℕ) (hn : n<2*k) :
      binomialResidueCarry (p := 2*k+1) 1 1 (n+1 : ℕ) = if n<k then 0 else 1 := by
    rw [binomialResidueCarry,one_mul,ZMod.val_natCast_of_lt (by omega : n+1<2*k+1)]
    split <;> split <;> first | rfl | omega
  constructor
  · intro n hn
    rw [he n hn,topResidueWeight]
    split <;> split <;> first | (exfalso; omega) | norm_num
  · rw [sum_sub_distrib,sum_topResidueWeight hh,sum_congr rfl (fun n hn => he n (mem_range.mp hn)),
      sum_initial _ _ (by omega : k≤2*k),show 2*k-k=k by omega]
    ring

#print axioms binomialResidueCarry_reflect
#print axioms signedBinomialResidues_absolute_error
#print axioms signedBinomialResidues_majorant_excess
#print axioms centralBinomialResidue_excess
#print axioms last_quotient_class_iff_top_residue

end GaloisForLFunctions.ExceptionalLayerTheory
