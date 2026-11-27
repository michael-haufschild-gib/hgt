import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-! # Strict improvement of nonintegral heights for two positive frequencies -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Window

open Real Finset

/-- Joint angular error when one unit of height advances the sum of the
two phases by π. The first frequency has share α. -/
def signal (α x : ℝ) := max |cos (π*(α*x))| |cos (π*((1-α)*x))|

def sample (α : ℝ) (j : ℕ) := |cos (π*(α*(j : ℝ)))|

theorem at_integer (α : ℝ) (j : ℕ) : signal α j = sample α j := by
  have eq : π*((1-α)*(j : ℝ))= -(π*(α*(j : ℝ)))+(j : ℝ)*π := by ring
  simp only [signal,sample,eq,cos_add_nat_mul_pi,cos_neg,abs_mul,abs_pow,abs_neg,abs_one,
    one_pow,one_mul,max_self]

private def displacement (u : ℝ) (i : ℤ) := u-(i : ℝ)-1/2

private theorem centered (u : ℝ) : |displacement u ⌊u⌋| ≤ 1/2 := by
  unfold displacement
  exact abs_le.mpr ⟨by linarith only [Int.floor_le u],
    by linarith only [Int.lt_floor_add_one u]⟩

private theorem centered_cos (u : ℝ) (i : ℤ) (h : |displacement u i| ≤ 1/2) :
    |cos (π*u)|=sin (π*|displacement u i|) := by
  let e := displacement u i
  have arg : π*u=(π/2+π*e)+(i : ℝ)*π := by dsimp only [e,displacement]; ring
  have pos : 0 ≤ sin (π*|e|) :=
    sin_nonneg_of_nonneg_of_le_pi (mul_nonneg pi_pos.le (abs_nonneg e))
      (by linarith only [mul_le_mul_of_nonneg_left h pi_pos.le,pi_pos])
  change |cos (π*u)|=sin (π*|e|)
  rw [arg,cos_add_int_mul_pi,abs_mul,abs_zpow,abs_neg,abs_one,one_zpow,one_mul,
    cos_add,cos_pi_div_two,sin_pi_div_two,zero_mul,one_mul,zero_sub,abs_neg]
  rcases le_total 0 e with he | he
  · rw [abs_of_nonneg he] at pos ⊢; exact abs_of_nonneg pos
  · rw [abs_of_nonpos he,mul_neg,sin_neg] at pos ⊢; exact abs_of_nonpos (neg_nonneg.mp pos)

private theorem strict_balance {α e f : ℝ} (ha : 0 < α) (hb : α < 1) (hne : e ≠ -f) :
    |(1-α)*e-α*f| < max |e| |f| := by
  have L : -max |e| |f| ≤ e := (neg_le_neg (le_max_left _ _)).trans (neg_abs_le e)
  have U : e ≤ max |e| |f| := (le_abs_self e).trans (le_max_left _ _)
  have L' : -max |e| |f| ≤ -f := neg_le_neg ((le_abs_self f).trans (le_max_right _ _))
  have U' : -f ≤ max |e| |f| := (neg_le_abs f).trans (le_max_right _ _)
  rcases lt_or_gt_of_ne hne with h | h
  · have p := mul_pos ha (sub_pos.mpr h)
    have q := mul_pos (sub_pos.mpr hb) (sub_pos.mpr h)
    exact abs_lt.mpr ⟨by linarith only [p,L],by linarith only [q,U']⟩
  · have p := mul_pos ha (sub_pos.mpr h)
    have q := mul_pos (sub_pos.mpr hb) (sub_pos.mpr h)
    exact abs_lt.mpr ⟨by linarith only [q,L'],by linarith only [p,U]⟩

/-- Every noninteger point in an integer-ended window has a strictly
better grid point. The grid index is the sum of the two nearest half-integers. -/
theorem improve {α : ℝ} (ha : 0 < α) (hb : α < 1) (N : ℕ) (x : ℝ)
    (lo : 0 ≤ x) (hi : x ≤ N) (off : ∀ j : Fin (N+1), x ≠ (j.val : ℝ)) :
    ∃ j : Fin (N+1), sample α j.val < signal α x := by
  let u := α*x
  let v := (1-α)*x
  let i := ⌊u⌋
  let l := ⌊v⌋
  let m := i+l+1
  have uv : u+v=x := by dsimp only [u,v]; ring
  have ix : 0 ≤ i := Int.floor_nonneg.mpr (mul_nonneg ha.le lo)
  have lx : 0 ≤ l := Int.floor_nonneg.mpr (mul_nonneg (sub_pos.mpr hb).le lo)
  have end_ne := off ⟨N,Nat.lt_succ_self N⟩
  have inside := lt_of_le_of_ne hi end_ne
  have il : ((i+l : ℤ) : ℝ)<(N : ℝ) := by
    push_cast
    linarith only [Int.floor_le u,Int.floor_le v,uv,inside]
  have bound : i+l < (N : ℤ) := by exact_mod_cast il
  have mn : 0 ≤ m := by dsimp only [m]; omega
  let j : Fin (N+1) := ⟨m.toNat,by dsimp only [m]; omega⟩
  have jm : (j.val : ℝ)=(i : ℝ)+(l : ℝ)+1 := by
    exact_mod_cast (Int.toNat_of_nonneg mn : (j.val : ℤ)=i+l+1)
  let e := displacement u i
  let f := displacement v l
  let d := (1-α)*e-α*f
  have eu : |e| ≤ 1/2 := centered u
  have fv : |f| ≤ 1/2 := centered v
  have neq : e≠ -f := by
    intro eq
    apply off j
    dsimp only [e,f,displacement] at eq
    linarith only [eq,uv,jm]
  have strict : |d| < max |e| |f| := strict_balance ha hb neq
  have lim : max |e| |f| ≤ 1/2 := max_le eu fv
  have jd : displacement (α*(j.val : ℝ)) i=d := by
    dsimp only [d,e,f,displacement,u,v]
    rw [jm]; ring
  have grid : sample α j.val=sin (π*|d|) := by
    unfold sample
    rw [centered_cos _ i (by rw [jd]; exact strict.le.trans lim),jd]
  have rise : sin (π*|d|)<sin (π*max |e| |f|) :=
    sin_lt_sin_of_lt_of_le_pi_div_two
      ((by linarith only [pi_pos] : -(π/2) ≤ 0).trans (mul_nonneg pi_pos.le (abs_nonneg _)))
      (by linarith only [mul_le_mul_of_nonneg_left lim pi_pos.le])
      (mul_lt_mul_of_pos_left strict pi_pos)
  refine ⟨j,?_⟩
  rw [grid]
  change sin (π*|d|) < max |cos (π*u)| |cos (π*v)|
  rw [centered_cos u i eu,centered_cos v l fv]
  rcases le_total |e| |f| with h | h
  · rw [max_eq_right h] at rise; exact rise.trans_le (le_max_right _ _)
  · rw [max_eq_left h] at rise; exact rise.trans_le (le_max_left _ _)

/-- Exact finite-window minimum, taken over one irrational rotation
when the two elementary frequencies are incommensurable. -/
def floorValue (α : ℝ) (N : ℕ) :=
  (univ : Finset (Fin (N+1))).inf' univ_nonempty (fun j => sample α j.val)

theorem attained (α : ℝ) (N : ℕ) : ∃ j : Fin (N+1), sample α j.val=floorValue α N := by
  obtain ⟨j,_,h⟩ := exists_mem_eq_inf' (univ_nonempty (α := Fin (N+1))) (fun i => sample α i.val)
  exact ⟨j,h.symm⟩

theorem lower {α : ℝ} (ha : 0 < α) (hb : α < 1) (N : ℕ) (x : ℝ)
    (lo : 0 ≤ x) (hi : x ≤ N) : floorValue α N ≤ signal α x := by
  by_cases grid : ∃ j : Fin (N+1), x=(j.val : ℝ)
  · obtain ⟨j,rfl⟩ := grid
    rw [at_integer]
    exact inf'_le _ (mem_univ j)
  · obtain ⟨j,better⟩ := improve ha hb N x lo hi (fun j h => grid ⟨j,h⟩)
    exact (inf'_le _ (mem_univ j)).trans better.le

theorem minimizers {α : ℝ} (ha : 0 < α) (hb : α < 1) (N : ℕ) (x : ℝ)
    (lo : 0 ≤ x) (hi : x ≤ N) :
    signal α x=floorValue α N ↔
      ∃ j : Fin (N+1), x=(j.val : ℝ) ∧ sample α j.val=floorValue α N := by
  constructor
  · intro hit
    by_contra! missing
    have off (j : Fin (N+1)) : x ≠ (j.val : ℝ) := by
      rintro rfl; exact missing j rfl ((at_integer α j.val).symm.trans hit)
    obtain ⟨j,better⟩ := improve ha hb N x lo hi off
    exact (inf'_le (fun i : Fin (N+1) => sample α i.val) (mem_univ j)).not_gt (better.trans_eq hit)
  · rintro ⟨j,rfl,h⟩; exact (at_integer α j.val).trans h

#print axioms at_integer
#print axioms improve
#print axioms attained
#print axioms lower
#print axioms minimizers

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Window
