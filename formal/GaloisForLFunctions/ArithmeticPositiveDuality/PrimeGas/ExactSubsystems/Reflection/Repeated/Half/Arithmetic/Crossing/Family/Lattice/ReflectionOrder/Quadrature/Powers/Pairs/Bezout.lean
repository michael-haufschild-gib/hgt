import Mathlib.Data.Int.GCD
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic

/-! # The least determinant of odd lifts of a coprime pair -/

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Pairs

/-- Parity shared by the determinants of all pairs of odd lifts. -/
def residue (a b : ℕ+) : ℤ := ((b.val : ℤ)-(a.val : ℤ)) % 2

theorem residue_bounds (a b : ℕ+) : 0 ≤ residue a b ∧ residue a b ≤ 1 := by
  unfold residue
  omega

/-- Bézout supplies an odd determinant of least absolute value. A
common translation puts both lifts in their respective period intervals. -/
theorem finite_bezout (a b : ℕ+) (cop : Nat.Coprime a.val b.val) :
    ∃ (i : Fin a.val) (j : Fin b.val),
      (b.val : ℤ)*(2*(i.val : ℤ)+1)-(a.val : ℤ)*(2*(j.val : ℤ)+1)=residue a b := by
  let A : ℤ := a.val
  let B : ℤ := b.val
  have ha : 0 < A := Int.natCast_pos.mpr a.pos
  have hb : 0 < B := Int.natCast_pos.mpr b.pos
  let m := -((B-A)/2)
  let r := a.val.gcdB b.val*m
  let s := -(a.val.gcdA b.val*m)
  have bez := Nat.gcd_eq_gcd_ab a.val b.val
  rw [cop.gcd_eq_one] at bez
  change 1=A*a.val.gcdA b.val+B*a.val.gcdB b.val at bez
  have base : B*r-A*s=m := by dsimp only [r,s]; linear_combination -m*bez
  have parity : B-A+2*m=residue a b := by change B-A+2*(-((B-A)/2))=(B-A)%2; omega
  let u := r%A
  let q := r/A
  let v := s-B*q
  have decomp : u+A*q=r := Int.emod_add_mul_ediv r A
  have hit : B*(2*u+1)-A*(2*v+1)=residue a b := by
    dsimp only [v]
    linear_combination 2*B*decomp + 2*base + parity
  have hu : 0 ≤ u := Int.emod_nonneg _ ha.ne'
  have hu' : u < A := Int.emod_lt_of_pos _ ha
  obtain ⟨hd,hd'⟩ := residue_bounds a b
  have hv : 0 ≤ v := by
    by_contra! neg
    have bad := mul_neg_of_pos_of_neg ha (show 2*v+1<0 by omega)
    have left := mul_nonneg hb.le hu
    nlinarith only [bad,left,hb,hit,hd']
  have hv' : v < B := by
    by_contra! large
    have left := mul_nonneg hb.le (show 0 ≤ A-1-u by omega)
    have right := mul_nonneg ha.le (sub_nonneg.mpr large)
    nlinarith only [hit,hd,left,right,ha,hb]
  refine ⟨⟨u.toNat,?_⟩,⟨v.toNat,?_⟩,?_⟩
  · exact_mod_cast (show (u.toNat : ℤ)<(a.val : ℤ) by simpa only [Int.toNat_of_nonneg hu] using hu')
  · exact_mod_cast (show (v.toNat : ℤ)<(b.val : ℤ) by simpa only [Int.toNat_of_nonneg hv] using hv')
  · simpa only [Int.toNat_of_nonneg hu,Int.toNat_of_nonneg hv] using hit

/-- Every odd determinant is at least the parity residue in absolute value. -/
theorem least_odd (a b : ℕ+) (i j : ℕ) :
    residue a b ≤ |(b.val : ℤ)*(2*(i : ℤ)+1)-(a.val : ℤ)*(2*(j : ℤ)+1)| := by
  let z := (b.val : ℤ)*(i : ℤ)-(a.val : ℤ)*(j : ℤ)
  have eq : (b.val : ℤ)*(2*(i : ℤ)+1)-(a.val : ℤ)*(2*(j : ℤ)+1)=
      2*z+((b.val : ℤ)-(a.val : ℤ)) := by dsimp only [z]; ring
  rw [eq]
  unfold residue
  rcases le_total 0 (2*z+((b.val : ℤ)-(a.val : ℤ))) with h | h
  · rw [abs_of_nonneg h]; omega
  · rw [abs_of_nonpos h]; omega

#print axioms finite_bezout
#print axioms least_odd
#print axioms residue_bounds

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Pairs
