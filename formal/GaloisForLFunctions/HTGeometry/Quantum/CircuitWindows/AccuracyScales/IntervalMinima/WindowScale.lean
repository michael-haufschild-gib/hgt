import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-! # Observation length and precision for a superexponential time window -/

open Filter
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima

/-- Number of bits specifying a unit time cell, with N=k+3. -/
def windowBits (k : ℕ) := (k+3)*((k+3).sqrt+2)

theorem windowBits_strictMono : StrictMono windowBits := by
  intro i j hij
  have h₁ := Nat.add_lt_add_right hij 3
  have h₂ := Nat.sqrt_le_sqrt h₁.le
  exact (Nat.mul_lt_mul_of_pos_right h₁ (by omega : 0 < (i+3).sqrt+2)).trans_le
    (Nat.mul_le_mul_left (j+3) (Nat.add_le_add_right h₂ 2))

theorem prefix_le_windowBits (k : ℕ) : k+3 ≤ windowBits k :=
  Nat.le_mul_of_pos_right _ (by omega : 0 < (k+3).sqrt+2)

/-- For every fixed record clearance exponent and every fixed compiler
scale m, its quadratic number of accuracy bits eventually dominates
q times the number of bits needed to specify a cell. -/
theorem windowBits_le_precision (q m : ℕ) (hm : 0 < m) :
    ∀ᶠ k : ℕ in atTop, q*windowBits k ≤ ((k+3)/m)^2 := by
  let c := 4*m^2*q
  filter_upwards [eventually_ge_atTop ((2*c+2)*(2*c+2)),eventually_ge_atTop m] with k hk hmk
  let N := k+3
  let u := N.sqrt
  have hN : m ≤ N := hmk.trans (by dsimp only [N]; omega)
  have hs : (2*c+2)*(2*c+2) ≤ N := hk.trans (by dsimp only [N]; omega)
  have hroot : 2*c+2 ≤ u := Nat.le_sqrt.mpr hs
  have hu : u*u ≤ N := Nat.sqrt_le N
  have hc : c*(u+2) ≤ N := by
    calc _ ≤ c*(2*u) := Nat.mul_le_mul_left _ (by omega)
         _ = (2*c)*u := by ring
         _ ≤ u*u := Nat.mul_le_mul_right _ (by omega)
         _ ≤ _ := hu
  have hd := Nat.div_pos hN hm
  have hmod := Nat.mod_lt N hm
  have hid := Nat.mod_add_div N m
  have hunit : m ≤ m*(N/m) := Nat.le_mul_of_pos_right _ hd
  have hdouble : N ≤ 2*m*(N/m) := by
    rw [Nat.mul_assoc]
    omega
  have hleft : (4*m^2)*(q*windowBits k) ≤ N^2 := by
    calc _ = N*(c*(u+2)) := by change (4*m^2)*(q*(N*(u+2)))=_; dsimp only [c]; ring
         _ ≤ N*N := Nat.mul_le_mul_left _ hc
         _ = _ := (sq _).symm
  have hright : N^2 ≤ (4*m^2)*((k+3)/m)^2 := by
    calc _ ≤ (2*m*(N/m))^2 := Nat.pow_le_pow_left hdouble _
         _ = _ := by change _=4*m^2*(N/m)^2; ring
  exact Nat.le_of_mul_le_mul_left (hleft.trans hright) (by positivity)

#print axioms windowBits_le_precision
end GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
