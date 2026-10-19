import GaloisForLFunctions.BiScaleUncertainty.SieveMomentSpectralEquivalence
import GaloisForLFunctions.BiScaleUncertainty.CoprimeOverlapQuarticReadout
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Arithmetic edge orders and their quartic resonances

Pairwise coprime odd vertex blocks give incomparable orders on distinct
edges. A zero-sum frequency tuple cannot have a vertex occurring just once.
Explicit triangle and cycle frequencies recover their coordinate products
from the complete fourth translated observation array.
-/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
set_option autoImplicit false

/-- In a zero-sum tuple, all other additive orders jointly annihilate each entry. -/
theorem order_dvd_product_of_sum_zero {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] (r : ι → G) (hz : (∑ i, r i) = 0) (j : ι) :
    addOrderOf (r j) ∣ ∏ i ∈ Finset.univ.erase j, addOrderOf (r i) := by
  let B := ∏ i ∈ Finset.univ.erase j, addOrderOf (r i)
  apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
  have ht : (∑ i, B • r i) = B • r j := by
    apply Finset.sum_eq_single j
    · intro i _ hij
      apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
      exact Finset.dvd_prod_of_mem _ (by simp [hij])
    · simp
  rw [← Finset.smul_sum, hz, smul_zero] at ht
  exact ht.symm

/-- A nontrivial block cannot occur in just one order of a zero-sum tuple. -/
theorem no_exclusive_coprime_block {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] (r : ι → G) (hz : (∑ i, r i) = 0) (j : ι)
    (b : ℕ) (hb : 1 < b) (hdiv : b ∣ addOrderOf (r j))
    (hc : ∀ i, i ≠ j → Nat.Coprime b (addOrderOf (r i))) : False := by
  have hprod : Nat.Coprime b (∏ i ∈ Finset.univ.erase j, addOrderOf (r i)) := by
    apply Nat.Coprime.prod_right
    intro i hi
    exact hc i (Finset.mem_erase.mp hi).1
  have he := Nat.eq_one_of_dvd_coprimes hprod (dvd_refl b)
    (hdiv.trans (order_dvd_product_of_sum_zero r hz j))
  omega

namespace ArithmeticEdges

/-- Nontrivial odd blocks with disjoint arithmetic factors. -/
structure Blocks (V : Type*) where
  value : V → ℕ
  odd : ∀ v, Odd (value v)
  gt_one : ∀ v, 1 < value v
  coprime : ∀ u v, u ≠ v → Nat.Coprime (value u) (value v)

namespace Blocks
variable {V : Type*} (D : Blocks V)

/-- The additive order attached to an unordered edge. -/
def order (u v : V) : ℕ := 2 * D.value u * D.value v

theorem order_symm (u v : V) : D.order u v = D.order v u := by
  unfold order
  ring

theorem value_dvd_order {u v w : V} (hw : w = u ∨ w = v) :
    D.value w ∣ D.order u v := by
  rcases hw with rfl | rfl
  · exact ⟨2 * D.value v, by unfold order; ring⟩
  · exact ⟨2 * D.value u, by unfold order; ring⟩

theorem coprime_order {u v w : V} (hu : w ≠ u) (hv : w ≠ v) :
    Nat.Coprime (D.value w) (D.order u v) :=
  ((D.odd w).coprime_two_right.mul_right (D.coprime w u hu)).mul_right
    (D.coprime w v hv)

/-- An order can divide another edge order only if both endpoints persist. -/
theorem endpoint_of_order_dvd {u v x y w : V}
    (h : D.order u v ∣ D.order x y) (hw : w = u ∨ w = v) : w = x ∨ w = y := by
  by_contra hn
  push Not at hn
  have he := Nat.eq_one_of_dvd_coprimes (D.coprime_order hn.1 hn.2)
    (dvd_refl (D.value w)) ((D.value_dvd_order hw).trans h)
  have := D.gt_one w
  omega

/-- Distinct two-vertex supports give incomparable orders. -/
theorem order_dvd_iff {u v x y : V} (huv : u ≠ v) :
    D.order u v ∣ D.order x y ↔ (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  constructor
  · intro h
    have hu := D.endpoint_of_order_dvd h (Or.inl rfl : u = u ∨ u = v)
    have hv := D.endpoint_of_order_dvd h (Or.inr rfl : v = u ∨ v = v)
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv rfl).elim
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
    · exact (huv rfl).elim
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact dvd_refl _
    · rw [D.order_symm]

/-- Every vertex in a resonant tuple occurs in another edge occurrence. -/
theorem resonance_vertex_repeats {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] (r : ι → G) (u v : ι → V)
    (ho : ∀ i, addOrderOf (r i) = D.order (u i) (v i))
    (hz : (∑ i, r i) = 0) (j : ι) (w : V) (hw : w = u j ∨ w = v j) :
    ∃ i, i ≠ j ∧ (w = u i ∨ w = v i) := by
  by_contra hn
  apply no_exclusive_coprime_block r hz j (D.value w) (D.gt_one w)
  · rw [ho]
    exact D.value_dvd_order hw
  · intro i hij
    rw [ho]
    apply D.coprime_order
    · intro he
      exact hn ⟨i,hij,Or.inl he⟩
    · intro he
      exact hn ⟨i,hij,Or.inr he⟩

end Blocks

open ZMod
open AffineSieve
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- An oriented edge frequency with a common half-period component. -/
def edgeFrequency (N p q : ℕ) : ZMod N.factorial :=
  (N.factorial / 2 : ℕ) + (N.factorial / p : ℕ) - (N.factorial / q : ℕ)

private theorem add_order {P A B : ℕ} [NeZero P] (x y : ZMod P)
    (hx : addOrderOf x = A) (hy : addOrderOf y = B) (hc : Nat.Coprime A B) :
    addOrderOf (x+y) = A*B := by
  have hcomm : AddCommute x y := add_comm x y
  have h := hcomm.addOrderOf_add_eq_mul_addOrderOf_of_coprime
    (show Nat.Coprime (addOrderOf x) (addOrderOf y) by rwa [hx,hy])
  simpa only [hx,hy] using h

theorem edgeFrequency_order {N p q : ℕ} (hN : 2 ≤ N) (hp : Odd p) (hq : Odd q)
    (hpN : p ∈ Finset.Icc 1 N) (hqN : q ∈ Finset.Icc 1 N)
    (hpq : Nat.Coprime p q) : addOrderOf (edgeFrequency N p q) = 2*p*q := by
  let d : ZMod N.factorial := (N.factorial / 2 : ℕ)
  let a : ZMod N.factorial := (N.factorial / p : ℕ)
  let b : ZMod N.factorial := (N.factorial / q : ℕ)
  have hd : addOrderOf d = 2 := frequency_order (Finset.mem_Icc.mpr ⟨by omega,hN⟩)
  have ha : addOrderOf a = p := frequency_order hpN
  have hb : addOrderOf (-b) = q := by
    rw [addOrderOf_neg]
    exact frequency_order hqN
  change addOrderOf (d+a-b) = _
  rw [sub_eq_add_neg]
  exact add_order (d+a) (-b) (add_order d a hd ha hp.coprime_two_left) hb
    (hq.coprime_two_left.mul_left hpq)

/-- Four oriented edges around a cycle. -/
def cycleFrequencies (N p q r s : ℕ) : Fin 4 → ZMod N.factorial :=
  ![edgeFrequency N p q, edgeFrequency N q r, edgeFrequency N r s, edgeFrequency N s p]

theorem cycleFrequencies_sum {N p q r s : ℕ} (hN : 2 ≤ N) :
    (∑ i, cycleFrequencies N p q r s i) = 0 := by
  have hd := frequency_order (Finset.mem_Icc.mpr ⟨by omega,hN⟩)
  have hz := addOrderOf_nsmul_eq_zero (((N.factorial / 2 : ℕ)) : ZMod N.factorial)
  rw [hd,two_nsmul] at hz
  rw [Fin.sum_univ_four]
  dsimp [cycleFrequencies,edgeFrequency]
  linear_combination 2 * hz

theorem cycleFrequencies_orders {N p q r s : ℕ} (hN : 2 ≤ N)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hs : Odd s)
    (hpN : p ∈ Finset.Icc 1 N) (hqN : q ∈ Finset.Icc 1 N)
    (hrN : r ∈ Finset.Icc 1 N) (hsN : s ∈ Finset.Icc 1 N)
    (hpq : Nat.Coprime p q) (hqr : Nat.Coprime q r)
    (hrs : Nat.Coprime r s) (hsp : Nat.Coprime s p) (i : Fin 4) :
    addOrderOf (cycleFrequencies N p q r s i) = ![2*p*q,2*q*r,2*r*s,2*s*p] i := by
  fin_cases i
  · exact edgeFrequency_order hN hp hq hpN hqN hpq
  · exact edgeFrequency_order hN hq hr hqN hrN hqr
  · exact edgeFrequency_order hN hr hs hrN hsN hrs
  · exact edgeFrequency_order hN hs hp hsN hpN hsp

/-- A cycle reads the product of its four arithmetic coordinates. -/
theorem cycle_products_of_fourth_moments {N p q r s : ℕ} (hN : 2 ≤ N)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hs : Odd s)
    (hpN : p ∈ Finset.Icc 1 N) (hqN : q ∈ Finset.Icc 1 N)
    (hrN : r ∈ Finset.Icc 1 N) (hsN : s ∈ Finset.Icc 1 N)
    (hpq : Nat.Coprime p q) (hqr : Nat.Coprime q r)
    (hrs : Nat.Coprime r s) (hsp : Nat.Coprime s p)
    (c e : ℕ → ℝ) (hm : ∀ h : Fin 4 → ℕ, translatedMoment N c h = translatedMoment N e h) :
    selbergMultiplesCoord N c (2*p*q) * selbergMultiplesCoord N c (2*q*r) *
      selbergMultiplesCoord N c (2*r*s) * selbergMultiplesCoord N c (2*s*p) =
    selbergMultiplesCoord N e (2*p*q) * selbergMultiplesCoord N e (2*q*r) *
      selbergMultiplesCoord N e (2*r*s) * selbergMultiplesCoord N e (2*s*p) := by
  have hh := resonant_products_of_moments_eq N c e 4 hm (cycleFrequencies N p q r s)
    (cycleFrequencies_sum hN)
  simp_rw [cycleFrequencies_orders hN hp hq hr hs hpN hqN hrN hsN hpq hqr hrs hsp] at hh
  simpa [Fin.prod_univ_four] using hh

/-- A triangle reads two signed coordinates times the square of its third. -/
theorem triangle_products_of_fourth_moments {N p q r : ℕ} (hN : 2 ≤ N)
    (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpN : p ∈ Finset.Icc 1 N) (hqN : q ∈ Finset.Icc 1 N)
    (hrN : r ∈ Finset.Icc 1 N)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r)
    (c e : ℕ → ℝ) (hm : ∀ h : Fin 4 → ℕ, translatedMoment N c h = translatedMoment N e h) :
    selbergMultiplesCoord N c (2*p*q) * selbergMultiplesCoord N c (2*p*r) *
      selbergMultiplesCoord N c (2*q*r)^2 =
    selbergMultiplesCoord N e (2*p*q) * selbergMultiplesCoord N e (2*p*r) *
      selbergMultiplesCoord N e (2*q*r)^2 := by
  have hh := resonant_products_of_moments_eq N c e 4 hm (CoprimeOverlap.frequencies N p q r)
    (CoprimeOverlap.frequencies_sum hN)
  simp_rw [CoprimeOverlap.frequencies_orders hN hp hq hr hpN hqN hrN hpq hpr hqr] at hh
  simpa [Fin.prod_univ_four,pow_two,mul_assoc] using hh

end ArithmeticEdges

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
