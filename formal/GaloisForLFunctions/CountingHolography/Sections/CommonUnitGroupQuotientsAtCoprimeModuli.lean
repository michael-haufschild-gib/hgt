import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-! # Common unit group quotients at coprime moduli

Prime powers in a modulus contribute their own prime to the principal
unit group. For coprime moduli those two contributions are coprime.
Thus every common quotient order divides the product of the residue
field unit orders. Passing from the modulus to its full unit count
loses at most a factor equal to the largest permitted prime.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset

/-- Product of the unit orders of the residue fields at the distinct primes of u. -/
def residueUnitOrder (u : ℕ) : ℕ := ∏ p ∈ u.primeFactors, (p-1)

private def primePowerPart (u : ℕ) := u / ∏ p ∈ u.primeFactors, p

private theorem primePowerPart_dvd (u : ℕ) : primePowerPart u ∣ u :=
  ⟨_,(Nat.div_mul_cancel (Nat.prod_primeFactors_dvd u)).symm⟩

private theorem totient_split (u : ℕ) : u.totient=primePowerPart u*residueUnitOrder u :=
  Nat.totient_eq_div_primeFactors_mul u

/-- Every common divisor of the two totients is already paid for by
the distinct residue primes, with no dependence on their multiplicities. -/
theorem gcd_totient_dvd_residueUnitOrders {u v : ℕ} (hc : u.Coprime v) :
    u.totient.gcd v.totient ∣ residueUnitOrder u*residueUnitOrder v := by
  let d := u.totient.gcd v.totient
  let t := residueUnitOrder u*residueUnitOrder v
  have h₁ : d ∣ primePowerPart u*t := by
    have hd := (Nat.gcd_dvd_left u.totient v.totient).trans (dvd_mul_right u.totient (residueUnitOrder v))
    simpa only [d,t,totient_split u,mul_assoc] using hd
  have h₂ : d ∣ primePowerPart v*t := by
    have hd := (Nat.gcd_dvd_right u.totient v.totient).trans (dvd_mul_right v.totient (residueUnitOrder u))
    simpa only [d,t,totient_split v,mul_assoc,mul_comm (residueUnitOrder v) (residueUnitOrder u)] using hd
  have h := Nat.dvd_gcd h₁ h₂
  have hcop := hc.of_dvd (primePowerPart_dvd u) (primePowerPart_dvd v)
  simpa only [Nat.gcd_mul_right,hcop.gcd_eq_one,one_mul,mul_one] using h

/-- The order of the image of any homomorphism of the actual unit groups
divides the product of the residue field unit orders. -/
theorem unitHom_range_dvd_residueUnitOrders {u v : ℕ} (hu : 0<u) (hv : 0<v) (hc : u.Coprime v)
    (f : (ZMod u)ˣ →* (ZMod v)ˣ) :
    Nat.card f.range ∣ residueUnitOrder u*residueUnitOrder v := by
  letI : NeZero u := ⟨hu.ne'⟩
  letI : NeZero v := ⟨hv.ne'⟩
  have hU : Nat.card (ZMod u)ˣ=u.totient := by rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient]
  have hV : Nat.card (ZMod v)ˣ=v.totient := by rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient]
  exact (Nat.dvd_gcd (hU ▸ Subgroup.card_range_dvd f) (hV ▸ f.range.card_subgroup_dvd_card)).trans
    (gcd_totient_dvd_residueUnitOrders hc)

/-- Multiplying p/(p−1) over any subset of the integers from two through
L costs at most L. Filling in all missing factors gives a telescoping product. -/
private theorem prime_product_le_residue_product (S : Finset ℕ) {L : ℕ} (hL : 1≤L)
    (hS : S⊆Icc 2 L) : (∏ p ∈ S, p)≤L*∏ p ∈ S, (p-1) := by
  induction L, hL using Nat.le_induction generalizing S with
  | base =>
    have he : S=∅ := eq_empty_iff_forall_notMem.mpr fun p hp => by
      have hh := mem_Icc.mp (hS hp)
      omega
    simp [he]
  | succ m hm ih =>
    by_cases h : m+1∈S
    · let T := S.erase (m+1)
      have ht : T⊆Icc 2 m := by
        intro p hp
        obtain ⟨hne,hmem⟩ := mem_erase.mp hp
        obtain ⟨hlo,hhi⟩ := mem_Icc.mp (hS hmem)
        exact mem_Icc.mpr ⟨hlo,by omega⟩
      have he : S=insert (m+1) T := (insert_erase h).symm
      rw [he,prod_insert (notMem_erase _ _),prod_insert (notMem_erase _ _),Nat.add_sub_cancel]
      exact Nat.mul_le_mul_left _ (ih T ht)
    · have ht : S⊆Icc 2 m := by
        intro p hp
        obtain ⟨hlo,hhi⟩ := mem_Icc.mp (hS hp)
        exact mem_Icc.mpr ⟨hlo,by have hne : p≠m+1 := fun e => h (e ▸ hp); omega⟩
      exact (ih S ht).trans (Nat.mul_le_mul_right _ (Nat.le_succ m))

/-- The cardinality of the unit group of a positive integer with no
prime factor above L is within a factor L of that integer. -/
theorem le_cutoff_mul_totient {u L : ℕ} (hL : 1≤L)
    (hp : ∀ p ∈ u.primeFactors, p≤L) : u ≤ L*u.totient := by
  have hS (p : ℕ) (h : p∈u.primeFactors) := mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors h).two_le,hp p h⟩
  have h := Nat.mul_le_mul_left (primePowerPart u) (prime_product_le_residue_product u.primeFactors hL hS)
  have he : primePowerPart u*(∏ p ∈ u.primeFactors,p)=u := Nat.div_mul_cancel (Nat.prod_primeFactors_dvd u)
  rw [he] at h
  rw [totient_split]
  exact h.trans_eq (by unfold residueUnitOrder; ring)

#print axioms gcd_totient_dvd_residueUnitOrders
#print axioms unitHom_range_dvd_residueUnitOrders
#print axioms le_cutoff_mul_totient

end GaloisForLFunctions.CountingHolography.Sections
