import GaloisForLFunctions.BiScaleUncertainty.SieveTripleFourier
import Mathlib.Algebra.BigOperators.Fin

/-!
# Primitive triples within a two-adic order class

Explicit triples of order `2^k*p`, for every odd `p`, all sum to the same
frequency. Pairing one triple with the negative of another produces a sixth
resonance whose coordinate product is the cube of a signed pair product.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Three primitive frequencies sharing the centre of a fixed power-of-two order class. -/
def valuationTriple (N k p : ℕ) : Fin 3 → ZMod N.factorial :=
  let r : ZMod N.factorial := (N.factorial / (2^k*p) : ℕ)
  ![r, r, if p = 1 then -r else (p-2) • r]

private theorem odd_sub_two {p : ℕ} (hp : Odd p) (hp1 : p ≠ 1) : Odd (p-2) := by
  obtain ⟨j,hj⟩ := hp
  refine ⟨j-1, ?_⟩
  omega

/-- Every entry retains the requested exact additive order, including odd part one. -/
theorem valuationTriple_order {N k p : ℕ} (hp : Odd p)
    (hd : 2^k*p ∈ Finset.Icc 1 N) (i : Fin 3) :
    addOrderOf (valuationTriple N k p i) = 2^k*p := by
  have hr := frequency_order hd
  fin_cases i
  · exact hr
  · exact hr
  · change addOrderOf (if p = 1 then -((N.factorial / (2^k*p) : ℕ) : ZMod N.factorial)
        else (p-2) • ((N.factorial / (2^k*p) : ℕ) : ZMod N.factorial)) = _
    by_cases hp1 : p = 1
    · simpa [hp1] using hr
    · rw [if_neg hp1]
      have hp2 : 2 ≤ p := by obtain ⟨j,hj⟩ := hp; omega
      have hc : Nat.Coprime (2^k*p) (p-2) := by
        apply Nat.coprime_mul_iff_left.mpr
        exact ⟨(odd_sub_two hp hp1).coprime_two_left.pow_left k,
          (Nat.coprime_self_sub_right hp2).mpr hp.coprime_two_right⟩
      have hc' : Nat.Coprime (addOrderOf
          (((N.factorial / (2^k*p) : ℕ) : ZMod N.factorial))) (p-2) := by
        rwa [hr]
      exact hc'.addOrderOf_nsmul.trans hr

/-- The sum depends only on the power of two, not on the odd part. -/
theorem valuationTriple_sum {N k p : ℕ} (hp : Odd p)
    (hd : 2^k*p ∈ Finset.Icc 1 N) :
    (∑ i, valuationTriple N k p i) = ((N.factorial / 2^k : ℕ) : ZMod N.factorial) := by
  have hp0 : 0 < p := by obtain ⟨j,hj⟩ := hp; omega
  have hdvd : 2^k*p ∣ N.factorial := Nat.dvd_factorial (Finset.mem_Icc.mp hd).1
    (Finset.mem_Icc.mp hd).2
  obtain ⟨t,ht⟩ := hdvd
  have h2 : 0 < (2:ℕ)^k := by positivity
  have hd0 : 0 < (2:ℕ)^k*p := Nat.mul_pos h2 hp0
  have hdiv : N.factorial / (2^k*p) = t := by
    rw [ht,Nat.mul_div_cancel_left _ hd0]
  have hhalf : N.factorial / 2^k = p*t := by
    rw [ht,Nat.mul_assoc,Nat.mul_div_cancel_left _ h2]
  rw [Fin.sum_univ_three]
  change ((N.factorial / (2^k*p) : ℕ) : ZMod N.factorial) +
    ((N.factorial / (2^k*p) : ℕ) : ZMod N.factorial) +
    (if p = 1 then -((N.factorial / (2^k*p) : ℕ) : ZMod N.factorial)
      else (p-2) • ((N.factorial / (2^k*p) : ℕ) : ZMod N.factorial)) = _
  rw [hdiv,hhalf]
  by_cases hp1 : p = 1
  · simp [hp1]
  · rw [if_neg hp1,nsmul_eq_mul]
    have hp2 : 2 ≤ p := by obtain ⟨j,hj⟩ := hp; omega
    push_cast [Nat.cast_sub hp2]
    ring

/-- Six explicit resonant frequencies coupling two orders in the same valuation class. -/
def valuationSix (N k p q : ℕ) : Fin 6 → ZMod N.factorial :=
  ![valuationTriple N k p 0, valuationTriple N k p 1, valuationTriple N k p 2,
    -valuationTriple N k q 0, -valuationTriple N k q 1, -valuationTriple N k q 2]

/-- The six frequencies form an exact zero-sum resonance. -/
theorem valuationSix_sum {N k p q : ℕ} (hp : Odd p) (hq : Odd q)
    (hd : 2^k*p ∈ Finset.Icc 1 N) (he : 2^k*q ∈ Finset.Icc 1 N) :
    (∑ i, valuationSix N k p q i) = 0 := by
  have hp' := valuationTriple_sum hp hd
  have hq' := valuationTriple_sum hq he
  simp only [Fin.sum_univ_three] at hp' hq'
  rw [Fin.sum_univ_six]
  change valuationTriple N k p 0 + valuationTriple N k p 1 + valuationTriple N k p 2 +
    -valuationTriple N k q 0 + -valuationTriple N k q 1 + -valuationTriple N k q 2 = 0
  linear_combination hp' - hq'

/-- Products over these six exact orders are cubes of pair products. -/
theorem valuationSix_order_product {N k p q : ℕ} (hp : Odd p) (hq : Odd q)
    (hd : 2^k*p ∈ Finset.Icc 1 N) (he : 2^k*q ∈ Finset.Icc 1 N)
    (v : ℕ → ℂ) :
    (∏ i, v (addOrderOf (valuationSix N k p q i))) = (v (2^k*p)*v (2^k*q))^3 := by
  rw [Fin.prod_univ_six]
  change v (addOrderOf (valuationTriple N k p 0)) *
    v (addOrderOf (valuationTriple N k p 1)) * v (addOrderOf (valuationTriple N k p 2)) *
    v (addOrderOf (-valuationTriple N k q 0)) * v (addOrderOf (-valuationTriple N k q 1)) *
    v (addOrderOf (-valuationTriple N k q 2)) = _
  simp only [addOrderOf_neg,valuationTriple_order hp hd,valuationTriple_order hq he]
  ring

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
