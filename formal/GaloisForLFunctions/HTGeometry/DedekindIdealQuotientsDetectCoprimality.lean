import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Tactic

/-!
# Ideal quotients detect coprimality in Dedekind domains

For a nonzero ideal `m`, the quotient `(m : I)` equals `m` precisely
when `m + I` is the unit ideal. If the quotient is unchanged, the
integral fractional ideal `m * (m + I)⁻¹` lies inside `m`. Cancelling
`m` forces the inverse of `m + I` to be integral, hence `m + I = 1`.
The converse follows by multiplying a decomposition of one.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
local notation "FI" => FractionalIdeal (nonZeroDivisors A) (FractionRing A)

/-- A nonzero ideal is unchanged by quotienting by `I` exactly when the two ideals are coprime. -/
theorem ideal_colon_eq_self_iff_sup_eq_top (m I : Ideal A) (hm : m ≠ ⊥) :
    m.colon (I : Set A) = m ↔ m ⊔ I = ⊤ := by
  constructor
  · intro hcolon
    let J := m ⊔ I
    have hJ : J ≠ ⊥ := by
      intro h
      exact hm (le_bot_iff.mp (show m ≤ ⊥ from h ▸ (le_sup_left : m ≤ J)))
    have hmF : (m : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hm
    have hJF : (J : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
    have hmJ : (m : FI) ≤ (J : FI) :=
      (FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing A)).mpr le_sup_left
    have hNint : (m : FI) * (J : FI)⁻¹ ≤ 1 := by
      calc
        (m : FI) * (J : FI)⁻¹ ≤ (J : FI) * (J : FI)⁻¹ := mul_le_mul_left hmJ _
        _ = 1 := mul_inv_cancel₀ hJF
    obtain ⟨N, hN⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hNint
    have hNJ : N * J = m := by
      apply FractionalIdeal.coeIdeal_injective (K := FractionRing A)
      change ((N * J : Ideal A) : FI) = (m : FI)
      rw [FractionalIdeal.coeIdeal_mul, hN, mul_assoc, inv_mul_cancel₀ hJF, mul_one]
    have hNI : N * I ≤ m := by
      calc
        N * I ≤ N * J := mul_le_mul_right le_sup_right N
        _ = m := hNJ
    have hNm : N ≤ m := by
      rw [← hcolon]
      intro r hr
      apply Submodule.mem_colon.mpr
      intro s hs
      exact hNI (Ideal.mul_mem_mul hr hs)
    have hNmF : (m : FI) * (J : FI)⁻¹ ≤ (m : FI) := by
      rw [← hN]
      exact (FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing A)).mpr hNm
    have hJinv : (J : FI)⁻¹ ≤ 1 := by
      calc
        (J : FI)⁻¹ = (m : FI)⁻¹ * ((m : FI) * (J : FI)⁻¹) := by
          rw [← mul_assoc, inv_mul_cancel₀ hmF, one_mul]
        _ ≤ (m : FI)⁻¹ * (m : FI) := mul_le_mul_right hNmF _
        _ = 1 := inv_mul_cancel₀ hmF
    by_contra hJtop
    exact FractionalIdeal.not_inv_le_one_of_ne_bot hJ hJtop hJinv
  · intro htop
    apply le_antisymm _ Ideal.le_colon
    intro r hr
    have h1 : (1 : A) ∈ m ⊔ I := by rw [htop]; exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
    have hprod : r * (x + y) ∈ m := by
      rw [mul_add]
      exact m.add_mem (m.mul_mem_left r hx) (Submodule.mem_colon.mp hr y hy)
    rwa [hxy, mul_one] at hprod

end GaloisForLFunctions.HTGeometry
