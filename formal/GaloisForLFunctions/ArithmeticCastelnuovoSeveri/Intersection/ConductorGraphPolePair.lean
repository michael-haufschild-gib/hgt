import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.ConductorGraphContacts
import GaloisForLFunctions.SurfaceOfSpecZ.TheTwoHalfProducts
import Mathlib.Algebra.Polynomial.Reverse

/-!
# The pole pairing on the conductor graphs

The affine elimination equation for two graphs is their polynomial
difference. At infinity, reciprocal coordinates give the graph equations
`Z reverse(Gᵢ)(U) = Uⁱ`. Eliminating Z gives the minor below.
Its order at zero and the affine degree add to the polar bidegree,
while the content of the affine equation records the finite prime contact.
-/

noncomputable section

open Polynomial
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Elimination in the reciprocal coordinates U = 1/T and Z = 1/Y. -/
def infinityGraphMinor (i j : ℕ) : ℤ[X] :=
  (conductorGraph j).reverse * X^i - (conductorGraph i).reverse * X^j

private theorem infinityGraphMinor_order {i j : ℕ} (hij : i < j) :
    (infinityGraphMinor i j).natTrailingDegree = i := by
  let L := (conductorGraph j).reverse - (conductorGraph i).reverse * X^(j-i)
  have hj0 : j ≠ 0 := by omega
  have hG : conductorGraph j ≠ 0 := by
    intro h
    have e := conductorGraph_natDegree hj0
    rw [h, natDegree_zero] at e
    exact hj0 e.symm
  have h0 : L.coeff 0 ≠ 0 := by
    simp [L, coeff_mul_X_pow', (by omega : ¬ j-i ≤ 0), hG]
  have hL : L ≠ 0 := fun he => h0 (by rw [he, coeff_zero])
  have he : infinityGraphMinor i j = L * X^i := by
    rw [infinityGraphMinor, sub_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hij.le]
  rw [he, natTrailingDegree_mul_X_pow hL, natTrailingDegree_eq_zero.mpr (Or.inr h0), zero_add]

/-- The two geometric multiplicities give the polar bidegree for each distinct pair. -/
theorem conductorGraph_polar_degree {i j : ℕ} (hi : 0 < i) (hj : 0 < j) (hne : i ≠ j) :
    (conductorGraph i - conductorGraph j).natDegree + (infinityGraphMinor i j).natTrailingDegree =
      i+j := by
  have hlt {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
      (conductorGraph a - conductorGraph b).natDegree = b := by
    rw [natDegree_sub_eq_right_of_natDegree_lt, conductorGraph_natDegree hb.ne']
    rwa [conductorGraph_natDegree ha.ne', conductorGraph_natDegree hb.ne']
  rcases lt_or_gt_of_ne hne with hij | hji
  · rw [hlt hi hj hij, infinityGraphMinor_order hij, Nat.add_comm]
  · have he : infinityGraphMinor i j = -infinityGraphMinor j i := by
      rw [infinityGraphMinor, infinityGraphMinor, neg_sub]
    rw [he, natTrailingDegree_neg, infinityGraphMinor_order hji, ← neg_sub (conductorGraph j),
      natDegree_neg, hlt hj hi hji]

/-- The horizontal multiplicities and the vertical content of the same pair
recover the pole kernel and the prime-power contact simultaneously. -/
theorem conductorGraph_pole_and_prime {i t : ℕ} (hi : 0 < i) (ht : 1 < t) :
    ((conductorGraph i - conductorGraph (i*t)).natDegree +
        (infinityGraphMinor i (i*t)).natTrailingDegree : ℕ) =
      i + i*t ∧
    Real.sqrt ((i:ℝ)*(i*t : ℕ)) * (2 * Real.cosh ((Real.log i - Real.log (i*t : ℕ))/2)) =
      ((conductorGraph i - conductorGraph (i*t)).natDegree : ℝ) +
        (infinityGraphMinor i (i*t)).natTrailingDegree ∧
    Real.log (conductorContact i (i*t) : ℝ) = Λ t := by
  have ht0 : 0 < t := by omega
  have hit := Nat.mul_pos hi ht0
  have h := conductorGraph_polar_degree hi hit (lt_mul_of_one_lt_right hi ht).ne
  refine ⟨h, ?_, log_conductorContact_mul hi.ne' ht0.ne'⟩
  rw [SurfaceOfSpecZ.sqrt_mul_two_cosh (Nat.cast_pos.mpr hi) (Nat.cast_pos.mpr hit)]
  exact_mod_cast h.symm

#print axioms conductorGraph_pole_and_prime

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
