import GaloisForLFunctions.HTGeometry.InfiniteTorusCharacter

/-!
# Parseval's identity for finite character packets

Haar orthogonality gives the exact squared norm of a finite packet on a
countable product torus. The identity is independent of the number of
coordinates used by its characters.
-/

noncomputable section

open Complex Finset MeasureTheory
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

variable {I J : Type*} [Countable I] [Fintype J]

/-- Haar integration keeps precisely the equal-frequency terms in a packet. -/
theorem integral_norm_sq_torusCharacter_sum (n : J → I →₀ ℤ) (c : J → ℂ) :
    ((∫ x, ‖∑ j, c j * torusCharacter (n j) x‖ ^ 2 ∂torusHaar I : ℝ) : ℂ) =
      ∑ i, ∑ j, conj (c i) * c j * (if n i = n j then 1 else 0) := by
  classical
  have he (x : UnitAddTorus I) :
      ((‖∑ j, c j * torusCharacter (n j) x‖ ^ 2 : ℝ) : ℂ) =
        ∑ i, ∑ j, conj (c i) * c j * torusCharacter (n j - n i) x := by
    push_cast
    rw [← Complex.conj_mul', map_sum, sum_mul_sum]
    apply sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [map_mul, sub_eq_add_neg, torusCharacter_add_index, torusCharacter_neg_index]
    ring
  have hint (i j : J) : Integrable
      (fun x => conj (c i) * c j * torusCharacter (n j - n i) x) (torusHaar I) :=
    ((torusCharacter (n j - n i)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  rw [← integral_complex_ofReal]
  simp_rw [he]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp_rw [integral_finsetSum _ fun j _ => hint _ j, integral_const_mul,
    integral_torusCharacter, sub_eq_zero]
  apply sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [eq_comm (n j) (n i)]

/-- Distinct characters are an orthonormal family, on finite or infinite tori. -/
theorem integral_norm_sq_torusCharacter_sum_of_injective
    (n : J → I →₀ ℤ) (hn : Function.Injective n) (c : J → ℂ) :
    (∫ x, ‖∑ j, c j * torusCharacter (n j) x‖ ^ 2 ∂torusHaar I) =
      ∑ j, ‖c j‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  rw [integral_norm_sq_torusCharacter_sum]
  push_cast
  apply sum_congr rfl fun i _ => ?_
  rw [sum_eq_single i]
  · rw [if_pos rfl, mul_one, Complex.conj_mul']
  · intro j _ hj
    rw [if_neg (fun h => hj (hn h).symm), mul_zero]
  · simp

end GaloisForLFunctions.HTGeometry
