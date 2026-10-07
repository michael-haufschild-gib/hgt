import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Explicit integer descent of a complex three-term relation

A common unit coefficient turns a complex linear relation into an affine
relation. One differing integer coefficient then eliminates the complex
scalars and produces a nonzero integer relation without matrix base change.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Polynomial

/-- Explicit integral descent of a three-term complex relation with a common unit coefficient. -/
theorem integer_relation_of_complex_three_relation (A B D : ℤ[X]) (n : ℕ)
    (hA : A.coeff n = 1) (hB : B.coeff n = 1) (hD : D.coeff n = 1)
    (a b c : ℂ) (hc : c ≠ 0)
    (hrel : C a * A.map (Int.castRingHom ℂ) + C b * B.map (Int.castRingHom ℂ) +
      C c * D.map (Int.castRingHom ℂ) = 0) :
    ∃ u v w : ℤ, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧ C u * A + C v * B + C w * D = 0 := by
  by_cases hBA : B = A
  · refine ⟨1, -1, 0, Or.inl one_ne_zero, ?_⟩
    simp [hBA]
  have hk : ∃ k, B.coeff k ≠ A.coeff k := by
    by_contra h
    push Not at h
    exact hBA (Polynomial.ext h)
  obtain ⟨k, hk⟩ := hk
  let d : ℤ := B.coeff k - A.coeff k
  let e : ℤ := D.coeff k - A.coeff k
  have hd : d ≠ 0 := sub_ne_zero.mpr hk
  have hcoeff (j : ℕ) :
      a * (A.coeff j : ℂ) + b * (B.coeff j : ℂ) + c * (D.coeff j : ℂ) = 0 := by
    simpa using congrArg (fun p : ℂ[X] => p.coeff j) hrel
  have hsum : a + b + c = 0 := by simpa [hA, hB, hD] using hcoeff n
  have hdiff (j : ℕ) :
      b * ((B.coeff j : ℂ) - A.coeff j) +
        c * ((D.coeff j : ℂ) - A.coeff j) = 0 := by
    linear_combination hcoeff j - (A.coeff j : ℂ) * hsum
  refine ⟨e - d, -e, d, Or.inr (Or.inr hd), ?_⟩
  ext j
  simp only [coeff_add, coeff_C_mul, coeff_zero]
  have hprod : c * (((e - d) * A.coeff j + (-e) * B.coeff j + d * D.coeff j : ℤ) : ℂ) = 0 := by
    dsimp [d, e]
    push_cast
    linear_combination ((B.coeff k : ℂ) - A.coeff k) * hdiff j -
      ((B.coeff j : ℂ) - A.coeff j) * hdiff k
  exact_mod_cast (mul_eq_zero.mp hprod).resolve_left hc

end
end GaloisForLFunctions.HTGeometry
