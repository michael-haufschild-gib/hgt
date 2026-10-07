import GaloisForLFunctions.HTGeometry.TernaryTranslatedPowers
import GaloisForLFunctions.HTGeometry.IntegerPolynomialRelationReduction
import GaloisForLFunctions.HTGeometry.IntegerComplexThreeRelation

/-!
# The integer-polynomial ternary degree restriction

The characteristic-three classifier applies to arbitrary nonzero integer
relations after primitive reduction. Explicit complex descent supplies such
a relation for three integer polynomials with a common unit coefficient.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Polynomial

/-- The degree restriction follows from a genuine integer relation, without primitivity assumptions. -/
theorem ternary_degree_of_integer_relation {n : ℕ} (hn : 0 < n) (A B D : ℤ[X])
    (hA : A.map (Int.castRingHom (ZMod 3)) = X ^ n)
    (hB : B.map (Int.castRingHom (ZMod 3)) = (X - 1) ^ n)
    (hD : D.map (Int.castRingHom (ZMod 3)) = (X + 1) ^ n)
    (u v w : ℤ) (hne : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0)
    (hrel : C u * A + C v * B + C w * D = 0) : ∃ e : ℕ, n = 3 ^ e := by
  have hc : ∃ i : Fin 3, (![u, v, w] : Fin 3 → ℤ) i ≠ 0 := by
    rcases hne with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  obtain ⟨d, ⟨i, hi⟩, hd⟩ := exists_nonzero_mod_three_polynomial_relation
    (![A, B, D] : Fin 3 → ℤ[X]) (![u, v, w] : Fin 3 → ℤ) hc
    (by simpa [Fin.sum_univ_three] using hrel)
  have hmod : C (d 0) * X ^ n + C (d 1) * (X - 1) ^ n + C (d 2) * (X + 1) ^ n =
      (0 : (ZMod 3)[X]) := by
    simpa [Fin.sum_univ_three, hA, hB, hD] using hd
  rcases (ternary_translated_power_relation_iff hn (d 0) (d 1) (d 2)).mp hmod with
    hz | hp
  · obtain ⟨h0, h1, h2⟩ := hz
    fin_cases i <;> contradiction
  · exact hp.1

/-- Complex dependence of the monic integer fibers already forces a power-of-three degree. -/
theorem ternary_degree_of_complex_relation {n : ℕ} (hn : 0 < n) (A B D : ℤ[X])
    (hAn : A.coeff n = 1) (hBn : B.coeff n = 1) (hDn : D.coeff n = 1)
    (hA : A.map (Int.castRingHom (ZMod 3)) = X ^ n)
    (hB : B.map (Int.castRingHom (ZMod 3)) = (X - 1) ^ n)
    (hD : D.map (Int.castRingHom (ZMod 3)) = (X + 1) ^ n)
    (a b c : ℂ) (hc : c ≠ 0)
    (hrel : C a * A.map (Int.castRingHom ℂ) + C b * B.map (Int.castRingHom ℂ) +
      C c * D.map (Int.castRingHom ℂ) = 0) : ∃ e : ℕ, n = 3 ^ e := by
  obtain ⟨u, v, w, hne, hrel⟩ :=
    integer_relation_of_complex_three_relation A B D n hAn hBn hDn a b c hc hrel
  exact ternary_degree_of_integer_relation hn A B D hA hB hD u v w hne hrel

end
end GaloisForLFunctions.HTGeometry
