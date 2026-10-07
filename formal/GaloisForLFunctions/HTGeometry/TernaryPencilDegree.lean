import GaloisForLFunctions.HTGeometry.TernaryPolynomialDegree
import GaloisForLFunctions.HTGeometry.IntegerFiberRoots
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Degree of a rational map with three labeled integer fibers

The full fiber over each of three targets is contained in its prescribed
integer residue class modulo three. If none of those fibers contains infinity,
the positive projective degree is a power of three. Canonical rational-function
numerator and denominator give a direct wrapper for actual rational maps.

Complete root multisets retain all multiplicities. Complex pencil dependence is
descended to integers and primitively reduced before invoking characteristic
three. No assertion that every allowed degree occurs in characteristic zero is
made, and no conclusion about transcendental parameters follows.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Polynomial

/-- The homogeneous fiber condition at infinity preserves the full pencil degree. -/
theorem pencil_natDegree_of_infinity_avoided (P Q : ℂ[X]) (t : ℂ)
    (hinf : P.coeff (max P.natDegree Q.natDegree) ≠
      t * Q.coeff (max P.natDegree Q.natDegree)) :
    (P - C t * Q).natDegree = max P.natDegree Q.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_sub_le _ _).trans
      (max_le (le_max_left _ _) ((natDegree_C_mul_le _ _).trans (le_max_right _ _)))
  · simpa only [coeff_sub, coeff_C_mul] using sub_ne_zero.mpr hinf

/-- Three complete labeled complex fibers force a power-of-three pencil degree. -/
theorem ternary_labeled_pencil_degree (P Q : ℂ[X]) (t₀ t₁ t₂ : ℂ)
    (ht : t₀ ≠ t₁) (hn : 0 < max P.natDegree Q.natDegree)
    (hinf₀ : P.coeff (max P.natDegree Q.natDegree) ≠ t₀ * Q.coeff (max P.natDegree Q.natDegree))
    (hinf₁ : P.coeff (max P.natDegree Q.natDegree) ≠ t₁ * Q.coeff (max P.natDegree Q.natDegree))
    (hinf₂ : P.coeff (max P.natDegree Q.natDegree) ≠ t₂ * Q.coeff (max P.natDegree Q.natDegree))
    (h₀ : ∀ z : ℂ, P.eval z = t₀ * Q.eval z → ∃ k : ℤ, z = k ∧ (k : ZMod 3) = 0)
    (h₁ : ∀ z : ℂ, P.eval z = t₁ * Q.eval z → ∃ k : ℤ, z = k ∧ (k : ZMod 3) = 1)
    (h₂ : ∀ z : ℂ, P.eval z = t₂ * Q.eval z → ∃ k : ℤ, z = k ∧ (k : ZMod 3) = -1) :
    ∃ e : ℕ, max P.natDegree Q.natDegree = 3 ^ e := by
  let f₀ := P - C t₀ * Q
  let f₁ := P - C t₁ * Q
  let f₂ := P - C t₂ * Q
  have hd₀ : f₀.natDegree = max P.natDegree Q.natDegree :=
    pencil_natDegree_of_infinity_avoided P Q t₀ hinf₀
  have hd₁ : f₁.natDegree = max P.natDegree Q.natDegree :=
    pencil_natDegree_of_infinity_avoided P Q t₁ hinf₁
  have hd₂ : f₂.natDegree = max P.natDegree Q.natDegree :=
    pencil_natDegree_of_infinity_avoided P Q t₂ hinf₂
  have hf₀ : f₀ ≠ 0 := by
    intro h
    have hdeg : f₀.natDegree = 0 := by rw [h, natDegree_zero]
    exact (ne_of_gt hn) (hd₀.symm.trans hdeg)
  have hf₁ : f₁ ≠ 0 := by
    intro h
    have hdeg : f₁.natDegree = 0 := by rw [h, natDegree_zero]
    exact (ne_of_gt hn) (hd₁.symm.trans hdeg)
  have hf₂ : f₂ ≠ 0 := by
    intro h
    have hdeg : f₂.natDegree = 0 := by rw [h, natDegree_zero]
    exact (ne_of_gt hn) (hd₂.symm.trans hdeg)
  obtain ⟨A, hAm, hAd, hAf, hAr⟩ := integer_polynomial_of_labeled_complex_roots f₀ 0 hf₀
    (fun z hz => h₀ z (by simpa [f₀, sub_eq_zero] using hz))
  obtain ⟨B, hBm, hBd, hBf, hBr⟩ := integer_polynomial_of_labeled_complex_roots f₁ 1 hf₁
    (fun z hz => h₁ z (by simpa [f₁, sub_eq_zero] using hz))
  obtain ⟨D, hDm, hDd, hDf, hDr⟩ := integer_polynomial_of_labeled_complex_roots f₂ (-1) hf₂
    (fun z hz => h₂ z (by simpa [f₂, sub_eq_zero] using hz))
  have hAn : A.coeff (max P.natDegree Q.natDegree) = 1 := by
    rw [← hd₀, ← hAd]
    exact hAm.coeff_natDegree
  have hBn : B.coeff (max P.natDegree Q.natDegree) = 1 := by
    rw [← hd₁, ← hBd]
    exact hBm.coeff_natDegree
  have hDn : D.coeff (max P.natDegree Q.natDegree) = 1 := by
    rw [← hd₂, ← hDd]
    exact hDm.coeff_natDegree
  have hrel : C ((t₁ - t₂) * f₀.leadingCoeff) * A.map (Int.castRingHom ℂ) +
      C ((t₂ - t₀) * f₁.leadingCoeff) * B.map (Int.castRingHom ℂ) +
      C ((t₀ - t₁) * f₂.leadingCoeff) * D.map (Int.castRingHom ℂ) = 0 := by
    have hp : C (t₁ - t₂) * f₀ + C (t₂ - t₀) * f₁ + C (t₀ - t₁) * f₂ = 0 := by
      dsimp [f₀, f₁, f₂]
      simp only [map_sub]
      ring
    rw [hAf, hBf, hDf] at hp
    simpa only [map_mul, mul_assoc] using hp
  exact ternary_degree_of_complex_relation hn A B D hAn hBn hDn
    (by simpa [hd₀] using hAr) (by simpa [hd₁] using hBr)
    (by simpa [hd₂] using hDr) _ _ _
    (mul_ne_zero (sub_ne_zero.mpr ht) (leadingCoeff_ne_zero.mpr hf₂)) hrel

/-- The same law for the canonical coprime numerator and denominator of an actual rational function. -/
theorem ternary_labeled_rational_degree (V : RatFunc ℂ) (t₀ t₁ t₂ : ℂ)
    (ht : t₀ ≠ t₁) (hn : 0 < max V.num.natDegree V.denom.natDegree)
    (hinf₀ : V.num.coeff (max V.num.natDegree V.denom.natDegree) ≠
      t₀ * V.denom.coeff (max V.num.natDegree V.denom.natDegree))
    (hinf₁ : V.num.coeff (max V.num.natDegree V.denom.natDegree) ≠
      t₁ * V.denom.coeff (max V.num.natDegree V.denom.natDegree))
    (hinf₂ : V.num.coeff (max V.num.natDegree V.denom.natDegree) ≠
      t₂ * V.denom.coeff (max V.num.natDegree V.denom.natDegree))
    (h₀ : ∀ z : ℂ, V.num.eval z = t₀ * V.denom.eval z → ∃ k : ℤ, z = k ∧ (k : ZMod 3) = 0)
    (h₁ : ∀ z : ℂ, V.num.eval z = t₁ * V.denom.eval z → ∃ k : ℤ, z = k ∧ (k : ZMod 3) = 1)
    (h₂ : ∀ z : ℂ, V.num.eval z = t₂ * V.denom.eval z → ∃ k : ℤ, z = k ∧ (k : ZMod 3) = -1) :
    ∃ e : ℕ, max V.num.natDegree V.denom.natDegree = 3 ^ e :=
  ternary_labeled_pencil_degree V.num V.denom t₀ t₁ t₂ ht hn hinf₀ hinf₁ hinf₂ h₀ h₁ h₂

end
end GaloisForLFunctions.HTGeometry
