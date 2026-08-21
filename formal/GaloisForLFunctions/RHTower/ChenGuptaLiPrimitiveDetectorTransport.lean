import GaloisForLFunctions.RHTower.ChenGuptaLiFiniteZeroDetector
import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveFiniteSum

open ArithmeticFunction

noncomputable section

namespace RHTower

/-- The finite CGL Möbius detector for an imprimitive nonprincipal character is exactly the
primitive-conductor detector with the original-level coprimality filter on its coefficient range.
This is finite-sum transport only; it does not assert an infinite Euler-product factorization. -/
theorem cglPrimitive_zeroDetectionMobiusPolynomial_eq_filtered
    (X n : ℕ) (χ : NonprincipalDirichletCharacter n) (z : ℂ) :
    zeroDetectionMobiusPolynomial X (n + 1) χ.1 z =
      ∑ d ∈ (Finset.Icc 1 (X + 1)).filter (fun d => d.Coprime (n + 1)),
        (moebius d : ℂ) *
          (cglPrimitiveCharacterReduction n χ).primitiveCharacter d * (d : ℂ) ^ (-z) := by
  unfold zeroDetectionMobiusPolynomial
  let S := Finset.Icc 1 (X + 1)
  have hsum := cglPrimitiveCharacterReduction_sum_eq_filteredPrimitive n χ S
    (fun d => (moebius d : ℂ) * (d : ℂ) ^ (-z))
  change (∑ d ∈ S, (moebius d : ℂ) * χ.1 d * (d : ℂ) ^ (-z)) = _
  calc
    (∑ d ∈ S, (moebius d : ℂ) * χ.1 d * (d : ℂ) ^ (-z)) =
        ∑ d ∈ S, ((moebius d : ℂ) * (d : ℂ) ^ (-z)) * χ.1 d := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = ∑ d ∈ S.filter (fun d => d.Coprime (n + 1)),
        ((moebius d : ℂ) * (d : ℂ) ^ (-z)) *
          (cglPrimitiveCharacterReduction n χ).primitiveCharacter d := hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      ring

/-- The finite CGL Dirichlet-series truncation for an imprimitive nonprincipal character is
exactly the primitive-conductor truncation with the original-level coprimality filter. -/
theorem cglPrimitive_zeroDetectionLTruncation_eq_filtered
    (Y n : ℕ) (χ : NonprincipalDirichletCharacter n) (z : ℂ) :
    zeroDetectionLTruncation Y (n + 1) χ.1 z =
      ∑ m ∈ (Finset.Icc 1 (Y + 1)).filter (fun m => m.Coprime (n + 1)),
        (cglPrimitiveCharacterReduction n χ).primitiveCharacter m * (m : ℂ) ^ (-z) := by
  unfold zeroDetectionLTruncation
  let S := Finset.Icc 1 (Y + 1)
  have hsum := cglPrimitiveCharacterReduction_sum_eq_filteredPrimitive n χ S
    (fun m => (m : ℂ) ^ (-z))
  change (∑ m ∈ S, χ.1 m * (m : ℂ) ^ (-z)) = _
  calc
    (∑ m ∈ S, χ.1 m * (m : ℂ) ^ (-z)) =
        ∑ m ∈ S, ((m : ℂ) ^ (-z)) * χ.1 m := by
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = ∑ m ∈ S.filter (fun m => m.Coprime (n + 1)),
        ((m : ℂ) ^ (-z)) * (cglPrimitiveCharacterReduction n χ).primitiveCharacter m := hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      ring

end RHTower
