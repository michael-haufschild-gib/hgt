import GaloisForLFunctions.AdelicKreinGeometry.Haar.PositivePart
import GaloisForLFunctions.AdelicKreinGeometry.Haar.SplittingUniqueness
import GaloisForLFunctions.ArithmeticPositiveDuality.TheExtremalsOfTheHeckeLawAreTwistedHaarStates

/-!
# Canonical positive-plus-slope splitting

An integer-invariant finite-index Haar kernel has a unique positive Haar part and Hermitian slope part. The slope part carries exactly the original negative index.
-/

open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The slope coefficient left after removing the canonical positive Haar part. -/
def haarSlopePart (k : AffineGroupQ → ℂ) (hp : ∀ g, k (g * translation 1) = k g)
    (u : ℚˣ) : ℂ := k (dilation u) - haarPositivePart k hp (dilation u)

/-- The discarded coefficient depends only on slope. -/
theorem haarPositivePart_add_slope {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (g : AffineGroupQ) :
    k g = haarPositivePart k hp g + haarSlopePart k hp (slopeUnit g) := by
  have h := haarPositivePart_remainder_translation hk hi hs hp (affShift g) (dilation (slopeUnit g))
  have hg : translation (affShift g) * dilation (slopeUnit g) = g :=
    (eq_translation_mul_dilation g).symm
  rw [hg] at h
  change k g = haarPositivePart k hp g +
    (k (dilation (slopeUnit g)) - haarPositivePart k hp (dilation (slopeUnit g)))
  linear_combination h

/-- The slope remainder is Hermitian. -/
theorem haarSlopePart_hermitian {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) : IsHermKernel (haarSlopePart k hp) := by
  have hpos := haarPositivePart_posDef hk hi hs hp
  intro u
  change k (dilation u⁻¹) - haarPositivePart k hp (dilation u⁻¹) =
    (starRingEnd ℂ) (k (dilation u) - haarPositivePart k hp (dilation u))
  rw [map_inv, hk, hpos.1, map_sub]

/-- Removing the canonical positive Haar part preserves the entire negative index. -/
theorem negIndex_haarSlopePart {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) : negIndex (haarSlopePart k hp) = negIndex k := by
  have h := negIndex_add_slope_of_integer_successor (haarPositivePart_posDef hk hi hs hp)
    (haarPositivePart_hasIntegerSuccessor hk hi hs hp) (haarSlopePart k hp)
    (haarSlopePart_hermitian hk hi hs hp)
  have he : (fun g => haarPositivePart k hp g + haarSlopePart k hp (slopeUnit g)) = k :=
    funext fun g => (haarPositivePart_add_slope hk hi hs hp g).symm
  rw [he] at h
  exact h.symm

/-- Every integer-invariant finite-index Haar kernel has a unique positive-plus-slope decomposition. -/
theorem exists_unique_positive_haar_slope_split {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) :
    ∃ p : AffineGroupQ → ℂ, ∃ ψ : ℚˣ → ℂ,
      IsPosDefKernel p ∧ HasIntegerSuccessor p ∧ IsHermKernel ψ ∧
      (∀ g, k g = p g + ψ (slopeUnit g)) ∧ negIndex ψ = negIndex k ∧
      ∀ (p' : AffineGroupQ → ℂ) (ψ' : ℚˣ → ℂ),
        IsPosDefKernel p' → HasIntegerSuccessor p' → IsHermKernel ψ' →
        (∀ g, k g = p' g + ψ' (slopeUnit g)) → p' = p ∧ ψ' = ψ := by
  refine ⟨haarPositivePart k hp, haarSlopePart k hp, haarPositivePart_posDef hk hi hs hp,
    haarPositivePart_hasIntegerSuccessor hk hi hs hp, haarSlopePart_hermitian hk hi hs hp,
    haarPositivePart_add_slope hk hi hs hp, negIndex_haarSlopePart hk hi hs hp, ?_⟩
  intro p' ψ' hp' hs' hψ' he'
  exact positive_haar_slope_split_unique hp' (haarPositivePart_posDef hk hi hs hp)
    hs' (haarPositivePart_hasIntegerSuccessor hk hi hs hp) hψ'
    (haarSlopePart_hermitian hk hi hs hp)
    (fun g => (he' g).symm.trans (haarPositivePart_add_slope hk hi hs hp g))

#print axioms haarPositivePart_add_slope
#print axioms negIndex_haarSlopePart
#print axioms exists_unique_positive_haar_slope_split
end GaloisForLFunctions.AdelicKreinGeometry
