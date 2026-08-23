import GaloisForLFunctions.HTGeometry.TripticSourceDivisor

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Two meromorphic sheets with a specified product norm at one point. All local regularity and
nontriviality conditions are carried by the object rather than exposed as theorem premises. -/
structure MeromorphicNormPairAt (w : ℂ) where
  left : ℂ → ℂ
  right : ℂ → ℂ
  norm : ℂ → ℂ
  left_meromorphic : MeromorphicAt left w
  right_meromorphic : MeromorphicAt right w
  left_order_ne_top : meromorphicOrderAt left w ≠ ⊤
  right_order_ne_top : meromorphicOrderAt right w ≠ ⊤
  product_eq_norm : ∀ z : ℂ, left z * right z = norm z

namespace MeromorphicNormPairAt

variable {w : ℂ} (P : MeromorphicNormPairAt w)

/-- Exact divisor additivity for a meromorphic two-sheet norm identity. -/
theorem order_add :
    (meromorphicOrderAt P.left w).untop₀ +
        (meromorphicOrderAt P.right w).untop₀ =
      (meromorphicOrderAt P.norm w).untop₀ := by
  have hmul := untop₀_meromorphicOrderAt_mul P.left_meromorphic P.right_meromorphic
    P.left_order_ne_top P.right_order_ne_top
  have hfun : (fun z : ℂ => P.left z * P.right z) = P.norm :=
    funext P.product_eq_norm
  rw [hfun] at hmul
  exact hmul.symm

end MeromorphicNormPairAt

/-- A meromorphic norm pair at a point outside the norm divisor. -/
structure MeromorphicNormPairUnitAt (w : ℂ) extends MeromorphicNormPairAt w where
  norm_order_zero : (meromorphicOrderAt norm w).untop₀ = 0

namespace MeromorphicNormPairUnitAt

variable {w : ℂ} (P : MeromorphicNormPairUnitAt w)

/-- Away from the norm divisor, the two sheets have opposite local zero/pole orders. -/
theorem right_order_eq_neg_left :
    (meromorphicOrderAt P.right w).untop₀ =
      -(meromorphicOrderAt P.left w).untop₀ := by
  have hadd := P.toMeromorphicNormPairAt.order_add
  rw [P.norm_order_zero] at hadd
  omega

end MeromorphicNormPairUnitAt

end

end GaloisForLFunctions.HTGeometry
