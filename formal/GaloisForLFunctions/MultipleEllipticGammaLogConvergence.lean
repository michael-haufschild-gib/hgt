import GaloisForLFunctions.FinitePiProductSummability

/-!
# Absolute convergence of the all-order multiple elliptic-gamma logarithmic kernel

For every finite nome set strictly inside the unit disc, both halves of the parity-correct
multiple elliptic-gamma logarithmic kernel are absolutely summable.  The resulting kernel is an
actual convergent series on the full multi-index lattice.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

set_option maxHeartbeats 1000000

variable {ι : Type} [Fintype ι]

/-- The forward multi-geometric argument family is absolutely summable. -/
theorem summable_norm_multipleEllipticGammaForwardArgument
    {p : ι → ℂ} {x : ℂ} (hp : ∀ i, ‖p i‖ < 1) :
    Summable (fun n : ι → ℕ =>
      ‖multipleEllipticGammaForwardArgument p x n‖) := by
  have hweights : Summable (fun n : ι → ℕ =>
      ∏ i, ‖p i‖ ^ (n i + 1)) := by
    exact summable_fintype_pi_product_of_nonneg ι
      (fun i n => ‖p i‖ ^ (n + 1))
      (fun i => by
        have hi0 : 0 ≤ ‖p i‖ := norm_nonneg _
        simpa [pow_succ, mul_comm] using
          (summable_geometric_of_lt_one hi0 (hp i)).mul_left ‖p i‖)
      (fun i n => pow_nonneg (norm_nonneg _) _)
  have hscaled := hweights.mul_right ‖x‖⁻¹
  apply hscaled.congr
  intro n
  simp [multipleEllipticGammaForwardArgument, div_eq_mul_inv]

/-- The backward multi-geometric argument family is absolutely summable. -/
theorem summable_norm_multipleEllipticGammaBackwardArgument
    {p : ι → ℂ} {x : ℂ} (hp : ∀ i, ‖p i‖ < 1) :
    Summable (fun n : ι → ℕ =>
      ‖multipleEllipticGammaBackwardArgument p x n‖) := by
  have hweights : Summable (fun n : ι → ℕ =>
      ∏ i, ‖p i‖ ^ n i) := by
    exact summable_fintype_pi_product_of_nonneg ι
      (fun i n => ‖p i‖ ^ n)
      (fun i => summable_geometric_of_lt_one (norm_nonneg _) (hp i))
      (fun i n => pow_nonneg (norm_nonneg _) _)
  have hscaled := hweights.mul_right ‖x‖
  apply hscaled.congr
  intro n
  simp [multipleEllipticGammaBackwardArgument]

/-- The all-order logarithmic summand is absolutely summable. -/
theorem summable_multipleEllipticGammaLogSummand
    {p : ι → ℂ} {x : ℂ} (hp : ∀ i, ‖p i‖ < 1) :
    Summable (multipleEllipticGammaLogSummand p x) := by
  exact (summable_ellipticGammaLogAtom_of_summable_norm
      (summable_norm_multipleEllipticGammaForwardArgument hp)).add
    ((summable_ellipticGammaLogAtom_of_summable_norm
      (summable_norm_multipleEllipticGammaBackwardArgument hp)).mul_left
        (multipleEllipticGammaLogSign ι))

/-- The actual convergent all-order multiple elliptic-gamma logarithmic kernel. -/
def multipleEllipticGammaLogKernel (p : ι → ℂ) (x : ℂ) : ℂ :=
  ∑' n : ι → ℕ, multipleEllipticGammaLogSummand p x n

end

end GaloisForLFunctions
