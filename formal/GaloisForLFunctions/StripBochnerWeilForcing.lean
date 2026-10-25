import GaloisForLFunctions.StripBochnerWeilForcing.StripBochnerShadows
import GaloisForLFunctions.StripBochnerWeilForcing.CollectivePoleRepulsion
import GaloisForLFunctions.StripBochnerWeilForcing.InfiniteGaugePoleRigidity

/-!
# Strip Bochner–Weil Forcing

Umbrella for the coupled strip Bochner–Weil form and its pole-budget forcing laws:

* **Strip shadows (`StripBochnerShadows`):** the multi-channel scale-height Bochner–Weil form
  `stripBochnerForm` unifying boundary divisor positive definiteness (`δ ↓ 0⁺`), scaling-surface
  `κ`-polar Castelnuovo–Severi defect positivity (`polarSurfaceOfPoleBudget`), and pole-budget
  monotonicity.
* **Collective multi-zero interior pole–repulsion (`CollectivePoleRepulsion`):** completed positive
  systems `CompletedPositiveSystem κ d F Λ`, dihedral orbit extraction inside Hadamard's zero-pair
  expansion, the master coupled strip pole–zero inequality, the sharp Følner collective interior
  threshold `κ < 2 * ∑_ℓ m_ℓ` with explicit sharpness witnesses at `κ = 2 r + 1`, and uniform `κ²`
  collar sparsity across heights.
* **Infinite multiplicative gauge collapse & simple-pole refund rigidity
  (`InfiniteGaugePoleRigidity`):** collapse of any infinite finite-abscissa multiplicative gauge
  with finite-order `(s(s − 1))^κ`-completion to a monic degree-`2 κ` polynomial (bounding whole-strip
  complex off-critical quartets by `⌊κ/2⌋`), and unconditional simple-pole (`κ = 1`) rigidity
  ruling out all nonzero nonnegative Laplace log-deformations of `ξ` even when arbitrary critical-zero
  refunds are permitted.

See `StripBochnerWeilForcing/README.md`.
-/
