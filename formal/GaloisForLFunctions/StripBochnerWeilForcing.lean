import GaloisForLFunctions.StripBochnerWeilForcing.StripBochnerShadows
import GaloisForLFunctions.StripBochnerWeilForcing.CollectivePoleRepulsion
import GaloisForLFunctions.StripBochnerWeilForcing.InfiniteGaugePoleRigidity
import GaloisForLFunctions.StripBochnerWeilForcing.StripReflectionRigidity
import GaloisForLFunctions.StripBochnerWeilForcing.SharpHalfPoleCollar

/-!
# Strip Bochner–Weil Forcing

Umbrella for the coupled strip Bochner–Weil form and its five unconditional pole-budget forcing
laws:

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
* **Reference-free strip reflection & the `κ = 1` phase transition (`StripReflectionRigidity`):**
  direct critical-strip reflection cancelling `(s(s − 1))^κ` and `logDeriv Λ` without reference `ξ`,
  unconditional realization of both real and complex off-critical zeros in `CompletedPositiveSystem 2 1`,
  impossibility of entire (`κ = 0`) Laplace-positive completions without finite-order assumptions, and
  the archimedean real-zero budget `4 ord_{1/2}(Λ) + 8 ∑_{x ∈ X} ord_x(Λ) + 5 d < 9 κ` forcing
  `5 d < 9 κ`, `κ ≥ 1`, `κ = 1 → d = 1`, and complete real-line nonvanishing `∀ x : ℝ, Λ x ≠ 0` at `κ = 1`.
* **Iterated box wavepackets & sharp `⌊κ / 2⌋` collar sparsity (`SharpHalfPoleCollar`):**
  polynomial-scale iterated discrete box convolutions eliminating both the `√r` star loss (`κ² → ⌊κ/2⌋`)
  and all `Δ`-separation / low-ordinate cutoffs, establishing `2 * ∑_{z ∈ Z} ord_z(Λ) ≤ κ` across all
  `0 < Im z ≤ T`, `Re z > 1 − sharpCollarWidth κ d T` (`≍_κ 1 / (d log(3 + T))`), and an exception-free
  zero-free collar across all `|Im z| ≤ T` at `κ = 1`.

See `StripBochnerWeilForcing/README.md`.
-/
