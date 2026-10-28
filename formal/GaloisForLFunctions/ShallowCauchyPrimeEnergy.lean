import GaloisForLFunctions.ShallowCauchyPrimeEnergy.PoissonKernelDomination
import GaloisForLFunctions.ShallowCauchyPrimeEnergy.MultiscaleLorentzL2
import GaloisForLFunctions.ShallowCauchyPrimeEnergy.ShallowCauchyEnergyBound
import GaloisForLFunctions.ShallowCauchyPrimeEnergy.ShallowCauchyImplications

/-!
# Prime-Side Shallow Cauchy Energy at Critical Spacing

Umbrella for the unconditional prime-side theory of the `h`-shifted Cauchy Gram energy of shallow
strict-right zeros of `ξ` and `ζ` in a dyadic window `[T, 2T]`:

* **Poisson kernel domination and semigroup identity (`PoissonKernelDomination`):** pointwise
  domination of `4h · transverseCauchyKernel (h + a) (h + b) Δ` for `0 ≤ a, b ≤ h` and `2h ≤ R₀` by
  the width-`R₀` Lorentzian `4 R₀² / (R₀² + Δ²)`, and exact reduction of any finite Lorentzian pair
  sum to `(4 / (π R₀)) ∫ (G_{R₀/2}(t))² dt` via half-plane Poisson convolution.
* **Prime-cascade multiscale `L²` bound (`MultiscaleLorentzL2`):** dyadic shell decomposition of
  `G_{R₀/2}(t)` on `[T, 2T]` and unconditional `L²` control from the prime-side multiscale level-set
  measure (`exists_multiScale_narrowZeroSum_superlevel_volume_le`), yielding
  `Σ_{c₁, c₂ ∈ dyadicZeroWindow T} R₀² / (R₀² + (γ₁ − γ₂)²) ≤ C · (R₀ log T) · T log T` uniformly
  for `0 < R₀ ≤ 1/32` with `κ₂ ≤ R₀ log T`.
* **Shallow Cauchy energy bound (`ShallowCauchyEnergyBound`):** critical-line reflection saving on
  `XiRightUpperZeroCopy` cancelling the prefactor `4`, the uniform bound
  `h · xiShallowCauchyEnergy h T ≤ C · max(κ₂, 2 h log T) · T log T` for `0 < h ≤ 1/64`, and the
  critical-spacing resolution `xiShallowCauchyEnergy (1 / log T) T ≤ C · T (log T)²` together with
  multiplicity-weighted `finiteOfflineCauchyEnergy` bounds for shallow strict-right zeros of `ξ`
  and `ζ`.
* **Unconditional implications (`ShallowCauchyImplications`):** normalization by the Riemann–von
  Mangoldt count `N(T, 2T)`, uniform `α`-independent energy saturation for `h = α / log T` across
  `κ₂ / 2 ≤ α ≤ (log T) / 64`, squared-multiplicity and `K / log T` close-pair anti-clustering
  bounds for shallow off-line `ζ`-zeros, and the joint shallow-energy + exponential-deep-tail Ward
  budget combining the prime-side shallow bound with Selberg's two-length Barban–Vehov near-line
  density.
-/
