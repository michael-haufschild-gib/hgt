import GaloisForLFunctions.FamilyContinuationTheory.TwistedColumnsCorrelateThroughOneResidue
import GaloisForLFunctions.FamilyContinuationTheory.ContinuationFromACommonSignal
import GaloisForLFunctions.FamilyContinuationTheory.TheTwoLegsGiveTheRiemannHypothesis
import GaloisForLFunctions.FamilyContinuationTheory.TheSignalOfTheZetaKernelIsAMoebiusSum
import GaloisForLFunctions.FamilyContinuationTheory.TheOddPowerOfAGaussSumCarriesTheMoebiusSign

/-!
# Family continuation theory

Umbrella for the route "a zero-free half-plane by continuing the reciprocals of a family of
`L`-functions across its rightmost zeros, then from a half-plane to the line".

* **Continuation from a common signal.** A kernel `G` holomorphic on `Re s > 1` with decay on
  vertical strips, whose signal `(1/2π) ∫ G(2+it) Z^{2+it} dt` is `O(Z^b)`, extends to `Re s > b`;
  if `G L = E` with `E` zero-free, `L` has no zero in `Re s > b`. A sum with a direct bound and
  a comparison with the signal gives the half-plane right of the larger exponent.
* **The two legs for `ζ`.** The kernel `exp((s − c)²)/((s − 1)ζ(s))` is a signal kernel; a bound
  `O(Z^b)`, `b < 1`, for its signal gives the half-plane `Re s > b`; with positivity of the dressed
  lag aggregate at level one it gives the Riemann hypothesis. The signal is the smoothed Möbius
  sum `Σ_n μ(n) · signal (poleKernel c) 2 (Z/n)`.
* **Additive columns of residue characters.** The correlation of two columns of coprime moduli is
  one term; a weighted second moment over the rows is a multiplicative form in the frequency; at
  the frequencies on which the characters are trivial the terms add without cancellation.
* **The sign of the source.** The `n`-th power of a Gauss sum of order `n > 2` is `−card F` for
  odd `n` and `χ(−1) · card F` for even `n`, modulo `(μ − 1)²` in `ℤ[μ]`: odd orders carry the
  Möbius sign, and three is the least of them.
-/
