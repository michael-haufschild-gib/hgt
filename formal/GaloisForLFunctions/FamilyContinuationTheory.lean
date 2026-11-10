import GaloisForLFunctions.FamilyContinuationTheory.TwistedColumnsCorrelateThroughOneResidue
import GaloisForLFunctions.FamilyContinuationTheory.ContinuationFromACommonSignal
import GaloisForLFunctions.FamilyContinuationTheory.TheTwoLegsGiveTheRiemannHypothesis
import GaloisForLFunctions.FamilyContinuationTheory.TheSignalOfTheZetaKernelIsAMoebiusSum
import GaloisForLFunctions.FamilyContinuationTheory.TheOddPowerOfAGaussSumCarriesTheMoebiusSign
import GaloisForLFunctions.FamilyContinuationTheory.ThePlanarLargeSieve
import GaloisForLFunctions.FamilyContinuationTheory.TheLargeSieveOverTheEisensteinIntegers
import GaloisForLFunctions.FamilyContinuationTheory.TheNormCountOfTheEisensteinIntegers
import GaloisForLFunctions.FamilyContinuationTheory.TheEisensteinLatticeSumIsZetaTimesAnLFunction
import GaloisForLFunctions.FamilyContinuationTheory.TheSevenEighthsGeometryIsAVertex

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
* **The mean square of the additive polynomial.** The large sieve for points of the torus `ℝ²/ℤ²`
  separated in the maximum of the two circle distances; its form over the Eisenstein integers
  with the self-dual character `exp(2πi Tr(w/√−3))`; fractions `d/s` with `|s|² ≤ Y`, distinct
  modulo `ℤ[ω]`, are `1/Y`-separated, and the mean square over a row box of side `N` is at most
  `(2N + 2Y ∑_{k≤M} 1/k)² ∑ |c|²`.
* **The transfer to `ζ`.** The number of Eisenstein integers of norm `n` is `6 Σ_{d ∣ n} χ₃(d)`, and
  `Σ_{(m,n) ≠ 0} (m² − mn + n²)^{−s} = 6 ζ(s) L(s, χ₋₃)` for `Re s > 1`: the zeta function of
  `ℚ(√−3)` carries the zeros of `ζ`.
* **The budget of the compensated probe.** Low boundary `5/6 + M/12 − ℓ/6 + (M + ℓ − 1)₊/2` in the
  row length `M` and slot length `ℓ`; the face of zero retained length is paid by the tuple
  factor; the high exponent of the top rows is at most `−49/440640` at the published geometry and
  `−7/30672` in the bin `δ = 79/204`; every geometry with low boundary at most `7/8 − 1/4000` has
  a positive high exponent in that bin.
-/
