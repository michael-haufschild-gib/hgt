import GaloisForLFunctions.FamilyContinuationTheory.TwistedColumnsCorrelateThroughOneResidue
import GaloisForLFunctions.FamilyContinuationTheory.TheRowTwistBecomesItsGaussSum
import GaloisForLFunctions.FamilyContinuationTheory.ACommonPrimeOfTwoColumnsGivesAJacobiSum
import GaloisForLFunctions.FamilyContinuationTheory.ContinuationFromACommonSignal
import GaloisForLFunctions.FamilyContinuationTheory.TheSignalExponentIsThePositivityLevel
import GaloisForLFunctions.FamilyContinuationTheory.TheSignalOfTheZetaKernelIsAMoebiusSum
import GaloisForLFunctions.FamilyContinuationTheory.TheSignalExponentIsTheZeroAbscissa
import GaloisForLFunctions.FamilyContinuationTheory.TheContinuationFrameHoldsForHeckeLFunctions
import GaloisForLFunctions.FamilyContinuationTheory.TheSignalOfAHeckeKernelIsASumOverSquarefreeIdeals
import GaloisForLFunctions.FamilyContinuationTheory.TheContinuationFrameCoversEveryRayClassCharacter
import GaloisForLFunctions.FamilyContinuationTheory.TheSignalOfTheGaussianKernelIsALogNormalWindow
import GaloisForLFunctions.FamilyContinuationTheory.TheHeckeFamilyOfTheRationalsContainsZeta
import GaloisForLFunctions.FamilyContinuationTheory.TheHeckeFamilyOfTheThirdCyclotomicFieldContainsZeta
import GaloisForLFunctions.FamilyContinuationTheory.TheHeightIsChosenAfterTheTarget
import GaloisForLFunctions.FamilyContinuationTheory.TheOddPowerOfAGaussSumCarriesTheMoebiusSign
import GaloisForLFunctions.FamilyContinuationTheory.TwoGaussSumsWithAQuadraticProductCarryTheMoebiusSign
import GaloisForLFunctions.FamilyContinuationTheory.ThePlanarLargeSieve
import GaloisForLFunctions.FamilyContinuationTheory.TheLargeSieveOverTheEisensteinIntegers
import GaloisForLFunctions.FamilyContinuationTheory.TheNormCountOfTheEisensteinIntegers
import GaloisForLFunctions.FamilyContinuationTheory.TheEisensteinLatticeSumIsZetaTimesAnLFunction
import GaloisForLFunctions.FamilyContinuationTheory.TheSevenEighthsGeometryIsAVertex
import GaloisForLFunctions.FamilyContinuationTheory.TheReturnTransferIsTheRiemannHypothesisUnderAStrip

/-!
# Family continuation theory

Umbrella for the route "a zero-free half-plane by continuing the reciprocals of a family of
`L`-functions across its rightmost zeros".

* **Continuation from a common signal.** A kernel `G` holomorphic on `Re s > 1` with decay on
  vertical strips, whose signal `(1/2π) ∫ G(2+it) Z^{2+it} dt` is `O(Z^b)`, extends to `Re s > b`;
  if `G L = E` with `E` zero-free, `L` has no zero in `Re s > b`. A sum with a direct bound and
  a comparison with the signal gives the half-plane right of the larger exponent. The frame holds
  for the `L`-functions of the nontrivial ray class characters of a number field, with the
  kernels `exp((s − c)²)/L(s, ψ)`; their signal is the smoothed Möbius sum
  `Σ_S (−1)^{|S|} ψ(∏ S) w(Z/N(∏ S))` over the finite sets of primes, with the log-normal weight
  `w(y) = (2√π)⁻¹ y^c exp(−(log y)²/4)`, and a bound `O(Z^b)` for it excludes the zeros of
  `L(s, ψ)` in `Re s > b`. With the pole-cleared functions
  `(s − 1) L(s, ψ)` the family step covers every ray class character, the trivial ones
  included, and produces `HeckeHalfPlane K σ₀`. Over `ℚ` the trivial character of the unit
  modulus is `ζ`: `HeckeHalfPlane ℚ σ₀` puts the zeros of `ξ` in `Re ρ ≤ σ₀`. A comparison with
  an auxiliary height `Z^τ`, with losses `(1 + Z^τ)^A` and `Z^B (Z^τ)^{−N}` for every small `τ`
  and every `N`, keeps half of its saving, whatever the orders `A`, `B`; the family step holds
  with comparisons of this form.
* **The signal of `ζ`.** The kernel `exp((s − c)²)/((s − 1)ζ(s))` is a signal kernel; a bound
  `O(Z^b)`, `b < 1`, for its signal gives the half-plane `Re s > b` and positivity of the dressed
  lag aggregate on large primes at every level above `b + ½`; bounds with every exponent above
  `½` give the Riemann hypothesis. The signal is the smoothed Möbius sum
  `Σ_n μ(n) · signal (poleKernel c) 2 (Z/n)`. Conversely a zero-free half-plane `Re s > Θ` bounds
  the signal by `O(Z^b)` for every `b > Θ`: the zero abscissa is at most `b` exactly when the
  signal is `O(Z^{b'})` for every `b' > b`.
* **Additive columns of residue characters.** The correlation of two columns of coprime moduli is
  one term; a weighted second moment over the rows is a multiplicative form in the frequency; at
  the frequencies on which the characters are trivial the terms add without cancellation. Poisson
  summation in the row of a column times a multiplicative row twist is one column value times the
  transform of the twist, for a character its Gauss sum. At a prime common to two columns with
  the same nonprincipal character the local factor of the correlation is `−χ(b/a)` at the
  frequencies prime to it and `(N − 1) χ(b/a)` at the others.
* **The sign of the source.** The `n`-th power of a Gauss sum of order `n > 2` is `−card F` for
  odd `n` and `χ(−1) · card F` for even `n`, modulo `(μ − 1)²` in `ℤ[μ]`: odd orders carry the
  Möbius sign, and three is the least of them. For two characters with quadratic product,
  `g(χ) g(φ) = J(χ, φ) g(χ φ)` with `J ≡ −1`: the row coefficient `χ` and the row twist `φ` of a
  probe are such a pair (cubic and sextic, order four twice, sextic and cubic).
* **The mean square of the additive polynomial.** The large sieve for points of the torus `ℝ²/ℤ²`
  separated in the maximum of the two circle distances; its form over the Eisenstein integers
  with the self-dual character `exp(2πi Tr(w/√−3))`; fractions `d/s` with `|s|² ≤ Y`, distinct
  modulo `ℤ[ω]`, are `1/Y`-separated, and the mean square over a row box of side `N` is at most
  `(2N + 2Y ∑_{k≤M} 1/k)² ∑ |c|²`; there are at most `(2 + 2Y ∑ 1/k)²` such fractions, which
  bounds the mean square for bounded coefficients.
* **The transfer to `ζ`.** The number of Eisenstein integers of norm `n` is `6 Σ_{d ∣ n} χ₃(d)`, and
  `Σ_{(m,n) ≠ 0} (m² − mn + n²)^{−s} = 6 ζ(s) L(s, χ₋₃)` for `Re s > 1`: the zeta function of
  `ℚ(√−3)` carries the zeros of `ζ`; with a Dirichlet character `χ` of the norm the sum is
  `6 L(s, χ) L(s, χ χ₋₃)`. For a number field `K` with `IsCyclotomicExtension {3} ℚ K` the ring
  of integers has the basis `1, η`, norm form `a² − ab + b²`, six units and `Σ_{d ∣ n} χ₋₃(d)`
  ideals of norm `n`; `ζ_K = ζ · L(·, χ₋₃)`, and `HeckeHalfPlane K σ₀` puts the zeros of `ξ` in
  `Re ρ ≤ σ₀`.
* **The budget of the compensated probe.** Low boundary `5/6 + M/12 − ℓ/6 + (M + ℓ − 1)₊/2` in the
  row length `M` and slot length `ℓ`; the face of zero retained length is paid by the tuple
  factor; the high exponent of the top rows is at most `−49/440640` at the published geometry and
  `−7/30672` in the bin `δ = 79/204`; every geometry with low boundary at most `7/8 − 1/4000` has
  a positive high exponent in that bin. In the bin of rows without zeros right of the line, summed
  trivially, every geometry with low boundary below `13/15` has a positive high exponent: the
  room inside the probe is `[13/15, 7/8]`. Designs with more row variables, or with frequencies
  of lower order and rows of larger conductor, have larger boundaries in the same model.
* **From a half-plane to the line.** The transfer from return-free intervals of the prime orbit to
  bounded prime traces follows from the Riemann hypothesis, and under a zero-free strip it is
  equivalent to it.
-/
