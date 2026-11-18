import GaloisForLFunctions.PrimeExponentialSums.VinogradovAtRationals
import GaloisForLFunctions.PrimeExponentialSums.VaughanIdentityForEulerProducts
import GaloisForLFunctions.PrimeExponentialSums.VinogradovMinorArc
import GaloisForLFunctions.PrimeExponentialSums.PrimeSumsByParts
import GaloisForLFunctions.PrimeExponentialSums.MajorArcs
import GaloisForLFunctions.PrimeExponentialSums.PolynomialMajorArcs
import GaloisForLFunctions.PrimeExponentialSums.DyadicPrimeSums
import GaloisForLFunctions.PrimeExponentialSums.PrimesOffMajorArcs
import GaloisForLFunctions.PrimeExponentialSums.ReciprocalPhasesNearTheSquareRoot
import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsOfReciprocalPrimes
import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsOnIntegerReciprocalBlocks
import GaloisForLFunctions.PrimeExponentialSums.ReciprocalProductsOnShortFactorIntervals
import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsOnReciprocalProductRectangles
import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsAcrossAReciprocalProductWindow
import GaloisForLFunctions.PrimeExponentialSums.DivisorDilationsInSquareRootProductWindows

/-!
# Exponential sums over primes

`S_N(β) = Σ_{N < p ≤ 2N} e(pβ)` is `o(#{N < p ≤ 2N})` uniformly for `β` at distance more than `W/N`
from every rational of denominator at most `Q₀` (`exists_off_major_arcs`).

* **Minor arcs** (`VinogradovAtRationals`, `VinogradovMinorArc`): Vaughan's identity at a rational
  `a/q` of any denominator gives `|Σ_{n ≤ N} Λ(n) e(an/q)| ≤ N/(log N)^A` for
  `(log N)^{2A+12} ≤ q ≤ N/(log N)^{2A+12}`.
* **Partial summation** (`PrimeSumsByParts`): from `Λ`-weighted windows to prime sums, and the
  untwisted prime sum from the prime number theorem with a log-power error.
* **Major arcs** (`MajorArcs`): character expansion of `e(pa/q)` with the Ramanujan sum as principal
  coefficient, and Siegel–Walfisz in short windows for the nonprincipal characters.
* **Assembly** (`DyadicPrimeSums`, `PrimesOffMajorArcs`): Dirichlet approximation in lowest terms
  and the case split `q ≥ (2 log N)^14`, `Q₀ < q < (2 log N)^14`, `q ≤ Q₀`.
-/
