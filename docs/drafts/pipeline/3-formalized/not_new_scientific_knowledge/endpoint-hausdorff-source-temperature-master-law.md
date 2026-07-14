# Endpoint Hausdorff source-temperature master law

- **ID:** `endpoint-hausdorff-source-temperature-master-law`
- **Stage:** 3-formalized
- **Type:** quantitative source-divisor-temperature master theorem
- **Scientific status:** integrated RH-route theorem; novelty not claimed
- **Lean sources:**
  - `formal/GaloisForLFunctions/RHTower/PrimeArchScaledHausdorffDivisorValueRelation.lean`
  - `formal/GaloisForLFunctions/RHTower/PrimeArchEndpointHausdorffTemperatureMaster.lean`

## Master theorem

Put

\[
R_*=\frac{C}{1-C},\qquad
C=2+\gamma_E-\log(4\pi),
\]

and let

\[
D_*(k,r)=\sum_{j=0}^r(-1)^j\binom rj
R_*^{r-j}\mu_{k+j}
\]

be the endpoint-calibrated Hausdorff differences of the normalized prime--Gamma moment sequence.
For the reciprocal-square Xi coordinate

\[
\lambda_\rho=-\frac4{(2\rho-1)^2},
\]

every entry has the exact divisor-value representation

\[
D_*(k,r)=\Re\sum_\rho
\lambda_\rho^{k+1}(R_*-\lambda_\rho)^r.       \tag{1}
\]

The endpoint quartet and thermal-orientation estimates place `lambda_rho` and
`R_*-lambda_rho` in opposite narrow sectors.  Their arguments therefore cancel rather than add.
This proves the full rectangle

\[
\boxed{D_*(k,r)\ge0\qquad(0\le k\le13,\ 0\le r\le43).} \tag{2}
\]

Thus 616 source inequalities are unconditional.  Define the complementary tail condition

\[
\mathsf T_*:\quad
D_*(k,r)\ge0\quad\text{whenever }k>13\text{ or }r>43.
\]

For every fixed logarithmic aperture and every admissible prime--polar cutoff, the following are
equivalent:

\[
\boxed{
\mathsf T_*
\Longleftrightarrow \mathrm{RH}
\Longleftrightarrow \sigma_{\rm abs}(S_{L,N}^-)\le1
\Longleftrightarrow
\sum_{n\le X}S_{L,N}^-(n)=O_\varepsilon(X^{1+\varepsilon})
\quad(\varepsilon>0)
\Longleftrightarrow
\text{finite KMS/Wightman local moment closure}.}
\tag{3}
\]

Equations `(1)`--`(3)` are one theorem, not two parallel routes.  The prime--polar source,
reciprocal-square divisor, calibrated Hausdorff array, and finite-temperature closure are four
coordinates on the same object.  The unconditional rectangle is genuine progress on the missing
estimate; the remaining RH-bearing datum is exactly the cofinal tail outside that rectangle.

## Positive carrier statement

A successful construction must carry a cofinal section of the complementary tail `T_*`.  It may
do so through source abscissae, divisor values, Hausdorff differences, or finite KMS systems, but
the 616-condition rectangle no longer consumes any RH input.

## Formal theorem surface

- `scaledHausdorffMomentDifference_eq_re_xiCentralSum`
- `re_xiCentral_scaledBasis_rectangle_nonneg`
- `scaledPrimeArchEndpointHausdorffDifference_rectangle_nonnegative`
- `scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_rectangleTailNonnegative`
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_rectangleHausdorffTailNonnegative`
- `primeArchEndpointHausdorffTailNonnegative_iff_riemannHypothesis`
- `primeArchEndpointHausdorffTailNonnegative_iff_cumulativeNegativeMassCriticalGrowth`
- `primeArchEndpointHausdorffTailNonnegative_iff_finiteKMSLocalMomentClosure`
- `primeArchEndpointHausdorffSourceTemperatureMaster`

The theorem surface contains no project axioms or placeholders.

## Remaining research

The next estimate must be cofinal, not another isolated finite block.  The most promising target is
a propagation law showing that positivity on the proved rectangle, together with one
source-specific recurrence or total-positivity constraint, forces the entire tail `T_*`.
