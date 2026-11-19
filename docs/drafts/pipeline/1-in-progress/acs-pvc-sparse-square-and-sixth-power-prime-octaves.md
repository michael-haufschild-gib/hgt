# Square and sixth-power samples of the reciprocal prime octave

For \(r\ge2\) an integer, set \(e_n=\sum_{n/2<k\le n}\Lambda(k)/k-\log2\) and \(D_r^\pm(K)=\sum_{m=1}^K(e_{2m^r})^\pm\). The paper result is
\[
 \lim_{K\to\infty}\frac{\log(1+D_r^\pm(K))}{\log K}
 =\max\{0,1-r(1-\Theta)\}.
\]
Thus a subpower bound on the total negative error at the **sixth powers** on arbitrarily large prefixes implies \(|B(N)|\ll N^{11/3}\) at every endpoint. At the **squares** the analogous bound is equivalent to RH. Each \(\varepsilon>0\) may use its own unbounded sequence with \(D_r^-(K)\le C_\varepsilon K^\varepsilon\).

**Cost of sampling.** Put \(x_m=2m^r\). For either sign \(f(y)=y^\pm\), replacing \(f(e_n)\) by \(f(e_{x_m})\) on \(x_m\le n<x_{m+1}\) costs at most the cell length times the total variation there. The jumps at \(n=k\) and \(n=2k\) each have size at most \(\Lambda(k)/k\) before combining coincident jumps. The length of their cell is \(O_r(k^{1-1/r})\). Through \(x_K\) the total error is therefore
\[
 O_r\!\left(1+\sum_{k\le2K^r}\frac{\Lambda(k)}{k^{1/r}}\right)=O_r(K^{r-1})
\]
by partial summation of \(\psi(x)\ll x\). Equivalently put \(P_m=\psi(2m^r)+\psi(m^r)\). The cell ending at \(2m^r\) costs at most \(C_r(P_m-P_{m-1})/m\) for \(m\ge2\). Discrete Abel summation and \(P_m\le21m^r\) give the same result with both endpoints. Each cell has at most \(O_r(K^{r-1})\) entries. At any right zero of real part \(\beta>1-1/r\), the all-terminal lower bound for the chosen sign then gives \(D_r^\pm(K)\gg_{r,\rho}K^{1-r(1-\beta)}\) for every sufficiently large \(K\). The opposite inequality for the growth exponent follows by summing \(e_{2m^r}=O_t(m^{-r(1-t)})\) for \(\Theta<t<1\); when \(\Theta=1\) use the bounded octave mass. [Formal sign-mass bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/BothSignsOfTheReciprocalPrimeOctave.lean#L579)

**Integer product with a short cofactor.** At the \(m\)-th sample take \(M=m^r\), \(X=m^{r+1}\). Replacing \((e_{2M})^-\) by \((\log2-\log Q_M(X)/X)^+\) costs \(O(M/X)=O(1/m)\), for a total of \(O(\log(2K))\). Removing proper powers costs \(O(M^{-1/2})\) per sample, again within this allowance. The resulting ordinary product runs over \(u\le m^{r+1}\) with largest prime factor \(m^r<p\le2m^r\), assigning weight \(p\) once to each such integer. Two primes above \(m^r\) have product greater than the horizon, and \(u/p<m\). Thus the square/cube and sixth/seventh-power integer products have exactly the same growth exponents for their normalized deficits as the corresponding sparse prime sums. The required independent subpower bound on either sequence remains open. [Exact gcd product and rounding](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheGcdProductOnOneMangoldtOctave.lean#L90)

Lean verified the square/cube equivalence with RH, the sixth/seventh-power equivalence with the absolute conductor-prefix bound at every endpoint, and the signed bound of \(14(1+\log K)\) for replacing the sampled negative errors by integer gcd deficits. For either sign, Lean also verified that cofinal subpower growth at exponent \(r\) is equivalent to \(\Theta\le1-1/r\). The full logarithmic growth formula above remains on paper. [Square/cube equivalence](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/SquareAndSixthPowerSamplesOfTheReciprocalPrimeOctave.lean#L523) · [Sixth/seventh equivalence](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/SquareAndSixthPowerSamplesOfTheReciprocalPrimeOctave.lean#L534)

Transposing the conductors gives a signed main term for floor rounding at both sparse horizons. On paper its total is \(\frac12\log K+c_r+o(1)\), also for ordinary primes alone. [Floor term with both moving endpoints](acs-pvc-the-signed-floor-term-on-power-sampled-prime-octaves.md)
