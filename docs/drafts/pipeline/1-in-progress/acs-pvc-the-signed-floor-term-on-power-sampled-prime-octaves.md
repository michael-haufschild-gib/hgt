# The signed floor term on power-sampled prime octaves

Set \(M=m^r\), \(X=m^{r+1}\) for a fixed integer \(r\ge2\). In the integer gcd product the normalized cost of the sharp upper endpoint is
\[
 R_r(m)=\sum_{M<d\le2M}\frac{\Lambda(d)}d-\frac{\log Q_M(X)}X
       =\frac1X\sum_{M<d\le2M}\Lambda(d)\{X/d\}.
\]
On paper there is a constant \(c_r\) such that
\[
 \sum_{m\le K}R_r(m)=\tfrac12\log K+c_r+
 O_r(K^{-\min(1/3,r/9)}).
\]
The same logarithmic coefficient holds for ordinary primes alone. In particular the floor contributes \((\log 2)/2+o(1)\) per complete octave of the sampling index, including at the square/cube and sixth/seventh-power horizons. The remaining sparse prime deficits in §2.18 concern the reciprocal prime mass itself. [Integer product identity](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheGcdProductOnOneMangoldtOctave.lean#L90) · [Sparse criteria](acs-pvc-sparse-square-and-sixth-power-prime-octaves.md)

**Average the conductors first.** On any partial octave \(D<m\le K\le2D\), transpose the two finite sums. At fixed \(d\asymp_r D^r\) the admissible conductors form one interval, with \(m^r<d\le2m^r\) unchanged. For every integer \(j\ge1\), the phase \(j x^{r+1}/d\) has second derivative between positive constants times \(j/D\) there. The second derivative bound gives, uniformly on every subinterval,
\[
 \left|\sum_m e^{2\pi i j m^{r+1}/d}\right|
 \ll_r \sqrt{Dj}+\sqrt{D/j}.
\]
Erdős–Turán with \(H=\lfloor D^{1/3}\rfloor\) bounds the unnormalized discrepancy by \(O_r(D/H+\sqrt{DH})=O_r(D^{2/3})\). Integrating interval indicators on \([0,1]\) gives the same bound for \(\sum_m(\{m^{r+1}/d\}-1/2)\), including exact divisibilities. Abel summation against \(m^{-r-1}\) and \(\sum_{d\ll_r D^r}\Lambda(d)\ll_r D^r\) now give an error \(O_r(D^{-1/3})\) for the whole fragment. This centered error is uniform over all signed divisor weights \(|a_d|\le\Lambda(d)\) chosen independently of \(m\). The proof takes absolute values only after summing every eligible conductor at the same \(d\).

Lean verified the centered error on every partial octave, uniformly for all these signed divisor weights, with the summable bound \(O_r(D^{-1/4})\). The formal proof uses the second derivative estimate followed by the existing square-root harmonic bound for the sawtooth. The exponent \(-1/3\) above is on paper. [Uniform signed floor estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheCenteredFloorOnPowerSampledPrimeOctaves.lean#L279)

The remaining half-density on this fragment is \(\tfrac12\sum_m[\psi(2m^r)-\psi(m^r)]/m^{r+1}\). The project's \(O(x^{8/9})\) prime error and square-root proper-power bound give \(\tfrac12\sum_m 1/m+O_r(D^{-r/9})\). The geometric tail over all subsequent octaves converges with the stated power. Removing proper powers from the floor term costs \(O_r(D^{-r/2})\) per octave. [Prime error used in the density](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMassAtAQuadraticProductDivider.lean)

**Pointwise and cumulative laws at the eighth/ninth-power horizon.** Here every sufficiently late product has a deficit. In fact for \(r=8\) and every \(0<\delta<1/3000\),
\[
 \log 2-\frac{\log Q_{m^8}(m^9)}{m^9}
 =\frac1{2m}+O_\delta(m^{-1-\delta}).
\]
The same holds for the ordinary-prime product. Sum the cofactors first. For \(1\le j\le m\) put \(Y_j=\min(2M,mM/j)\). Exact factorization gives \(\log Q_M(mM)=\sum_{j=1}^m(\psi(Y_j)-\psi(M))\), including \(Y_m=M\). Replacing \(\psi(x)\) by \(x\) costs \(O_b(M^{b-1})\) after normalization for every \(b>\Theta\). With \(k=\lfloor m/2\rfloor\), the continuous contribution is exactly \(H_m-H_k+(2k-m)/m=H_{2k}-H_k\). Thus adjacent horizons \(2k,2k+1\) have identical continuous density. The harmonic expansion \(H_n=\log n+\gamma+1/(2n)+O(n^{-2})\) gives \(\log 2-1/(2m)+O(m^{-2})\) for **both** parities. The strict project strip permits \(b=1-(1+\delta)/8>20999/24000\). Removing proper powers costs \(O(m^{-4})\). Lean verifies the pointwise half-step with error \(O_\delta(m^{-1-\delta})\) for both the gcd product and the ordinary-prime price. [Ordinary-prime half-step](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheGcdDeficitAtTheEighthPowerEndpoints.lean#L334) Lean also proves that the sum of positive gcd-product deficits through \(K\) is \(\tfrac12\log K+c+O_\delta(K^{-\delta})\), with one constant \(c\) for every \(0<\delta<1/3000\). [Cumulative remainder](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheGcdDeficitAtTheEighthPowerEndpoints.lean#L240) The corresponding sixth-power arithmetic bound remains open. [Strict zero-free half-plane](../../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L147)
