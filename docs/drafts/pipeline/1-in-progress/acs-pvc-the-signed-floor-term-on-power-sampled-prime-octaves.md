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
Erdős–Turán with \(H=\lfloor D^{1/3}\rfloor\) bounds the unnormalized discrepancy by \(O_r(D/H+\sqrt{DH})=O_r(D^{2/3})\). Integrating interval indicators on \([0,1]\) gives the same bound for \(\sum_m(\{m^{r+1}/d\}-1/2)\), including exact divisibilities. Abel summation against \(m^{-r-1}\) and \(\sum_{d\ll_r D^r}\Lambda(d)\ll_r D^r\) now give an error \(O_r(D^{-1/3})\) for the whole fragment. Each prime or prime power keeps its two moving endpoints.

The remaining half-density on this fragment is \(\tfrac12\sum_m[\psi(2m^r)-\psi(m^r)]/m^{r+1}\). The project's \(O(x^{8/9})\) prime error and square-root proper-power bound give \(\tfrac12\sum_m 1/m+O_r(D^{-r/9})\). The geometric tail over all subsequent octaves converges with the stated power. Removing proper powers from the floor term costs \(O_r(D^{-r/2})\) per octave. [Prime error used in the density](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMassAtAQuadraticProductDivider.lean)

**A verified strip gives an arithmetic control case.** The project's bound \(\Theta\le20999/24000<7/8\) gives \(\sum_m|e_{2m^8}|<\infty\) by partial summation at any strictly intermediate exponent. Thus the unweighted sum through \(K\) of the actual eighth/ninth-power gcd deficits is \(\frac12\log K+c+o(1)\) on paper. Indeed \(|(R-e)^+-R|\le|e|\) for \(R\ge0\). The sixth-power arithmetic bound remains open. [Strict zero-free half-plane](../../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L147)
