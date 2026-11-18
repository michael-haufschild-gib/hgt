# Multiplicity needed to resolve ordinary prime contacts

The numerator bound for the square-root multiplicity range is formalized. [Square-root range](../3-formalized/prime-contact-products-at-small-multiplicity.md)

**A denominator window.** For large \(n\), consider \(e^8(2n+1)^2/3<q<e^8(2n+1)^2/2\). Since \(q>e^8 n^2\), every same-sign atom product vanishes. At mesh resolution \(r>0\), the lower sample \(j=12r\) has spline argument \(\log4-5\), and the paired upper sample has argument between \(3+\log(4/3)\) and \(3+\log2\). Both are strictly inside the spline support. Thus the signed row should be strictly negative for every \(m>0\). The prime number theorem in this interval gives a prospective lower bound of \(n^2/12\) for the log denominator at every positive multiplicity. Combined with the numerator bound, this predicts \(\log d_{\rm ord}(mD_n)\le -n^2/24\) uniformly for \(0<m\le c\sqrt n\) and large \(n\). [Denominator window](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ANegativePrimeWindowAtEveryMultiplicity.lean)

[One multiplicity per square conductor](../3-formalized/one-multiplicity-per-square-conductor.md) gives the uniform sampling and floor estimates.
