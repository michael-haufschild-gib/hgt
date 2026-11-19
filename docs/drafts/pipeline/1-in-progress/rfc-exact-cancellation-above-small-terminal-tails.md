# Exact cancellation above small terminal tails

- **Stage** 1-in-progress

For a squarefree integer, remove its factor of two if present, then strip each least prime at most the square of the integer part of the logarithm of one plus the current quotient. Call the final odd tail \(r\). A single constant \(K>0\) suffices for the following sharp statement. If \(K(1+\log^2(Y+1))\le\log X\), then the sum of \(\mu(n)\) over all \(n\le X\) with \(r\le Y\) is exactly zero.

An odd member is its own tail or has the form \(pcr\) with \(c\mid P(p-1)\) and \(\sqrt p\le\log(pr+1)\). Since \(\log p\le\sqrt p/2\) for large \(p\), this gives \(p\ll1+\log^2(r+1)\). The bound \(P(p-1)\le 4^p\) now gives \(\log(2pcr)\le K(1+\log^2(r+1))\). Every odd member and its even double therefore lie below the actual cutoff. They have equal terminal tails and opposite signs. Taking \(Y\) of order \(\exp(c\sqrt{\log X})\) for sufficiently small \(c>0\) removes this entire growing family with no error. The positive integer 1 and its double are included in the sign identity.
