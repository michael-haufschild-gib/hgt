# Half-height residues of the first prime-divisor moment

The summatory function of \(\log\operatorname{rad}n\) is \(\sum_{p\le N}(\log p)\lfloor N/p\rfloor\). Its jump series on \(\Re s>1\) is \(Z(s)=\zeta(s)\sum_p(\log p)p^{-s}\).

Write \(M=-\zeta'/\zeta\), \(H(s)=\sum_{p,k\ge2}(\log p)p^{-ks}\), with the sum over primes \(p\) and integers \(k\ge2\). Splitting off the squares and cubes gives
\[
Z(s)=-\zeta'(s)+\zeta(s)\bigl(H(2s)+H(3s)-H_{\ge4}(s)-M(2s)-M(3s)\bigr).
\]
The three tails are holomorphic on \(\Re s>1/4\) by locally uniform absolute convergence. At every nonreal point there, writing \(m(w)\) for the analytic order of \(\zeta\) at \(w\), one obtains
\[
\lim_{s\to z}(s-z)Z(s)=\zeta(z)\left(\frac{m(2z)}2+\frac{m(3z)}3\right).
\]
A vanishing residue at half a right zero forces its half to be a zero. Reflecting and halving repeatedly would give zeros tending to \(2/3\). Thus RH is equivalent to holomorphy of \(Z\) at every nonreal point right of one quarter.

More generally, suppose the residues vanish at all nonreal points with \(b<\Re s<1/2\), where \(1/4\le b\le1/3\). Repeated halving excludes \(2b<\beta<2-4b\). If \(\beta>3b\), vanishing at \(\rho/3\) gives a zero whose reflection lies in that excluded band. Any remaining zero right of \(2b\) has \(2-4b\le\beta\le3b\). For \(b<2/7\) there is none.

[Lean declarations](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheFirstPrimeDivisorMomentAtHalfARightZero.lean)
