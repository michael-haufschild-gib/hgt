# Cancellation between a prime-square cofactor and its proper multiples

Fix a prime \(\ell>4\) and put \(d=\ell^2\). In the actual capped reading \(R_n=T_n(n\lfloor\sqrt n\rfloor,n)\), write \(F_1(n)\) for the contribution of \(v=d\), and \(F_{>1}(n)\) for that of \(v=dt,\ t>1\). At \(n=\ell m\), the following bounds hold uniformly for \(m\ge1\), with \(L_m=1+\log(2m)\):
\[
 \ell F_1(\ell m)=-D_m+O_\ell(L_m^6),\qquad
 \ell F_{>1}(\ell m)= D_m+O_\ell(L_m^6).
\]
Thus the whole square-divisible family at these conductors costs \(O_\ell(N^3 L_N^6)\) through every terminal \(N\) after multiplication by \(n^2\). Its two parts may individually carry the full prime error.

For the singleton, square dilation of the complete fibre gives the first formula before clipping. Its lower products \(p d\le U_n=n\lfloor\sqrt n\rfloor\) occur on \([pd,\lceil pd/2\rceil^2)\). Give every other cofactor an empty interval in `spline_three_quarter_product_bound`. This charges \(O(1+\log U_n)\) for clipping. The cap retains \(d\) for \(n\ge d\).

For the proper multiples put \(U'=\lfloor U_n/d\rfloor\), \(M'=\lfloor n/d\rfloor\). The horizon at \(n\) is \(O(n^2)\), so the moving lower product endpoint is \(O(n)\) throughout it. For fixed \(\ell\) and all large \(m\), \(U_n\) dominates that endpoint. After square dilation, \(U'\asymp_\ell m^{3/2}\) likewise dominates the moving lower endpoint at conductor \(m\). The horizons may then be extended through zeros of the spline on both sides.

For every surviving pair \(pdt>U_n\), \(dt\le n\) gives \(p>\lfloor\sqrt n\rfloor\ge\ell\). Thus \((p,dt)=1\) is exactly \((p,t)=1\). All quotient floors divide exactly on replacing \(k\) by \(\lfloor k/d\rfloor\); the product cutoff is \(pt>U'\) and the cofactor cap is \(t\le M'\). Twice applying the prime-multiple identity gives \(g_1(dt)=g_1(t)-\mathbf1_{t=1}\). For \(t>1\) the weight is unchanged, and \(g_1(1)=0\) permits adjoining \(t=1\) to the reduced sum. Conversely a pair satisfying the reduced cutoffs has \(pdt>U_n\), so the same argument excludes \(p=\ell\). Telescoping the spline over consecutive blocks of \(d\) horizons now gives the exact identity \(\ell F_{>1}(\ell m)=T_m(U',M')\) for all large \(m\).

Here \((U')^2\le m^3\), since \(U_n^2\le n^3\) and \(n^3/d^2=m^3/\ell\). Also \(m/(M'+1)<\ell\). The joint cutoff theorem bounds \(|T_m(U',M')-D_m|\) by \(O_\ell(L_m^6)\). Absorb the finitely many smaller \(m\) in the constants and sum absolute errors. The complementary class \(d\nmid v\) and the other conductors still require signed control.

**Lean status.** The joint cutoff theorem is kernel-checked. Lean verification is pending for the singleton clipping, divided-slice identity and combined prefix. [Singleton clipping](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheClippedSquareComplement.lean) · [Opposite signals and weighted prefix](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/OppositePrimeSignalsOnSquareMultiples.lean)
