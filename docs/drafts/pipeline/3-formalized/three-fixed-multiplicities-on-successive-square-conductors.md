# Three fixed multiplicities on square conductors

Put $D_n=e_1+2e_{n^2}-e_{(2n+1)^2}$ for every positive integer $n$. Its total variation is at most four and its positive pole degree is $1+2n-(2n+1)=0$. Let $F(n)=\Re S(2\log n)$ and $K(x)=\Re S(x)$. Then
\[
 Q(D_n)=6K(0)+4F(n)-2F(2n+1)-4K(2\log(2+1/n)).
\]
The last lag lies in $[2\log 2,2\log 3]$. A uniform lower bound on these degrees implies $F(n)\ge F(2n+1)/2-C$. After $k$ iterations the terminal conductor parameter is $2^k(n+1)-1$. Its contribution divided by $2^k$ vanishes because $F(t)=o(t)$. The absence of zeros on the line $\Re s=1$ already gives this endpoint limit. Thus $F$ is bounded below on the squares, which detects RH. More generally an allowance $n^{2s}$ yields a convergent geometric sum for every $0\le s<1/2$ and detects $w\le s$.

**Finite arithmetic criterion.** RH is equivalent to the existence of a single integer base $B>0$ for which $d_{\rm ord}(mD_n)\le B^{m^2}$ at arbitrarily large $m$ for every $n>0$. The same equivalence holds for all positive-pole-balanced signed divisors of total variation at most four. The variation bound makes the proper-power and regularized gamma costs uniform in $n$. Existence of $B$ remains open.

The reverse inequality for the doubling difference bounds the trace from above by the same iteration applied to \(-F\). The upper width law then implies RH. Consequently, if RH fails, these degrees are unbounded in both directions at arbitrarily late conductors. Under RH every divisor in the family has positive degree. Unconditionally, at arbitrarily large $n$ the full modulus fits strictly inside the original radius for all sufficiently large $m$, and the ordinary section count recovers the whole Weil degree.

Lean declarations include `zetaZeroWidth_le_iff_successorSquareTriple`, `riemannHypothesis_iff_successorSquare_power`, `riemannHypothesis_iff_poleBalanced_mass_four` and `frequently_successorSquare_sections`. [Doubling on square conductors](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/DoublingOnThreeFixedMultiplicities.lean)
