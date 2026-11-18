# Opposite signs of the long prime contacts

Let $U=e_1$, $V_n=2e_{n^2}-e_{(2n+1)^2}$ and $D_n^\pm=U\pm V_n$. For $n\ge2$ their resolutions are equal. On a shared mesh the two contact rows satisfy
\[
 X_q(D_n^+)+X_q(D_n^-)=2X_q(U)+2X_q(V_n).
\]
All ratios of conductors internal to $U$ or $V_n$ are bounded by nine. Outside a fixed set of primes the right side vanishes exactly. At each such prime the sum of the two valuations is zero if its contact is integral and $-1$ otherwise. On the fixed set of remaining primes the total valuations cost $O(m^2)$.

**Arithmetic comparison to formalize.** One integer $B>0$ bounds $d_{\rm ord}(mD_n^+)d_{\rm ord}(mD_n^-)$ by $B^{m^2}$ at every conductor and every multiplicity. This would leave one orientation to control. The two divisors have positive pole degrees zero and two, respectively. Only the first is the fixed-multiplicity pole-balanced RH test. [Polarization of contact ideals](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/PolarizationOfContactIdeals.lean)

**Two balanced orientations.** Put $P=e_1+e_{n^2}-e_{(n+1)^2}$ and $R=e_{n^2}+e_{(n+1)^2}-e_{(2n+1)^2}$. Then $P+R=D_n^+$ and $P-R=e_1-2e_{(n+1)^2}+e_{(2n+1)^2}$. Both have zero positive pole and mass four. The parallelogram identity gives $Q(P+R)+Q(P-R)=2Q(P)+2Q(R)$. The unit-triple bound would control this sum absolutely. The finite-place comparison then pays both ordinary prime generators together on every conductor. A bound on either chosen orientation alone would force RH, since the degrees of $D_n^+$ are unbounded in both directions if RH fails.

At finite mesh, $R$ has only bounded conductor ratios. In $P$ the two distant atoms differ in log position by $2\log(1+1/n)$. Their Lipschitz difference costs $O(1/n)$ before the prime weight. All long rows have $q\asymp n^2$ and their total weight is $O(n)$ by Chebyshev. This gives a direct path to the upper product comparison even at small multiplicities.
