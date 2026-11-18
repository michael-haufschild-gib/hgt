# Prime mass escaping along dyadic square conductors

Let $e_n(p)=v_p(q_n)$ for the ordinary generator of $nD_n$. Put $F(v)=H(\log v)/\sqrt v$, $F_n(p)=F(p/n^2)$ and $M=\int_0^\infty F(v)\,dv>0$. The absolute valuation estimate gives
$$
e_n=4nF_n-nF_{2n}+r_n,\qquad
\sum_p |r_n(p)|\log p\le Cn^2.
$$
For $G_{n,k}=\prod_{0\le j<k}q_{2^jn}^{8^{k-1-j}}$, division of its valuations by $8^{k-1}$ gives
$$
4nF_n-4n\,4^{-k}F_{2^kn}+\sum_{j<k}8^{-j}r_{2^jn}.
$$
The last term has absolute logarithmic mass at most $2Cn^2$, uniformly in depth. For $k\log4>16$ the two profiles have disjoint prime supports. Taking positive and negative parts, the log numerator and denominator of the same reduced rational separately recover the two endpoint masses to this uniform precision.

For each fixed $n>0$ the prime coordinates $l_n(p)=\sum_{j\ge0}8^{-j}e_{2^jn}(p)$ exist and $\sum_p|l_n(p)|\log p<\infty$. The discrepancies $r_{2^jn}$ are absolutely summable in the two indices with these weights. At a fixed prime the moving endpoint eventually vanishes. In the sum over primes the ordinary prime number theorem gives $4^{-k}\sum_p F_{2^kn}(p)\log p\to n^2 M$. Thus the difference between the two orders of summation is explicit:
$$
\sum_p l_n(p)\log p-\sum_{j\ge0}8^{-j}\log q_{2^jn}=4n^3M .
$$
In particular the normalized dyadic log product differs from $4n[\sum_p F_n(p)\log p-n^2M]$ by at most $2Cn^2$. Bounding the centered positive prime mass at square-root scale remains open. [Absolute prime exponent estimate](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePrimeExponentsOnTheSquareDiagonal.lean) · [Ordinary prime test and positive mass](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheLogarithmicMomentOfTheSquarePrimeProfile.lean)

The weight $1/8$ is the transition between absolute convergence and divergence in prime order. For $0\le r<1/8$ the full absolute double series converges by the cubic height bound. Write $B_n=4nF_n$. If $1/8<r<2^{-2-2w}$, the series of signed conductor logs converges absolutely by the width bound. At each prime its coordinate sum equals
$$B_n+(r-1/8)\sum_{j\ge1}r^{j-1}B_{2^j n}+\sum_{j\ge0}r^j r_{2^j n}.$$
The last sum has finite absolute logarithmic mass since $4r<1$. The middle sum is nonnegative, and its logarithmic mass diverges since the endpoint masses grow as $4Mn^3 8^j$. Summing the prime coordinates in increasing prime order therefore tends to $+\infty$ throughout this interval.
