# Joint value and entropy at finite horizon

For a balanced factorial product at horizon $L$, let $q=\prod(j!)^{c_j}$ and $E=\prod j^{j c_j}$. Every positive rational has an exact zero-entropy presentation at sufficiently large horizon. [Proof](../3-formalized/zero-entropy-factorial-presentations.md)

**Finite-horizon classification.** At $L\ge10$, both $q$ and $E$ are positive rationals with prime factors at most $L$. Necessarily $p\mid v_p(E)$ for every prime $p$, since $p\mid j$ in every contribution to $v_p(E)$. If $L$ is prime, $v_L(E)=L v_L(q)$ since only $L!$ reaches $L$. They suffice. for each prime $p$ first give $p!$ exponent $v_p(E)/p$, balance at $1!$, and correct the remaining value by zero-entropy presentations of the smaller primes. At a composite horizon every prime at most $L$ is strictly smaller than $L$. At a prime horizon the prescribed top valuation cancels before correction.

The joint logarithmic image is formalized by `factorialJointImage_eq_prime_readings`. The coordinate form and attainment criterion are being formalized. [Prime generators of the joint image](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePrimeLatticeOfFactorialEntropy.lean)

The simultaneous absolute value of entropy and Stirling remainder has infimum $|\log q|/2$ at horizons at least six. At composite horizons $L\ge10$ the infimum is attained exactly when $2p\mid v_p(q)$ for every prime $p$. At prime horizons $L\ge11$ attainment also requires $v_L(q)=0$. This separates exact cancellation from arbitrarily good real approximation. It leaves the quantitative cost of the factorial exponents open.

**Why ten is the first full horizon.** At horizon nine with entropy zero, the prime coordinates of the entropy force
\[
c_7=c_5=0,\qquad c_3=-2c_6-6c_9,\qquad c_2=-4c_4-3c_6-12c_8.
\]
Writing \(v_p=v_p(q)\), factorial valuations give
\[
v_2=-c_4-c_6-5c_8+c_9,\quad v_3=c_4+2c_8-2c_9,\quad
v_5=c_6+c_8+c_9,\quad v_7=c_8+c_9 .
\]
Thus \(v_2+v_3+v_5=-2c_8\). Conversely, given any valuations supported on \(2,3,5,7\) satisfying that parity, take \(c_8=-(v_2+v_3+v_5)/2\), \(c_9=v_7-c_8\), \(c_6=v_5-v_7\), \(c_4=v_3+2v_7-4c_8\), and balance at \(1!\). The zero-entropy image at nine has index two. In particular even the price 2 first appears at ten. Below nine the same equations give the exact earlier images. At eight one needs \(v_2+v_3+v_5+2v_7=0\). At six and seven one needs \(v_7=0\) and \(v_2+v_3+v_5=0\). At four and five only multiples of \((-1,1,0,0)\) occur. Below four only the price one occurs.
