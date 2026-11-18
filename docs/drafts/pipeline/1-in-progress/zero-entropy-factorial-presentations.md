# Joint value and entropy at finite horizon

For a balanced factorial product at horizon $L$, let $q=\prod(j!)^{c_j}$ and $E=\prod j^{j c_j}$. Every positive rational has an exact zero-entropy presentation at sufficiently large horizon. [Proof](../3-formalized/zero-entropy-factorial-presentations.md)

**Proposed finite-horizon classification.** At $L\ge10$, both $q$ and $E$ are positive rationals with prime factors at most $L$. Necessarily $p\mid v_p(E)$ for every prime $p$, since $p\mid j$ in every contribution to $v_p(E)$. If $L$ is prime, $v_L(E)=L v_L(q)$ since only $L!$ reaches $L$. These conditions should suffice: for each prime $p$ first give $p!$ exponent $v_p(E)/p$, balance at $1!$, and correct the remaining value by zero-entropy presentations of the smaller primes. At a composite horizon every prime at most $L$ is strictly smaller than $L$. At a prime horizon the prescribed top valuation cancels before correction.

The simultaneous absolute value of entropy and Stirling remainder has infimum $|\log q|/2$ at horizons at least six. At composite horizons $L\ge10$ the infimum is attained exactly when $2p\mid v_p(q)$ for every prime $p$. At prime horizons $L\ge11$ attainment also requires $v_L(q)=0$. This separates exact cancellation from arbitrarily good real approximation. It leaves the quantitative cost of the factorial exponents open.
