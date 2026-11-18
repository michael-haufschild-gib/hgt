# Zero-entropy factorial presentations

Can the exact section generator be recovered from a balanced factorial product whose Stirling entropy vanishes identically? For integer exponents $c_j$, let $q=\prod(j!)^{c_j}$, $E=\prod j^{j c_j}$ and impose $\sum j c_j=0$.

For $a,b>0$ the quotient
$$Q(a,b)=(ab)!/((a!)^b(b!)^a)$$
has entropy zero in logarithmic units, after adding $ab$ copies of $1!$. Write $Q_4=Q(2,2)$, $Q_6=Q(2,3)$, $Q_9=Q(3,3)$ and $Q_{10}=Q(2,5)$. Cancellation of factorials gives
$$2=Q_9Q_4^4/(Q_{10}Q_6).$$
Now assume all positive integers below $n$ admit such presentations. For $n=2k\ge4$ multiply presentations of $2$ and $k$. For $n=2k-1\ge3$, expand
$$Q(2,k)=\frac{2k\,n\,(n-1)!}{(2!)^k(k!)^2}.$$
Every factor other than $n$ is a product of integers below $n$. This supplies $n$ at horizon at most $\max(10,n+1)$. Division supplies every positive rational. In particular every rational section generator admits a balanced, exactly zero-entropy presentation.

**Proposed finite-horizon classification.** At $L\ge10$, both $q$ and $E$ are positive rationals with prime factors at most $L$. Necessarily $p\mid v_p(E)$ for every prime $p$, since $p\mid j$ in every contribution to $v_p(E)$. If $L$ is prime, $v_L(E)=L v_L(q)$ since only $L!$ reaches $L$. These conditions should suffice: for each prime $p$ first give $p!$ exponent $v_p(E)/p$, balance at $1!$, and correct the remaining value by zero-entropy presentations of the smaller primes. At a composite horizon every prime at most $L$ is strictly smaller than $L$. At a prime horizon the prescribed top valuation cancels before correction.

The simultaneous absolute value of entropy and Stirling remainder has infimum $|\log q|/2$ at horizons at least six. At composite horizons $L\ge10$ the infimum is attained exactly when $2p\mid v_p(q)$ for every prime $p$. At prime horizons $L\ge11$ attainment also requires $v_L(q)=0$. This separates exact cancellation from arbitrarily good real approximation. It leaves the quantitative cost of the factorial exponents open.
