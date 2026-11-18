# Averaging the prime error at a complementary-factor boundary

**PVC · Formalized.** Write the factorial stencil at $R\ge1$ as $\sum_e c_e f(e)$, with mass $M_R$, support $1\le e\le2R$ and $\sum_e c_e/e=0$. For integers $a>0$ put
$$
B_R(a)=1-\sum_e c_e\lfloor a/e\rfloor-(1+\tfrac12\sum_e c_e).
$$
For every integer interval $A\le a<B$ and $X\ge0$, uniformly in the endpoints,
$$
\left|\sum_{a=A}^{B-1}B_R(a)\left(\psi\!\left(\left\lfloor X/(a+1)\right\rfloor\right)-\left\lfloor X/(a+1)\right\rfloor\right)\right|
\le 2M_R R\left\lfloor X/(A+1)\right\rfloor.
$$
For an average of $S$ cutoffs the cost is therefore $O(M_R R\sqrt X)$ whenever $(A+1)S\ge\sqrt X$. In particular $S=1+\lfloor\sqrt X/(A+1)\rfloor$ works at every horizon and initial cutoff.

**Proof.** The zero reciprocal moment gives $B_R(a)=\sum_e c_e r_e(a)$ with $r_e(a)=(a\bmod e)/e-(e-1)/(2e)$. Its [exact quadratic primitive](../../../../formal/GaloisForLFunctions/HTGeometry/CenteredModularAbel.lean) lies in $[-e/8,0]$. Every interval sum of $B_R$ consequently costs at most $M_R R/4$. More generally, pairing $B_R(a)$ with $\sum_{n\le X/(a+1)}u_n$ costs at most $(M_R R/4)\sum_{n\le U}|u_n|$. Each increment retains one interval of $a$. Expand the prime error as $\sum_{n\le X/(a+1)}(\Lambda(n)-1)$. The absolute coefficient mass is at most $\psi(U)+U\le8U$, where $U=\lfloor X/(A+1)\rfloor$. Multiplication gives the claim.

**Lean.** [`factorialBoundary_interval`, `factorialBoundary_quotient_prefix`, `factorialBoundary_smoothed_prime_error`](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/AveragingThePrimeErrorAtAComplementaryBoundary.lean).
