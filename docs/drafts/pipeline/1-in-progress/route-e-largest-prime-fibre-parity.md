# Route E largest-prime cofactor fibre retains primitive parity

- **ID:** E-LPF
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); Lean pending
- **Source:** `rh-current-frontier-map.md`, Route E primitive/noninteger-ratio obstacle
- **Statement:** Completing every denominator cofactor below a far prime does not cancel a fixed numerator Möbius cube: its literal primitive Gamma--Hankel fibre has the parity-predicted sign with an explicit $q^{-2}$ margin.

## Goal and scope

This tests the proposed Route E payment by denominator cofactors, including all cofactor grades rather than a fixed-depth subset. It is a negative result for that mechanism, not an RH estimate: cancellation across distinct largest-prime fibres or numerator supports growing with the fibre remains open. The denominator family lies below the physical cutoff (q^2), and each nonzero denominator has unique largest prime (q).

## Exact theorem

Let $P$ be a finite set of primes, $a_S=\prod_{p\in S}p$, $B_P=\prod_{p\in P}(1+p^2)$, and

\[
K(a,b)=\frac{a}{(a+b)(2a+b)},\qquad
T_P(q)=\sum_{S\subseteq P}\sum_{1\le d<q\atop (a_S,d)=1}
\mu(a_S)\mu(qd)K(a_S,qd).
\]

For every prime $q>32B_P$,

\[
(-1)^{|P|+1}q^2T_P(q)>\frac14.
\]

Every nonzero term is a literal coprime primitive pair in the cone $2a_S<qd$, with $qd<q^2$ and largest prime $q$. The theorem supplies no bound on the complete Route E covariance.

## Dependency-closed paper proof

Put $R_q=\{r<q:r\text{ prime}\}$, $U_q=\prod_{r\in R_q}(1-r^{-2})$, and first sum over all squarefree cofactors $d$ supported on $R_q$, without the restriction $d<q$. For every $a,d\ge1$,

\[
0\le \frac{a}{d^2}-q^2K(a,qd)
  \le \frac{3a^2}{qd^3}.
\]

Indeed, with $x=a/(qd)\ge0$, the middle difference is $a d^{-2}(1-[(1+x)(1+2x)]^{-1})$, and the parenthesis is at most $3x$. Since $\mu$ is ±1 or zero, the total approximation error is at most

\[
\frac3q\sum_{S\subseteq P}a_S^2
 \sum_{d\text{ squarefree},\,p\mid d\Rightarrow p<q}d^{-3}
 \le \frac{6B_P}{q}.
\]

Here $\sum_Sa_S^2=B_P$, while the cofactor sum is $\prod_{r\in R_q}(1+r^{-3})\le U_q^{-1}\le2$. The first inequality holds factorwise; the second follows because deleting factors in $(0,1)$ increases a product and

\[
U_q\ge\prod_{n=2}^{q-1}(1-n^{-2})
  =\frac{q}{2(q-1)}\ge\frac12.
\]

As $q>32B_P$, every $p\in P$ is below $q$. Möbius multiplicativity, coprimality and finite Boolean product expansion give the approximating main term exactly:

\[
M_P(q)
=-U_q\prod_{p\in P}
  \left(1-\frac{p}{1-p^{-2}}\right).
\]

Each parenthesized factor is negative with absolute value at least one, so $(-1)^{|P|+1}M_P(q)\ge1/2$.

Finally, omission of supported squarefree $d\ge q$ changes the normalized fibre by at most

\[
\sum_{S\subseteq P}a_S\sum_{d\ge q}d^{-2}
\le \frac{\prod_{p\in P}(1+p)}{q-1}
\le\frac{2B_P}{q}.
\]

The tail bound uses $d^{-2}\le[d(d-1)]^{-1}$ for $d\ge2$, whose series telescopes. Thus $|q^2T_P(q)-M_P(q)|\le8B_P/q<1/4$, proving the displayed strict margin.

## Research status

- Corpus audit: Route E already proves eventual parity for a fixed numerator Boolean cube against a **prime denominator only** (`RouteEPrimitiveAllGradeParityBarrier.lean`); it does not include all smaller-prime denominator cofactors. Search for Route E largest-prime/cofactor completion and exact kernel usages found no existing theorem of this form. This is a corpus novelty claim, not an external-priority claim.
- Positive survivor: exact main term $M_P(q)$, uniform Euler-factor margin, and quadratic-cutoff largest-prime disintegration. They identify the missing cancellation as a joint effect of changing numerator support or summing distinct $q$-fibres, not cofactor completion within one fixed-support fibre.
- Lean status: unformalized. Required ingredients are finite squarefree divisor reindexing, Möbius multiplicativity, finite Euler products, and elementary rational bounds. No new analytic limit theorem is required.
- Falsifier / next attack: seek a fixed $P$ and prime $q>32B_P$ violating the sign, or prove that summing these disjoint fibres cannot produce Route E's required covariance ceiling. The latter is open; this theorem alone is not an RH producer.
