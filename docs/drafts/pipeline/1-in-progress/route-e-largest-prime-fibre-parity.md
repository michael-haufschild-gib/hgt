# Route E largest-prime cofactor fibre retains primitive parity

- **ID:** E-LPF
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean-closed squarefree source expansion)
- **Source:** `rh-current-frontier-map.md`, Route E primitive/noninteger-ratio obstacle
- **Statement:** Completing every denominator cofactor below a far prime does not cancel a fixed numerator Möbius cube: its literal primitive Gamma--Hankel fibre has the parity-predicted sign with an explicit $q^{-2}$ margin.

## Goal and scope

This tests payment by **all** smaller-prime denominator cofactors, not a fixed-depth subset. The denominator family lies below the physical cutoff $q^2$ and each nonzero denominator has largest prime $q$. The old quadratic-mass threshold gives an absolutely summable selected family, but that threshold discarded the Euler main term's growing parity margin. Retaining the margin yields a *non-summable harmonic-scale selected family*. This is a source-side cancellation debt, not an RH estimate: other numerator channels may pay it.

## Exact theorem

Let $P$ be a finite set of primes below $q$, $a_S=\prod_{p\in S}p$, $B_P=\prod_{p\in P}(1+p^2)$, and $C_P=\prod_{p\in P}(p-1+p^{-2})\ge1$. Define

\[
K(a,b)=\frac{a}{(a+b)(2a+b)},\qquad
T_P(q)=\sum_{S\subseteq P}\sum_{1\le d<q\atop (a_S,d)=1}
\mu(a_S)\mu(qd)K(a_S,qd).
\]

For every prime $q$ satisfying $qC_P>32B_P$,

\[
(-1)^{|P|+1}q^2T_P(q)>\frac{C_P}{4}\ge\frac14.
\]

The sufficient scale is roughly $q\gg\prod_{p\in P}p$, rather than $q\gg\prod_{p\in P}p^2$: factorwise $p+1\le(1+p^2)/(p-1+p^{-2})\le p+2$, so $q>32\prod_{p\in P}(p+2)$ suffices. It also forces $q>2a_S$. Every nonzero term is therefore a literal coprime primitive pair in $2a_S<qd$, with $qd<q^2$ and largest prime $q$. The theorem supplies no bound on the complete covariance.

**Harmonic moving-prime corollary.** For every sufficiently large prime $q$, Bertrand's theorem chooses a prime $p(q)$ with $256p(q)\le q\le1024p(q)$. Complete *every* denominator cofactor supported on primes below $q$ in the singleton numerator cube. Then

\[
T_{\{p(q)\}}(q)>\frac{1}{8192q},\qquad
\sum_{q\text{ prime}}T_{\{p(q)\}}(q)=+\infty.
\]

Lean proves the stronger non-summability statement for this nonnegative selected family. This does **not** imply divergence of the full covariance, since other numerator channels may have opposite sign.

**Disjoint prime-numerator survivor.** The singleton cube is exactly the empty-numerator fibre plus the coefficient-one prime-numerator fibre

\[
H_{p,q}=\sum_{1\le d<q\atop(d,p)=1}
  \mu(p)\mu(qd)K(p,qd).
\]

The empty-numerator fibre is strictly negative for these $q$ by the same parity theorem with $P=\varnothing$. Therefore $H_{p(q),q}>T_{\{p(q)\}}(q)>1/(8192q)$, and $\sum_{q\text{ prime}}H_{p(q),q}=+\infty$. Unlike the cube sums, these chosen source pairs are disjoint: each has one fixed prime numerator and denominator with unique largest prime $q$. Thus cube overlap is not the reason this harmonic positive debt survives. The remaining payment must come from *other* numerator integers/channels of the complete signed source.

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

Since every $p\in P$ is below $q$, Möbius multiplicativity, coprimality and finite Boolean product expansion give the approximating main term exactly:

\[
M_P(q)
=-U_q\prod_{p\in P}
  \left(1-\frac{p}{1-p^{-2}}\right).
\]

Equivalently $M_P(q)=(-1)^{|P|+1}C_P\prod_{r<q,\ r\notin P}(1-r^{-2})$. The last product is at least $1/2$, so $(-1)^{|P|+1}M_P(q)\ge C_P/2$. Replacing $C_P$ by its minimum $1$ is exactly the information loss that created the old quadratic-mass boundary.

Finally, omission of supported squarefree $d\ge q$ changes the normalized fibre by at most

\[
\sum_{S\subseteq P}a_S\sum_{d\ge q}d^{-2}
\le \frac{\prod_{p\in P}(1+p)}{q-1}
\le\frac{2B_P}{q}.
\]

The tail bound uses $d^{-2}\le[d(d-1)]^{-1}$ for $d\ge2$, whose series telescopes. Thus $|q^2T_P(q)-M_P(q)|\le8B_P/q<C_P/4$, proving the displayed strict margin. For the moving singleton, $B_{\{p\}}=1+p^2\le2p^2$ and $C_{\{p\}}=p-1+p^{-2}\ge p/2$. The band $q\ge256p$ implies $qC>32B$; $q\le1024p$ then gives $T>p/(8q^2)\ge1/(8192q)$. Euler's prime-reciprocal divergence closes the corollary.

## Route-level consequence: the sign-locked region is subcritical

There is a stronger conclusion than fixed-support summability. For **any** choice of finite prime sets $P(q)$ satisfying $q>32B_{P(q)}$, the whole selected fibre family is absolutely summable over $q$; no cross-fibre signed payment is required there. Indeed the kernel inequality above and the injective squarefree-product parameterization give

\[
 |T_{P(q)}(q)|\le {2\over q^2}\prod_{p\in P(q)}(1+p).
\]

For every prime $p\ge2$, $(1+p)^4\le(1+p^2)^3$ (expand, or use $p^3(p^3-4)+p(2p^3-3p-4)\ge0$). Multiplication yields $\prod_{p\in P}(1+p)\le B_P^{3/4}$. Consequently

\[
 |T_{P(q)}(q)| < {2\over 32^{3/4}q^{5/4}},
 \qquad \sum_{q\ \mathrm{prime}}|T_{P(q)}(q)|<\infty.
\]

The old $q^{-5/4}$ bound is valid **only under its stronger hypothesis** $q>32B_P$. It does not classify all sign-locked selected cubes. The refined signal-to-error ratio $qC_P/B_P$ reaches moving supports with $B_P\gtrsim q$ and, for one prime $p(q)\asymp q$, produces a harmonic-divergent **disjoint numerator-prime channel**. This reverses the old route-level extrapolation: completing denominator cofactors alone does **not** make every selected numerator channel summable. Remaining hard problem is to identify and bound the exact payment from other numerator integers in the complete physical covariance. Boolean cubes overlap, but the prime-numerator channel itself does not.

## Research status

- Corpus audit: Route E already proves eventual parity for a fixed numerator Boolean cube against a **prime denominator only** (`RouteEPrimitiveAllGradeParityBarrier.lean`); it does not include all smaller-prime denominator cofactors. Search for Route E largest-prime/cofactor completion and exact kernel usages found no existing theorem of this form. This is a corpus novelty claim, not an external-priority claim.
- Positive survivor: exact main term and *amplified* parity margin $C_P$, a linear-in-support sign range, and a harmonic-divergent **coefficient-one prime-numerator** channel after full denominator-cofactor completion. The old $q^{-5/4}$ majorant remains a sharp statement of its restricted far-prime regime, not a global selected-family law.
- Lean status: `RouteELargestPrimeFibreParity.lean` proves the full finite squarefree support expansion, kernel and cutoff errors, parity margin, moving-singleton lower bound, Bertrand prime choice, and non-summability. `routeELargestPrimeCofactorSet q` is exactly all primes below $q$. `routeELargestPrimeMobiusFibre_eq_cut` identifies every squarefree-support coefficient with literal $\mu(a_S)\mu(qd_D)$. `routeELargestPrimeSingleton_eq_empty_add_prime`, `routeELargestPrimePrimeNumerator_harmonic_lower`, and `not_summable_routeELargestPrimePrimeNumeratorSelected` close the disjoint prime-only survivor.
- Falsifier / next attack: find a large prime $q$ for which the exact prime-numerator cofactor fibre violates the harmonic lower bound. The unresolved RH producer is the *complete* covariance: identify the other numerator integers and cross-fibre signs that pay this disjoint divergent positive family. No RH producer is presently established.
