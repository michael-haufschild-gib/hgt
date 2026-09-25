# Route E largest-prime cofactor fibre retains primitive parity

- **ID:** E-LPF
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); Lean pending
- **Source:** `rh-current-frontier-map.md`, Route E primitive/noninteger-ratio obstacle
- **Statement:** Completing every denominator cofactor below a far prime does not cancel a fixed numerator Möbius cube: its literal primitive Gamma--Hankel fibre has the parity-predicted sign with an explicit $q^{-2}$ margin.

## Goal and scope

This tests the proposed Route E payment by denominator cofactors, including all cofactor grades rather than a fixed-depth subset. It is a negative result for that local mechanism, not an RH estimate. The denominator family lies below the physical cutoff ($q^2$), and each nonzero denominator has unique largest prime $q$. The sign-locked region is in fact absolutely summable across $q$ even when the numerator support moves subject to the theorem's threshold; it cannot itself be an RH-scale obstruction.

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

This falsifies the tempting extrapolation that persistent sign in **one selected cube per largest-prime fibre** creates a global debt. The theorem does not bound the number of distinct cubes needed to cover the full source, nor their overlaps. RH-scale mass can still arise from their collective multiplicity, from the **joint-scale sector** $B_P\gtrsim q$ where the far-fibre expansion ceases to be uniform, or from other primitive pairs. The $5/4$ majorant is not asserted sharp for that sector.

## Research status

- Corpus audit: Route E already proves eventual parity for a fixed numerator Boolean cube against a **prime denominator only** (`RouteEPrimitiveAllGradeParityBarrier.lean`); it does not include all smaller-prime denominator cofactors. Search for Route E largest-prime/cofactor completion and exact kernel usages found no existing theorem of this form. This is a corpus novelty claim, not an external-priority claim.
- Positive survivor: exact main term $M_P(q)$, uniform Euler-factor margin, quadratic-cutoff largest-prime disintegration, and the new moving-support $q^{-5/4}$ absolute majorant for one selected cube per fibre. The majorant identifies a **subcritical selected family**, not a bound on the union of all such cubes.
- Lean status: sign theorem and moving-support summability remain paper-only. Scratch Lean checks the rational kernel remainder, finite Euler-factor sign, unique squarefree-product parameterization, reciprocal-square tail/total estimates, and the full weighted kernel-error ceiling $6B_P/q$. The literal finite Möbius source and final bounds remain to be closed.
- Falsifier / next attack: seek a prime $q>32B_P$ violating either the sign or the $q^{-5/4}$ bound. More important: characterize the joint-scale regime $B_P\gtrsim q$ without assuming a far-fibre expansion; test whether a new source-faithful invariant controls its cross-fibre resonance. No RH producer is presently established.
