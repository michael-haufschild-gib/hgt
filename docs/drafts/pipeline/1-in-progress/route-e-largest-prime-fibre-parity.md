# Route E largest-prime cofactor fibre retains primitive parity

- **ID:** E-LPF
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean-closed squarefree source expansion)
- **Source:** `rh-current-frontier-map.md`, Route E primitive/noninteger-ratio obstacle
- **Statement:** Completing every denominator cofactor below a far prime does not cancel a fixed numerator Möbius cube: its literal primitive Gamma--Hankel fibre has the parity-predicted sign with an explicit $q^{-2}$ margin.

## Goal and scope

This tests payment by **all** smaller-prime denominator cofactors, not a fixed-depth subset. The denominator family lies below the physical cutoff $q^2$ and each nonzero denominator has largest prime $q$. The old quadratic-mass threshold gives an absolutely summable selected family, but that threshold discarded the Euler main term's growing parity margin. Retaining the margin yields a *non-summable harmonic-scale selected family*. This is a source-side cancellation debt, not an RH estimate: other numerator channels may pay it.

**Receiver alignment.** Every theorem on this card concerns the boundary exponent $r=1$. The RH-equivalent Gamma--Hankel criterion instead requests an $N$-uniform one-sided covariance ceiling at exponents $r>1$ arbitrarily close to 1; its ceiling may depend on $r$. Thus bilateral divergence at $r=1$ alone neither proves nor obstructs that criterion. Any proposed transfer principle must be reconstructed at fixed $r>1$ with the complete common-gcd/primitive-ratio source and then supply the required $N$-uniform bound. This quantifier gap is a no-go for promoting the present boundary law to an RH producer.

**Fixed-order falsifier for a single chosen numerator.** Write
$K_r(a,b)=(a+b)^{-r}-(2a+b)^{-r}$, so $K_1=K$ exactly. Lean proves that for $1<r\le2$, $0\le a\le q$ and arbitrary coefficients $|c_{q,d}|\le1$,
\[
\left|\sum_{1\le d<q}c_{q,d}K_r(a,qd)\right|
 \le 6a q^{-r-1}\le6q^{-r}.
\]
The proof uses $0\le K_r(a,b)\le3a b^{-r-1}$ and $\sum_{d\ge1}d^{-2}\le2$; it retains the literal physical cofactor cutoff. Hence *one selected prime numerator per denominator prime* is absolutely summable at every fixed receiver exponent $r>1$, even with the actual Möbius/coprimality coefficients. The $r=1$ harmonic divergence and first $2p$ payment cannot by themselves force a fixed-$r$ covariance obstruction or payment law.

This does **not** dispose of a dense proportional prime-numerator band. A candidate next test is to prove uniform sign for every $p$ in a proportional band $p\asymp q$ and aggregate over its $\asymp q/\log q$ primes. On dyadic $q\asymp X$ blocks, a per-pair floor $\asymp X^{-r}$ would yield $\asymp X^{2-r}/\log^2X$, divergent for $1<r<2$. This aggregate prediction is not yet a theorem on this card; its source sign, common-gcd coupling, and all-grade counterpayment must be checked before interpreting it as RH-relevant.

**Fixed-order two-sign proportional-band test.** The first part of that prediction is now proved in Lean for the *literal cofactor-completed fibres*, not for the whole covariance. Uniformly for every fixed $r\ge1$, there are constants $C_r,D_r>0$ such that whenever $p,q$ are primes, $p\ge3$, and $1/1024\le p/q\le1/256$,
\[
  H_r(p,q)\ge C_r q^{-r},\qquad H_r(2p,q)\le-D_r q^{-r}.
\]
The stronger theorem says $-\mu(a)H_r(a,q)>K_r(a,q)/48$ for *every* squarefree $a$ with $q\ge128a$. Scale covariance $K_r(a,q)=q^{-r}K_r(a/q,1)$ and a compact positive ratio floor supply both displayed constants. This is a quantitative all-grade source sign, with the complete denominator cofactor sum below $q$ and no artificial sign choice.

For $1<r<2$, the ordinary prime number theorem makes the positive and negative *selected* block masses separately unbounded: take $N<p\le2N$ and $512N<q\le1024N$. Each window contains $\gg N/\log N$ primes; each pair has magnitude $\gg N^{-r}$ with its stated sign. Each block therefore has positive or negative magnitude $\gg N^{2-r}/\log^2N\to\infty$. Lean now proves the uniform finite-block inequalities with one constant independent of $N$ for each sign; the last analytic passage from the existing prime-window PNT theorem to unbounded block mass remains a dependency-closed paper deduction, not yet a Lean theorem. It does not assert divergence of the *signed total*: different grades, near-cone pairs and common-gcd/Gamma terms can cancel. It does prove that the one-fibre fixed-$r$ summability no-go does not extend to a dense numerator band and that a separately absolutely convergent all-grade limit is the wrong target.

**Interpretation test, not an RH claim.** Source-pair entropy is two-dimensional while each homogeneous edge decays like $q^{-r}$; the threshold $r=2$ is the balance point. Every far-cone grade keeps its sign after denominator completion, yet adjacent grades have opposite unbounded selected masses for $1<r<2$. Thus denominator-tail domination cannot be the missing RH mechanism. Any real source theorem must retain the simultaneous signed grade sum *before* the physical cutoff limit and show how the near cone/common-gcd/Gamma completion pays the residual. This shifts the candidate object from individual fibres to a jointly renormalized signed current. Whether such a current has an independently provable orientation law remains open; naming it is not a solution.

**All-grade far-cone theorem.** The uniform sign part of that prediction is now Lean-closed, and is stronger than a prime-only assertion. For every squarefree integer $a>0$, prime $q\ge128a$, and every real $r\ge1$, define the literal cofactor-completed numerator fibre
\[
H_r(a,q)=\sum_{1\le d<q\atop(a,d)=1}\mu(a)\mu(qd)K_r(a,qd).
\]
Then $-\mu(a)H_r(a,q)>0$. Thus *every* squarefree numerator grade retains its own alternating parity after all denominator cofactors below the physical $q$ cutoff; denominator completion cannot reverse even one far-cone fibre. The proof is universal: for any coefficients $|c_d|\le1$ with $c_1=1$, the $d=1$ term dominates all $d\ge2$. At $r=1$, $K_1(a,q)>\frac{11}{12}a/q^2$ when $q\ge128a$, while $\sum_{d\ge2}K_1(a,qd)\le\frac{11}{12}a/q^2$. For $r\ge1$, convexity of $x^r$ makes the secant slope on the later reciprocal interval no larger than on the first, preserving the strict dominance. The Möbius specialization uses only $\mu(a)^2=1$, $\mu(q)=-1$, and $|\mu|\le1$. This locates the unresolved payment in **other numerator grades or the near-ratio/common-gcd region**, not in a far-cone denominator cofactor tail. It is not a bound on the complete covariance.

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

**First literal payment channel.** For the same selected $p=p(q)\ge3$, let $J_{2p,q}$ be the cofactor-completed literal source with composite numerator $2p$ and its arithmetic Möbius coefficient. The exact Boolean-source identity is

\[
T_{\{2,p\}}(q)-T_{\{2\}}(q)=H_{p,q}+J_{2p,q}.
\]

The parity-margin theorem makes $T_{\{2,p\}}(q)<0<T_{\{2\}}(q)$ whenever $q\ge256p$. Consequently $J_{2p,q}<-H_{p,q}<-1/(8192q)$ in the moving band. Thus a *disjoint composite-numerator channel* actually overpays the disjoint prime-numerator harmonic debt. This is not full-covariance cancellation: higher numerator grades and the physical common-gcd/limit remain. It does falsify the conjecture that denominator-cofactor completion leaves a prime-only obstruction with no source-level payment.

After deleting only the finite initial segment $q<4096$, the selected $2p(q)$ channel is non-summable on its own: its terms are negative and bounded above by $-1/(8192q)$, while the prime reciprocal series diverges. Lean proves this non-summability. Hence the selected completed fibres have *both* a divergent positive prime channel and a divergent negative composite channel. Separate finite-variation completion of these channels cannot be the all-grade solution; the signed transfer must be retained before the cofinal limit. This bilateral divergence is a fibre-level statement, not yet a formal theorem about total variation of the raw pair measure.

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

For the two-prime cube, $B_{\{2,p\}}=5(1+p^2)\le(50/9)p^2$ and $C_{\{2,p\}}=(5/4)(p-1+p^{-2})\ge(5/6)p$ for $p\ge3$. Hence $q\ge256p$ implies the same strict margin condition for $\{2,p\}$, while it trivially does so for $\{2\}$. Their opposite parity signs give the strict increment above. Expanding the four numerator subsets of $\{2,p\}$ and subtracting the two subsets of $\{2\}$ leaves *exactly* the $p$ and $2p$ Möbius terms, proving the payment identity without a hidden cube-overlap argument.

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

The old $q^{-5/4}$ bound is valid **only under its stronger hypothesis** $q>32B_P$. It does not classify all sign-locked selected cubes. The refined signal-to-error ratio $qC_P/B_P$ reaches moving supports with $B_P\gtrsim q$ and, for one prime $p(q)\asymp q$, produces a harmonic-divergent **disjoint numerator-prime channel**. Completing denominator cofactors alone does **not** make every selected numerator channel summable. But numerator activation by $2$ exposes a disjoint opposite-sign $2p$ channel with greater harmonic magnitude; both selected signed tails are non-summable. The hard problem is therefore an *all-grade source transfer/payment law* under the physical cutoff and common-gcd limit, not isolation of a prime debt or a local cube sign. This is a route-level reinterpretation to test, not an RH producer.

## Research status

- Corpus audit: Route E already proves eventual parity for a fixed numerator Boolean cube against a **prime denominator only** (`RouteEPrimitiveAllGradeParityBarrier.lean`); it does not include all smaller-prime denominator cofactors. Search for Route E largest-prime/cofactor completion and exact kernel usages found no existing theorem of this form. This is a corpus novelty claim, not an external-priority claim.
- Positive survivor: exact main term and *amplified* parity margin $C_P$, a linear-in-support sign range, and **bilateral non-summability of disjoint prime and composite numerator fibres** after full denominator-cofactor completion. The old $q^{-5/4}$ majorant remains a sharp statement of its restricted far-prime regime, not a global selected-family law.
- Lean status: `RouteELargestPrimeFibreParity.lean` proves the full finite squarefree support expansion, kernel and cutoff errors, parity margin, moving-singleton lower bound, Bertrand prime choice, and prime-channel non-summability. `routeELargestPrimeCofactorSet q` is exactly all primes below $q$. `routeELargestPrimeMobiusFibre_eq_cut` identifies every squarefree-support coefficient with literal $\mu(a_S)\mu(qd_D)$. `routeELargestPrimeSingleton_eq_empty_add_prime`, `routeELargestPrimePrimeNumerator_harmonic_lower`, and `not_summable_routeELargestPrimePrimeNumeratorSelected` close the disjoint prime-only survivor. `routeELargestPrimeTwoActivatedIncrement_eq_prime_add_composite`, `routeELargestPrimeTwoPrimeNumerator_harmonic_upper`, and `not_summable_routeELargestPrimeCompositeNumeratorSelected` identify the first literal composite payment and prove its selected tail non-summable. `RouteEFixedOrderSelectedFibreBoundary.lean` proves $K_1=K$, fixed-order one-fibre summability, real-ratio secant transport, quantitative all-grade first-cofactor dominance, homogeneity, and the positive-prime/negative-$2p$ compact-band floors at every $r\ge1`. `RouteEFixedOrderPrimeBandMass.lean` proves uniform finite-block lower/upper inequalities for the two disjoint numerator grades and identifies both window cardinalities with the established prime-window sets. Both new leaves passed `lake env lean`; the first passed targeted `lake build --old`; umbrella imports are wired without a full umbrella build. The PNT-to-unbounded-mass passage remains a paper deduction, not a Lean theorem.
- Falsifier / next attack: test the dense two-prime proportional-band conjecture at fixed $1<r<2$, then its composite-numerator counterpayment. The unresolved RH producer is the *complete* cutoff-uniform covariance, including common-gcd/Gamma coupling and all numerator grades. A single selected numerator per $q$ is now proved summable at fixed $r>1$ and cannot discharge it. No RH producer is presently established.
