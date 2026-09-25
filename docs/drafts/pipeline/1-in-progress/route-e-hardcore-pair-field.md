# Route E hard-core pair field: parity without exact transport

## Claim and status

This is a **new proposed interpretation**, not an RH proof.  Instead of choosing a
row kernel after defining one Möbius source, generate two squarefree prime sets
as the two colours of a single prime-by-prime exclusion field.  This makes
coprimality structural.  The unconditioned finite identities below have paper
proofs; the local physical two-shell law is open.  Do not promote a marginal
or macroscopic estimate to that law.

## Finite field and exact source law

For a finite prime set \(P\), independently at each \(p\in P\) choose
\((X_p,Y_p)=(0,0),(1,0),(0,1)\) with respective probabilities
\((p-1)/(p+1),1/(p+1),1/(p+1)\).  Write \(S=\{p:X_p=1\}\),
\(T=\{p:Y_p=1\}\).  Then \(S\cap T=\varnothing\) identically and each
marginal has critical Euler occupation probability \(q_p=1/(p+1)\), the
source already certified in `RouteEMovingEulerTiltChiSquareContiguity.lean`.

The joint Fourier/Mellin factor, with arbitrary phases \(z_p,w_p\), is
\[
  J_p(z,w)=\frac{p-1+z+w}{p+1},\qquad
  J_p(z,w)-M_p(z)M_p(w)
   =-\frac{(1-z)(1-w)}{(p+1)^2},\quad
  M_p(z)=\frac{p+z}{p+1}.
\]
Thus the interaction is negative and second-order in prime occupation,
not a column-normalization prescription.  At frequencies
\(z_p=e^{iu\log p/\log N}\), \(w_p=e^{iv\log p/\log N}\), telescoping products
give joint/marginal characteristic difference at most
\(|uv|(\log N)^{-2}\sum_p(\log p)^2/(p+1)^2\).  This is only
**macroscopic** log-energy decoupling.

There is also an exact finite **conjugate character order**.  If every
\(|z_p|=1\) and \(w_p=\overline{z_p}\), then
\(J_p(z_p,\overline{z_p})\) is real and
\[
  |M_p(z_p)|^2-J_p(z_p,\overline{z_p})
      =|1-z_p|^2/(p+1)^2\ge0.
\]
For \(p\ge3\), \(J_p\ge(p-3)/(p+1)\ge0\).  Only \(p=2\) may give a
negative factor.  If it does, the joint product is nonpositive while the
product of marginal squares is nonnegative; otherwise multiply the
local inequalities.  Hence, for **every** finite prime set,
\[
  \prod_{p\in P}J_p(z_p,\overline{z_p})
       \le\left|\prod_{p\in P}M_p(z_p)\right|^2.
\]
This is a nonlocal negative cross-covariance for the unweighted critical
Euler source.  The local factor and global sign are Lean-proven in
`RouteEHardCorePairField.lean`.  The physical Gibbs multiplier is not a
positive spectral weight for this inequality, so its signed Route E
covariance is **not** thereby controlled.

The sign is **not** negative semidefinite for arbitrary observables.
For two distinct prime coordinates \(p,q\), put
\(f(S)=(1_{p\in S}-q_p)(1_{q\in S}-q_q)\).  Prime coordinates of the
trinary field are independent, while
\(\operatorname{Cov}(X_p,Y_p)=-q_p^2\); hence
\(\mathbb E[f(S)f(T)]=q_p^2q_q^2>0\).  In general a centered
\(k\)-coordinate interaction carries sign \((-1)^k\).
Thus the conjugate-character order is a special mixture of grades, not
an operator-wide negative order.  The positive survivor is an exact
**grade-parity spectral law** for coprime exclusion.  Any physical
multiplier argument must control its even-grade projection; positivity
of the local exclusion interaction cannot do that alone.  The exact
grade law is Lean-proven in `RouteEHardCoreWalshSpectrum.lean`.

The stronger reinterpretation is spectral.  Conditional on the left
set \(S\), the right set occupies prime \(p\) with probability
\(0\) if \(p\in S\) and \(1/p\) otherwise.  This is a reversible
Markov transition for the critical Bernoulli source.  Its centered
one-prime coordinate \(X_p-q_p\) has eigenvalue \(-1/p\); independence
across primes makes every Walsh interaction \(\phi_K\) an eigenvector:
\[
   \mathcal K\phi_K
     =\frac{(-1)^{|K|}}{\prod_{p\in K}p}\phi_K
     =\frac{\mu(n_K)}{n_K}\phi_K,
       \qquad n_K=\prod_{p\in K}p.
\]
Thus a Möbius-over-radical sign appears as the **chirality spectrum of
coprime exclusion**.  This is a new interpretation of the pair operator;
it does **not** erase the literal Möbius coefficient from the original
Route E source.
The consequence for any real observable \(F\) is
\[
 \operatorname{Cov}(F(S),F(T))
   =\sum_{\varnothing\ne K\subseteq P}
       \frac{\mu(n_K)}{n_K}\,\widehat F(K)^2
\]
in the normalized biased Walsh basis.  Lean now proves both the
normalized eigenlaw and the **uncentered** quadratic identity
\(\mathbb E[F(S)F(T)]=\sum_K\mu(n_K)n_K^{-1}\widehat F(K)^2\)
in `RouteEHardCoreWalshSpectrum.lean`; subtracting the empty grade
gives the displayed centered formula.  This compresses
three distinct facts: exact source marginals, odd/even grade sign, and
the special conjugate-character order above.  It is a candidate
framework change, **not** evidence that the physical Route E observable
has the required odd-grade dominance.

There is an exact bridge to the **unweighted finite primitive sector**.
For disjoint \(S,T\), the joint field assigns
\[
 J_P(S,T)=\frac{C_P}{\prod_{p\in S}(p-1)\prod_{p\in T}(p-1)},
 \qquad C_P=\prod_{p\in P}\frac{p-1}{p+1}.
\]
Hence for every symmetric pair kernel \(H\), finite cutoff \(N\), and
critical coefficient exponent \(\sigma\), if
\(A_{N,\sigma}(S)=(-1)^{|S|}n_S^{-\sigma}
 \prod_{p\in S}(p-1)1_{n_S\le N}\), then
\[
 \sum_{\substack{a,b\le N\\a,b\text{ squarefree}\\(a,b)=1}}
    \frac{\mu(a)\mu(b)}{(ab)^\sigma}H(a,b)
 =C_P^{-1}\,\mathbb E_J[A_{N,\sigma}(S)
       A_{N,\sigma}(T)H(n_S,n_T)]
\]
provided \(P\) contains every prime \(\le N\).  This is paper-proven
by the displayed pointwise joint mass.  The finite-subset Radon identity
and generic primitive quadratic form are Lean-proven in
`RouteEHardCorePrimitiveBridge.lean`; the integer-indexed specialization
remains paper-only.
The positive common-gcd scale weight of the complete Route E moment is
an additional two-leg kernel and cannot be dropped.  The reweighted
observable still contains the literal \(\mu\) sign and grows strongly
with occupied primes; the spectral identity alone gives no bound.

The bridge sharpens the obstruction. For **every** real subset source \(a\),
Lean proves
\[
 C_P\sum_{S\cap T=\varnothing}a(S)a(T)
   =\sum_{K\subseteq P}\frac{\mu(n_K)}{n_K}
       \widehat{\big(A_Pa\big)}(K)^2,
 \qquad A_P(S)=\prod_{p\in S}(p-1).
\]
Thus the unweighted primitive-pair channel is *exactly* an indefinite
odd/even-grade energy after source-faithful Radon amplification. This is
stronger than an eigenfunction example, but no inequality on the physical
source follows. The complete Gamma ratio kernel and positive common-gcd
scale weight must still be retained. The existing positive Gamma-frequency
representation turns that kernel into an integrated odd/even-grade balance,
not automatic pointwise dominance. The decisive question is whether that
balance can be proved from a source-side identity surviving the physical
cutoff and all scales. Otherwise this spectral reinterpretation is a
classification/no-go, not an RH route.

## Empty-grade barrier: the Möbius source survives the change of basis

The zero Walsh grade is not a harmless vacuum term. For any real subset
observable $a$ and $q_p=(p+1)^{-1}$, the exact finite law is
$$
  \widehat{(A_Pa)}(\varnothing)
  =V_P\sum_{S\subseteq P} a(S)\prod_{p\in S}(1-p^{-1}),
  \qquad V_P=\prod_{p\in P}\frac{p}{p+1}.
$$
`RouteEHardCoreEmptyGradeBarrier.lean` proves this, including a closed
prime-indexed specialization. For the literal signed squarefree cutoff
$a(S)=(-1)^{|S|}n_S^{-\sigma}1_{n_S\le N}$ and all primes $\le N$,
the normalized zero grade is the weighted Möbius sum
$$
  V_P^{-1}\widehat{(A_Pa)}(\varnothing)
     =\sum_{n\le N}\frac{\mu(n)\varphi(n)}{n^{1+\sigma}}.
$$
The integer-indexed specialization is paper-proven, Lean-pending.

More sharply, put $b(n)=\mu(n)\varphi(n)/n$ for $n\ge1$ and define the
multiplicative function $g$ by $g(p^k)=1/p$ for every $k\ge1$.
Prime-power comparison gives $b=\mu*g$ under Dirichlet convolution.
`RouteEHardCoreTotientConvolution.lean` now proves this equality as a
closed arithmetic-function identity, proves $g(p^k)=1/p$, and identifies
the coefficient with $\mu(n)\varphi(n)/n$ for every positive integer.
The inverse $h=g^{-1}$ has
$h(p^k)=-p^{-1}(1-p^{-1})^{k-1}$ for $k\ge1$.
Both $\sum_n|g(n)|n^{-\alpha}$ and $\sum_n|h(n)|n^{-\alpha}$ converge
for every $\alpha>0$: their prime-local tails are bounded by
$p^{-1-\alpha}/(1-p^{-\alpha})$. Therefore finite convolution and
absolute majorization transfer any power bound $O(x^\beta)$, $\beta>0$,
between $\sum_{n\le x}b(n)$ and the Mertens sum $M(x)$ in both directions.
At $\sigma=1/2$, Abel summation further makes a subpower bound on the
**normalized** zero grade equivalent to the usual RH-scale Mertens bounds.
This transfer has a dependency-closed paper proof. The convolution and
integer-indexed coefficient are Lean-closed; the inverse, weighted absolute
summability, summatory transfer, and subset-to-integer cutoff bijection remain
Lean-pending. The theorem does not establish the RH-scale bound.

The calculation has a finite-summatory refinement of the corpus's existing
analytic-unit universality law
(`MobiusEnergyAnalyticUnitWallUniversalityLaw.lean`); it is **not** a new
universal mechanism. Let
$0\le\delta_p\le\min(1,C/p)$ for every prime, and define the multiplicative
squarefree coefficient $b_\delta$ by $b_\delta(p)=-1+\delta_p$ and
$b_\delta(p^k)=0$ for $k\ge2$. Then, for **every** $\beta>0$,
$$
  \sum_{n\le x}b_\delta(n)=O(x^\beta)
  \quad\Longleftrightarrow\quad
  \sum_{n\le x}\mu(n)=O(x^\beta).
$$
Indeed $b_\delta=\mu*g_\delta$, where $g_\delta(1)=1$ and
$g_\delta(p^k)=\delta_p$ for $k\ge1$. Its Dirichlet inverse satisfies
$h_\delta(p^k)=-\delta_p(1-\delta_p)^{k-1}$. For each $\alpha>0$,
both weighted absolute sums $\sum_n|g_\delta(n)|n^{-\alpha}$ and
$\sum_n|h_\delta(n)|n^{-\alpha}$ converge: each nonconstant prime-local
sum is bounded by $C p^{-1-\alpha}/(1-p^{-\alpha})$, and the sum of these
bounds over primes converges. Convolving either summatory function with
the other coefficient and using these weighted absolute sums proves both
implications. The original empty-grade coefficient is $\delta_p=1/p$.
Thus **no tame independent prime-local change of measure** can improve
the RH-scale zero-grade source bound; an effective mechanism must use the
coupled grades, the cutoff-dependent interaction, or a genuinely
nonlocal/singular source law. This paper-level finite-summatory statement
sharpens this card's obstruction but does not move the main producer frontier;
its generic Lean formalization remains open.

Route consequence: a proof that bounds each Walsh grade separately must
already pay an RH-equivalent zero grade. The exact spectral bridge may still
allow cancellation *between* grades and common-gcd scales; the theorem does
not rule that out. It identifies precisely why an operator norm or
Hilbert--Schmidt estimate alone cannot be the missing source-side payment.

`RouteEPrimitiveAllGradeParityBarrier.lean` already proves that the **literal
physical primitive Gamma kernel** switches its far-cone insertion sign with
every grade, and exhibits a fixed-support cone-scale sign transition. The
Walsh-grade parity found here is therefore not a replacement for that
physical result. It gives a different, exact diagonalization of the
coprime-exclusion source, but does not settle the corpus's collective
cube-overlap or cross-fibre signs. Any next theorem must couple those
physical fibres to the Walsh energy rather than merely reproduce grade
alternation.

A tempting infinite-prime reading is that the eigenvalues are square-summable
(\(\prod_p(1+p^{-2})\) converges) but not absolutely summable
(\(\prod_p(1+p^{-1})\) diverges). This does **not** create an independent
producer: `GibbsCriticalSieveNormalizationWall.lean` already proves the
same first-order/second-order normalization wall for the critical Gibbs
source. The new contribution is the *source-faithful signed spectrum* and
its exact primitive-pair bridge. Compactness or Hilbert--Schmidt regularity
alone cannot pay the physical current after restoring the sieve density.

Another false lead is the uncut two-variable signed Euler series. In its
absolute-convergence region its local factor $1-p^{-u}-p^{-v}$ can be
factored against the three reciprocal-zeta local factors at $u$, $v$,
and $u+v$; the leftover local error begins at $p^{-2u-v}$ and
$p^{-u-2v}$. The apparent zero from $\zeta(u+v)^{-1}$ at the critical
conjugate pair is an analytic-continuation statement, **not** a uniform
estimate for the finite hard-cutoff primitive sum. It cannot replace the
missing shell and common-scale payment. This is a paper-level algebraic
observation, not yet a Lean theorem and not a new RH producer.

If \(3\in P\), the union cardinality is odd with probability exactly
\(1/2\), because its parity characteristic has factor
\(1-4/(3+1)=0\).  Condition the joint field on that odd event.  It now
reverses the signs of \(S,T\) and remains coprime.  Its one-leg density
relative to the original Bernoulli source is exactly
\[
  r_P(S)=1-(-1)^{|S|}\prod_{p\in P\setminus S}(1-2/p).
\]
Indeed, conditional on \(S\), the other leg occupies each unused prime
with probability \(1/p\).  The resulting chi-square defect is
\[
  \chi^2_P=\prod_{p\in P}
  \left(1-\frac{4(p-1)}{p(p+1)}\right),\qquad
  1-\frac{4(p-1)}{p(p+1)}
  =\left(\frac{p-1}{p+1}\right)^2+
    \frac{4}{p(p+1)^2}.
\]
For all primes \(p\le N\), Mertens' product and convergence of
\(\sum_p p^{-3}\) imply \(\chi^2_P\asymp (\log N)^{-4}\).  The original
parity bias is \(b_P=\prod_{p\in P}(p-1)/(p+1)\asymp(\log N)^{-2}\).
Every exactly parity-neutral marginal \(\nu\) has
\(\chi^2(\nu\Vert\mu)\ge b_P^2\) by Cauchy--Schwarz against parity;
therefore this coprime construction has optimal **order** of marginal
distortion.  Exact unchanged marginals on both legs with sure parity
reversal are impossible whenever \(b_P\ne0\).

The correction has an exact **prime-3 dilation seam**.  Let
\(P'=P\setminus\{3\}\), let \(\mu'\) be the product Bernoulli law on
\(P'\), and put \(c(S)=\prod_{p\in P'\setminus S}(1-2/p)\).  For every
observable \(W\) on prime subsets,
\[
  \mathbb E_{\mu}\big[(r_P(S)-1)W(S)\big]
   =\frac14\,\mathbb E_{\mu'}\!
      \left[(-1)^{|S|}c(S)
        \big(W(S\cup\{3\})-W(S)\big)\right].
\]
Proof: split the Bernoulli expectation according to occupation of 3.
Its absent probability is \(3/4\) and contributes
\(-\tfrac14(-1)^{|S|}c(S)W(S)\); its present probability is \(1/4\)
and contributes \(+\tfrac14(-1)^{|S|}c(S)W(S\cup\{3\})\).
For a physical observable of the represented integer,
\(W(S\cup\{3\})=W(3n_S)\): the error is a literal signed dilation
commutator, not a generic transport defect.  This identity is paper-only.

## Risky physical prediction and falsifier

The actual Route E source also carries the physical unit-log multiplier
\(\exp(\sigma E-xe^E)\).  Conditioning **both** legs to one physical
unit-log shell is the missing hard step.  The prediction to test is a
two-variable local limit: after this double conditioning, the one-leg
law is close enough to the literal source-weighted shell law, uniformly
in the moving critical cutoff, to pay the Route E signed covariance.
The exact required error and signed observable must be taken from the
literal Route E receiver, not chosen after seeing an estimate.

Potential falsifiers: double-shell mass can be too small; conditioning
can magnify the small unconditional parity defect; or the resulting
signed covariance can remain of wrong sign even if marginals are close.
The macroscopic Fourier bound does **not** exclude any of these.  A
one-leg shell Cauchy--Schwarz bound is also insufficient because the
other leg may lie outside the shell.

**Direct chi-square payment fails at scale.**  The best generic
Cauchy--Schwarz error from \(\chi^2_P\asymp(\log N)^{-4}\) is
\(O((\log N)^{-2})\) before shell localization.  It has no power saving
in the physical parameter and cannot itself pay an RH-scale signed
source.  Any continuation of this route must exploit cancellation in
the explicit prime-3 commutator or a stronger two-shell structural law.

This construction respects the corpus no-go against **complete**
coprime replica cells: only sparse disjoint pairs are present.  It also
does not evade `RouteEParityColumnLoadCircularityNoGo.lean`; it replaces
an exact row-stochastic parity kernel with a joint field whose small
source defect must still be paid.  Bureaux--Enriquez (2016),
<https://arxiv.org/abs/1612.03700>, proves that a related *geometric*
coprimality probability has an RH-equivalent convergence rate.  That
paper is not evidence that the above two-shell payment holds; rather it
warns that a sufficiently sharp physical error may itself be RH-hard.

## Next decisive test

First insert the **literal** `reciprocalMomentStationaryKernel_eq_gammaIntegral`
and `primitiveCubicScaleWeight` into the new prime-subset bridge, preserving
every finite cutoff and common-gcd scale. This will produce the exact
Gamma-integrated signed Walsh-grade balance required by the existing Route E
receiver. Then test a source-side constraint on that specific balance, with
the far-cone all-grade parity barrier and two-prime sign transition as
mandatory falsifiers. A free-observable sign inequality is already false.

Prove or refute the double-shell local-limit estimate for the exact
trinary Euler product, first at the source's physical multiplier (not a
surrogate window), then propagate its **signed** effect through the
literal Route E covariance.  If it fails, extract the sharp correction
factor and ask whether that factor, rather than transport, carries the
missing arithmetic orientation.
