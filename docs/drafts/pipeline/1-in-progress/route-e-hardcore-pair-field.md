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
Euler source.  It is paper-proven; Lean currently certifies the local
factor, not this global sign.  The physical Gibbs multiplier is not a
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
of the local exclusion interaction cannot do that alone.  This is a
paper proof; the exact grade law remains to formalize.

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
by the displayed pointwise joint mass; it is not yet a Lean theorem.
The positive common-gcd scale weight of the complete Route E moment is
an additional two-leg kernel and cannot be dropped.  The reweighted
observable still contains the literal \(\mu\) sign and grows strongly
with occupied primes; the spectral identity alone gives no bound.

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

Prove or refute the double-shell local-limit estimate for the exact
trinary Euler product, first at the source's physical multiplier (not a
surrogate window), then propagate its **signed** effect through the
literal Route E covariance.  If it fails, extract the sharp correction
factor and ask whether that factor, rather than transport, carries the
missing arithmetic orientation.
