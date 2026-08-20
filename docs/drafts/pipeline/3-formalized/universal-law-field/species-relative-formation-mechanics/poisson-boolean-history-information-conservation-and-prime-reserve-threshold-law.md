# Poisson--Boolean--history information conservation and prime reserve threshold law

**ID:** ULF-SRFM-2  
**Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [THREE-SPECIES FUSION] [NEW CORPUS CONSEQUENCE] [NOVELTY UNVERIFIED] [LEAN CLOSED] [NOT RH]`

## 1. Purpose

This card closes the first genuine fusion gate in species-relative formation mechanics.  A count is
not identified with its hard-core support.  It is split, without loss, into

1. an additive multiplicity state;
2. a Boolean occupancy state;
3. a conditional excess-arrival history.

The split is a bijection, and relative information obeys an exact horizontal--vertical
conservation law.  On the literal reflected prime odds, the vertical information discarded by
Booleanization has a sharp all-prime summability transition at half aperture.

The general entropy chain rule is classical.  The load-bearing new corpus consequence is the
arithmetic reserve asymptotic and its exact threshold.  Neither statement proves RH or supplies a
source theorem forcing Booleanized and multiplicity-complete observers to agree.

## 2. Three formation species and common recovery

Write

\[
 \mathcal C=\mathbb N_0,
 \qquad \mathcal B=\{0,1\},
 \qquad \mathcal H=\mathbb N_0.
\]

The formation split is

\[
 \Phi(0)=0,
 \qquad
 \Phi(n+1)=(1,n).
 \tag{2.1}
\]

Thus

\[
 \Phi:\mathcal C\longrightarrow
 \{0\}\sqcup(\{1\}\times\mathcal H)
 \tag{2.2}
\]

is a bijection.  Its inverse is the common recovery law

\[
 \Psi(0)=0,
 \qquad
 \Psi(1,n)=n+1.
 \tag{2.3}
\]

The Boolean coordinate says whether a source label is occupied.  Conditional on occupancy, the
history coordinate records every arrival beyond the first.  Neither coordinate alone reconstructs
the count, while their marked pair does.

Let \(P,Q\) be probability laws on \(\mathcal C\) with full support.  Put

\[
 q_P=P(N>0),\qquad q_Q=Q(N>0),
 \tag{2.4}
\]

and let \(K_P,K_Q\) be the conditional laws of \(N-1\) given \(N>0\).

### Theorem 2.1 (formation split and information conservation)

The marked Boolean--history packets determine \(P,Q\) uniquely, and

\[
 \boxed{
 D(P\Vert Q)
 =D(\operatorname{Bern}(q_P)\Vert\operatorname{Bern}(q_Q))
  +q_P D(K_P\Vert K_Q).}
 \tag{2.5}
\]

Consequently the symmetrized information satisfies

\[
 \boxed{
 J(P,Q)=J_B(q_P,q_Q)
 +q_P D(K_P\Vert K_Q)
 +q_Q D(K_Q\Vert K_P).}
 \tag{2.6}
\]

The last two terms are the **history reserve** erased by Boolean support projection.

#### Proof

Under \(\Phi\), the vacuum probabilities are \(1-q_P,1-q_Q\), while for \(n\ge0\)

\[
 P(\Phi(N)=(1,n))=q_PK_P(n),
 \qquad
 Q(\Phi(N)=(1,n))=q_QK_Q(n).
\]

Therefore

\[
\begin{aligned}
D(P\Vert Q)
&=(1-q_P)\log\frac{1-q_P}{1-q_Q}
  +\sum_{n\ge0}q_PK_P(n)
     \log\frac{q_PK_P(n)}{q_QK_Q(n)}\\
&=D(\operatorname{Bern}(q_P)\Vert\operatorname{Bern}(q_Q))
  +q_PD(K_P\Vert K_Q).
\end{aligned}
\]

Apply the same identity with \(P,Q\) exchanged and add.  Reconstruction is (2.3).  ∎

### Intervention compatibility

For any parameterized family \(P_\theta\), formation followed by parameter intervention equals
parameter intervention followed by the maps

\[
 \theta\longmapsto q_{P_\theta},
 \qquad
 \theta\longmapsto K_{P_\theta}.
 \tag{2.7}
\]

This is not an analogy between three statistics.  It is a single law on a common recovered sample
space, with exact reconstruction and an exact conserved information budget.

## 3. Poisson formation split

Let \(P_\lambda=\operatorname{Pois}(\lambda)\), \(\lambda>0\).  Then

\[
 q_\lambda=1-e^{-\lambda},
 \tag{3.1}
\]

and the excess-history law is the shifted zero-truncated Poisson law

\[
 K_\lambda(n)
 =\frac{\lambda^{n+1}}{(n+1)!(e^\lambda-1)},
 \qquad n\ge0.
 \tag{3.2}
\]

### Corollary 3.1 (Poisson--Boolean--multiplicity identity)

For \(\lambda,\mu>0\),

\[
\begin{aligned}
D(\operatorname{Pois}(\lambda)\Vert\operatorname{Pois}(\mu))
&=D(\operatorname{Bern}(q_\lambda)\Vert
       \operatorname{Bern}(q_\mu))\\
&\quad+q_\lambda D(K_\lambda\Vert K_\mu).
\end{aligned}
\tag{3.3}
\]

The symmetric history reserve is

\[
 \mathcal R(\lambda,\mu)
 =q_\lambda D(K_\lambda\Vert K_\mu)
  +q_\mu D(K_\mu\Vert K_\lambda)\ge0.
 \tag{3.4}
\]

It vanishes exactly when \(\lambda=\mu\).

#### Proof

Equations (3.1)--(3.2) follow by conditioning the Poisson mass function on \(N>0\).
Apply Theorem 2.1.  Strictness follows from faithfulness of relative entropy and injectivity of
\(\lambda\mapsto K_\lambda\).  ∎

## 4. Reflected prime specialization

Fix \(0<t<1\).  For every prime \(p\), define reflected odds

\[
 a_p=p^{t-1},
 \qquad
 b_p=p^{-t-1},
 \qquad
 L_p=\log(a_p/b_p)=2t\log p.
 \tag{4.1}
\]

Let

\[
 \lambda(x)=\log(1+x),
 \qquad
 q(x)=\frac{x}{1+x}.
 \tag{4.2}
\]

Then \(1-e^{-\lambda(x)}=q(x)\).  Hence the Poisson intensities
\(\lambda(a_p),\lambda(b_p)\) have exactly the adaptive reflected Bernoulli laws as their Boolean
supports.

Define the prime history reserve

\[
\begin{aligned}
 R_p(t)
 &=(\lambda(a_p)-\lambda(b_p))
       \log\frac{\lambda(a_p)}{\lambda(b_p)}\\
 &\quad-(q(a_p)-q(b_p))\log\frac{a_p}{b_p}.
\end{aligned}
\tag{4.3}
\]

The first line is symmetric Poisson information and the second is symmetric Boolean information.
By (3.4),

\[
 R_p(t)=q(a_p)D(K_{\lambda(a_p)}\Vert K_{\lambda(b_p)})
 +q(b_p)D(K_{\lambda(b_p)}\Vert K_{\lambda(a_p)})>0.
\tag{4.4}
\]

### Theorem 4.1 (sharp prime reserve asymptotic)

For every fixed \(0<t<1\),

\[
 \boxed{
 R_p(t)\sim t(\log p)p^{-2(1-t)}}
 \qquad(p\to\infty\text{ through primes}).
 \tag{4.5}
\]

#### Proof

Put

\[
 f(x)=\frac{\log(1+x)}x,
 \qquad
 g(x)=\log(1+x)-\frac{x}{1+x}.
\tag{4.6}
\]

Since \(\lambda(x)=xf(x)\), equation (4.3) becomes

\[
 R_p(t)
 =[g(a_p)-g(b_p)]L_p
 +(\lambda(a_p)-\lambda(b_p))
     \log\frac{f(a_p)}{f(b_p)}.
\tag{4.7}
\]

As \(x\downarrow0\),

\[
 g(x)=\frac{x^2}{2}+O(x^3),
 \qquad
 \log f(x)=-\frac x2+O(x^2).
\tag{4.8}
\]

Moreover \(b_p/a_p=p^{-2t}\to0\), \(a_p\to0\), and \(L_p\to\infty\).  Consequently

\[
 \frac{g(a_p)-g(b_p)}{a_p^2}\longrightarrow\frac12,
\tag{4.9}
\]

whereas

\[
 \frac{(\lambda(a_p)-\lambda(b_p))
     \log(f(a_p)/f(b_p))}{a_p^2L_p}longrightarrow0.
\tag{4.10}
\]

Thus \(R_p(t)/(a_p^2L_p)\to1/2\).  Since
\(a_p^2=p^{-2(1-t)}\) and \(L_p=2t\log p\), (4.5) follows.  ∎

### Theorem 4.2 (exact all-prime threshold)

For \(0<t<1\),

\[
 \boxed{
 \sum_{p\ \mathrm{prime}}R_p(t)<\infty
 \quad\Longleftrightarrow\quad
 0<t<\frac12.}
 \tag{4.11}
\]

At \(t=0\), every reserve is zero.

#### Proof

Set \(\alpha=2(1-t)\).  Theorem 4.1 makes \(R_p(t)\) eventually comparable, above and below, to
\((\log p)p^{-\alpha}\).

If \(t<1/2\), then \(\alpha>1\).  Choose \(0<\varepsilon<\alpha-1\).  Eventually
\(\log p\le p^\varepsilon\), and the prime series is dominated by the convergent integer series
\(\sum_{n\ge2}n^{-(\alpha-\varepsilon)}\).

If \(t\ge1/2\), then \(\alpha\le1\).  Eventually \(\log p\ge1\) and
\(p^{-\alpha}\ge p^{-1}\).  Euler's divergence of \(\sum_p1/p\) forces divergence.  ∎

## 5. What this adds

The theorem separates two previously conflated questions.

- The Boolean reflected observer carries a first-arrival law.
- The Poisson formation carries all multiplicities.
- Their information difference is a positive conditional-history current.
- That current becomes globally finite precisely before half aperture.

Thus the half-aperture boundary is not inserted as a norm choice.  It is the convergence boundary
of information stored in the fibres of a literal species change.

## 6. Hostile tests and exact scope

1. **The entropy chain rule is not new.**  Theorem 2.1 is a concrete formation interpretation of
   classical disintegration.  New leverage lies in Theorems 4.1--4.2.
2. **Booleanization alone is not conservative.**  It drops the strictly positive reserve whenever
   reflected intensities differ.
3. **The pair is conservative only while marked.**  Forgetting which history belongs to which
   occupied source label destroys reconstruction.
4. **The threshold is not an RH selector.**  Every \(0<t<1/2\) has finite positive reserve.
5. **No universality over all formation species is claimed.**  Bose/Witt carry, phase winding,
   non-Hausdorff completion, and jet formation need separate comparison laws.
6. **The parameter range is load-bearing.**  The proof uses \(a_p\to0\), hence \(t<1\).
7. **No source quasi-invariance is produced.**  The theorem measures information lost by a declared
   species change; it does not force that loss to vanish.

## 7. Literature collision audit

Hurdle models routinely split a count into a binary zero/nonzero component and a zero-truncated
count component.  The KL chain rule under a measurable partition is classical.  Poisson and
zero-truncated-Poisson likelihoods are standard.

Representative parents are Fang--Fawzi--Renner--Sutter, *A chain rule for the quantum relative
entropy* ([arXiv:1909.05826](https://arxiv.org/abs/1909.05826)), whose starting point is the
classical conditional KL chain rule; López--Dunlavy--Lehoucq, *Zero-Truncated Poisson Regression
for Sparse Multiway Count Data Corrupted by False Zeros*
([arXiv:2201.10014](https://arxiv.org/abs/2201.10014)); and Agyarko--Acheampong--Seidu--Iddi,
*Marginalised Poisson Hurdle Model for Cross-Sectional Count Data with Excess Zeros*
([arXiv:2606.03023](https://arxiv.org/abs/2606.03023)).  Li's information-event construction
([arXiv:2307.07506](https://arxiv.org/abs/2307.07506)) is an adjacent Poisson representation of
conditional and relative information, but not the formation reserve studied here.

Broad searches through August 2026 found no source treating the reflected arithmetic family
(4.1), the reserve (4.3), or the sharp prime threshold (4.11).  Closest parents include current
Poisson hurdle work and general relative-entropy chain rules.  Therefore the correct status is
classical mechanism plus a new corpus theorem; no external priority claim is made.

## 8. Lean status

Closed unconditionally in

* `formal/GaloisForLFunctions/HTGeometry/CountableRelativeEntropyValue.lean`,
* `formal/GaloisForLFunctions/HTGeometry/PoissonOccupancyHistorySplit.lean`,
* `formal/GaloisForLFunctions/HTGeometry/CountFormationSplit.lean`,
* `formal/GaloisForLFunctions/HTGeometry/ReflectedPrimeHistoryReserve.lean`.

All five formalization items are discharged: the count-to-Boolean-history bijection and the
countable KL chain rule (`formationSplit`, `toReal_klDiv_formationSplit`), the explicit Poisson
conditional mass identities (`countExcessLaw_poissonMeasure`), positivity of the reserve
(`primeHistoryReserve_pos`), the small-odds asymptotic (`isEquivalent_primeHistoryReserve`), and
the exact prime-series threshold (`summable_primeHistoryReserve_iff`).  See the companion
`...-formalized.md` for the full result-to-declaration table.  Every declaration depends only on
`propext`, `Classical.choice`, `Quot.sound`.
