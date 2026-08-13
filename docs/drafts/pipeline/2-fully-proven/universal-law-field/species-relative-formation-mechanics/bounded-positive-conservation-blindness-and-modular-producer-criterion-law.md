# Bounded positive-conservation blindness and modular producer criterion law

**ID:** ULF-SRFM-5  
**Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [SELECTION-PRODUCER CLASSIFICATION]`
`[BOUNDED-CONSERVATION NO-GO] [MODULAR SURVIVOR] [NEW CORPUS CONSEQUENCE]`
`[NOVELTY UNVERIFIED] [LEAN PENDING] [NOT RH]`

## 1. Purpose

ULF-SRFM-4 proves that bounded recovered-history action along native superposition depth selects
equal rates. This card asks which source conservation laws can possibly provide that bound.

Answer is sharp. All probability-normalized bounded comparisons are blind:

- signed total mass is identically zero;
- total variation is uniformly bounded;
- Hellinger distance is uniformly bounded and saturates;
- Jensen--Shannon divergence is uniformly bounded;
- Boolean observer information tends to zero.

They coexist with linearly divergent recovered-history action. A viable producer must retain an
unbounded likelihood scale. Uniform source control of the logarithmic Radon--Nikodym cocycle is an
exact sufficient law and forces neutrality.

## 2. Superposition pair

Fix \(\alpha,\beta>0\), and for \(m\ge1\) put

\[
 P_m=\operatorname{Pois}(m\alpha),
 \qquad Q_m=\operatorname{Pois}(m\beta).
 \tag{2.1}
\]

Let \(B_m,H_m,C(\alpha,\beta)\) be as in ULF-SRFM-4, so

\[
 J(P_m,Q_m)=mC(\alpha,\beta)=B_m+H_m.
 \tag{2.2}
\]

For every \(n\in\mathbb N_0\), likelihood ratio is

\[
 L_m(n)=\frac{P_m(n)}{Q_m(n)}
 =e^{-m(\alpha-\beta)}\left(\frac\alpha\beta\right)^n.
 \tag{2.3}
\]

Its logarithm is the formed modular cocycle

\[
 \ell_m(n)=\log L_m(n)
 =n\log(\alpha/\beta)-m(\alpha-\beta).
 \tag{2.4}
\]

## 3. Bounded-conservation blindness

Use total-variation convention

\[
 d_{\rm TV}(P,Q)=\sup_A|P(A)-Q(A)|\le1.
\]

Let Hellinger affinity be \(\operatorname{Aff}(P,Q)=\sum_n\sqrt{P(n)Q(n)}\), and squared
Hellinger distance \(H^2(P,Q)=2-2\operatorname{Aff}(P,Q)\). Let

\[
 \operatorname{JS}(P,Q)
 ={1\over2}D(P\Vert M)+{1\over2}D(Q\Vert M),
 \qquad M={P+Q\over2}.
\]

### Theorem 3.1 -- bounded positive quantities cannot control hidden formation

For every \(m\ge1\),

\[
 (P_m-Q_m)(\mathbb N_0)=0,
 \qquad d_{\rm TV}(P_m,Q_m)\le1,
 \qquad \operatorname{JS}(P_m,Q_m)\le\log2.
 \tag{3.1}
\]

Moreover,

\[
 \boxed{
 \operatorname{Aff}(P_m,Q_m)
 =\exp\!\left[-{m\over2}(\sqrt\alpha-\sqrt\beta)^2\right].}
 \tag{3.2}
\]

Hence for \(\alpha\ne\beta\),

\[
 H^2(P_m,Q_m)\longrightarrow2,
 \qquad B_m\longrightarrow0,
 \qquad H_m\sim mC(\alpha,\beta)\longrightarrow\infty.
 \tag{3.3}
\]

Thus bounded signed mass, total variation, Hellinger, Jensen--Shannon, and saturated Boolean
information do not imply bounded recovered-history action.

#### Proof

Both laws have mass one, proving signed cancellation and the total-variation bound.
For \(M=(P+Q)/2\), both densities relative to \(M\) are at most two, so each directed relative
entropy in Jensen--Shannon divergence is at most \(\log2\).

For affinity,

\[
\begin{aligned}
 \sum_{n\ge0}\sqrt{P_m(n)Q_m(n)}
 &=e^{-m(\alpha+\beta)/2}
   \sum_{n\ge0}{(m\sqrt{\alpha\beta})^n\over n!}\\
 &=e^{-m(\alpha+\beta)/2+m\sqrt{\alpha\beta}}\\
 &=\exp\!\left[-{m\over2}(\sqrt\alpha-\sqrt\beta)^2\right].
\end{aligned}
\]

Equation `(3.3)` follows from `(3.2)` and ULF-SRFM-4, Theorem 3.1. QED.

### Corollary 3.2 -- source-zero and reflection parity are insufficient

For the reflected prime rates

\[
 \alpha_p(t)=\log(1+p^{t-1}),
 \qquad \beta_p(t)=\log(1+p^{-t-1}),
\]

the signed family \(\Sigma_m(t)=P_m(t)-Q_m(t)\) obeys

\[
 \Sigma_m(t)(\mathbb N_0)=0,
 \qquad \Sigma_m(-t)=-\Sigma_m(t),
 \qquad \|\Sigma_m(t)\|_{\rm TV}\le2,
 \tag{3.4}
\]

for every \(m\) and every \(|t|<1\). Nevertheless its recovered-history action is unbounded for
every \(t\ne0\).

Thus a zero-mass reflected signed source with uniformly bounded variation does not supply the Gate
VI conservation premise.

#### Proof

Reflection exchanges the two rates. Equations `(3.4)` are immediate. ULF-SRFM-4, Corollary 6.1,
gives unbounded history action off the neutral point. QED.

## 4. Modular producer criterion

Let \(P,Q\) be mutually absolutely continuous probability laws, put
\(L=dP/dQ\), \(\ell=\log L\), and assume \(\ell\in L^1(P+Q)\).

### Theorem 4.1 -- logarithmic-cocycle domination

\[
 \boxed{
 J(P,Q)
 =\int\ell\,d(P-Q)
 \le\int|\ell|\,d(P+Q).}
 \tag{4.1}
\]

Consequently, for any formed pair admitting a Boolean--history split,

\[
 H(P,Q)\le J(P,Q)le\int|\ell|\,d(P+Q).
 \tag{4.2}
\]

#### Proof

By definition,

\[
 D(P\Vert Q)=\int\ell\,dP,
 \qquad D(Q\Vert P)=-\int\ell\,dQ.
\]

Adding gives equality in `(4.1)`. Triangle inequality gives its upper bound. The exact information
split writes \(J=B+H\) with \(B,H\ge0\), proving `(4.2)`. QED.

### Corollary 4.2 -- uniform modular conservation selects equal rates

For \(P_m,Q_m\) from `(2.1)`, if

\[
 \sup_{m\ge1}\int|\ell_m|\,d(P_m+Q_m)<\infty,
 \tag{4.3}
\]

then \(\alpha=\beta\). It is already enough to assume `(4.3)` along any unbounded sequence of
formation depths.

#### Proof

Equations `(4.2)`--`(4.3)` uniformly bound \(H_m\). ULF-SRFM-4, Corollary 3.2, forces rate
equality. QED.

### Corollary 4.3 -- bounded modular oscillation also suffices

If one has source constants \(c_m\in\mathbb R\) and one \(C<\infty\) such that

\[
 |\ell_m-c_m|\le C
 \quad(P_m+Q_m)\text{-almost everywhere for every }m,
 \tag{4.4}
\]

then \(\alpha=\beta\).

#### Proof

Since \((P_m-Q_m)(\Omega)=0\), subtracting \(c_m\) does not change `(4.1)`. Therefore

\[
 J(P_m,Q_m)
 =\int(\ell_m-c_m)d(P_m-Q_m)le2C.
\]

The history action is bounded, and Corollary 4.2 applies. QED.

Equation `(4.4)` is the exact non-circular producer target: a source-derived uniform modular
oscillation bound may be verified before positive information is evaluated. It is stronger than
reflection, zero mass, total-variation control, or unitary phase covariance, and weaker than asking
the two formed laws to agree pointwise.

## 5. Hostile boundary and RH-facing gate

1. **Bounded divergence means bounded action. -- False.** Total variation, Hellinger, and
   Jensen--Shannon are bounded by construction and cannot control extensive hidden information.
2. **A signed source zero bounds positive separation. -- False.** `(3.4)` is an explicit reflected
   countermodel at every formation depth.
3. **Functional-equation parity bounds modular cocycle. -- False.** Parity exchanges
   \(\ell_m\) with \(-\ell_m\); it gives no magnitude bound.
4. **Any centered likelihood is bounded. -- False.** Centering removes scalar gauge only. For
   Poisson pair `(2.4)`, coefficient of \(n\) remains \(\log(\alpha/\beta)\), and count history
   escapes linearly.
5. **Modular criterion proves RH. -- False.** One must still derive `(4.3)` or `(4.4)` for the
   literal pre-zero source packet attached to each spectral state. Taking it as an axiom is
   equivalent to inserting missing conservation.

The new Gate VI target is therefore:

> Construct a source-normal logarithmic likelihood cocycle for the reflected formed packet and
> prove uniform integrability or uniform oscillation under native superposition depth before divisor
> specialization.

ULF-SRFM-4 and this card then force neutral rate, hence neutral reflected parameter.

## 6. Literature and scope

Poisson likelihood formulas and divergences are classical and are treated systematically by
Leskelä, [arXiv:2404.00294](https://arxiv.org/abs/2404.00294). Relative-entropy chain rules and
Markov recovery are established; Lacker [arXiv:1510.07030](https://arxiv.org/abs/1510.07030)
characterizes relative entropy through chain-rule behavior. Boundedness of Jensen--Shannon and
Hellinger quantities is standard.

Broad current-arXiv search found no exact coupled classification combining reflected Poisson
superposition, Boolean saturation, divergent conditional-history action, failure of every bounded
positive comparison, and the centered modular producer criterion. Claim remains new-to-corpus with
external novelty unverified.

No Lean was written or built. Formalization is deferred until hostile paper audit is complete.
