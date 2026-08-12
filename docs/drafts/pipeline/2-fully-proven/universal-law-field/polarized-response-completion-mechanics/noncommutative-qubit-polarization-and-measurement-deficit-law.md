# Noncommutative qubit polarization and measurement-deficit law

- **ID:** ULF-PRCM-2
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / NONCOMMUTATIVE REALIZATION / FOURTH-ORGAN PREDICTION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN PENDING] [NOT RH]`
- **Statement:** A genuinely noncommuting two-level exponential formation realizes response
  polarization with cubic BKM-response decay and linear quantum work escape; diagonal observation
  changes the response exponent from three to four and contracts linear work to logarithmic work.

## 1. Noncommutative exponential formation

Let

\[
 X=\begin{pmatrix}0&1\\1&0\end{pmatrix},
 \qquad
 Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}
\]

be Pauli matrices.  Fix `b>0` and define

\[
 H_t=tZ+bX,
 \qquad
 r_t=\sqrt{t^2+b^2},
 \qquad
 F(t)=\log\operatorname{Tr}(e^{H_t})=log(2\cosh r_t),
 \tag{NQP.1}
\]

\[
 \rho_t=\frac{e^{H_t}}{\operatorname{Tr}(e^{H_t})}.
 \tag{NQP.2}
\]

Every `rho_t` is a faithful density matrix.  The family is genuinely noncommutative:

\[
 [H_s,H_t]=b(s-t)[Z,X]\ne0
 \qquad(s\ne t).
 \tag{NQP.3}
\]

Since `H_t^2=r_t^2 I`, functional calculus gives

\[
 e^{H_t}=\cosh r_t\,I+\frac{\sinh r_t}{r_t}H_t,
\]

and therefore

\[
 \boxed{
 \rho_t=\frac12\left(I+\frac{\tanh r_t}{r_t}(tZ+bX)\right).}
 \tag{NQP.4}
\]

Conjugation by `X` implements the functional equation:

\[
 \boxed{X\rho_tX=\rho_{-t}.}
 \tag{NQP.5}
\]

Indeed `XZX=-Z` and `XXX=X`.

## 2. Exact quantum response fusion

Put

\[
 m(t)=\operatorname{Tr}(\rho_tZ)=F'(t).
\]

### Theorem 2.1 — BKM response and quantum Jeffreys work

For every real `t`,

\[
 \boxed{
 m(t)=\frac{t}{r_t}\tanh r_t,}
 \tag{NQP.6}
\]

and the relative-entropy Hessian, equivalently the one-dimensional
Bogoliubov--Kubo--Mori response, is

\[
 \boxed{
 I_Q(t)=F''(t)
 =\frac{b^2}{r_t^3}\tanh r_t
  +\frac{t^2}{r_t^2}\operatorname{sech}^2 r_t>0.}
 \tag{NQP.7}
\]

For quantum relative entropy

\[
 D_Q(\rho\Vert\sigma)=\operatorname{Tr}\rho(\log\rho-\log\sigma),
\]

one has

\[
 \boxed{
 D_Q(\rho_s\Vert\rho_t)
 =(s-t)m(s)+F(t)-F(s),}
 \tag{NQP.8}
\]

and hence the exact polarized-work identity

\[
 \boxed{
 J_Q(\rho_s,\rho_t)
 =(s-t)(m(s)-m(t))
 =|s-t|\int_{\min(s,t)}^{\max(s,t)}I_Q(u)\,du.}
 \tag{NQP.9}
\]

Thus ULF-PRCM-1 applies with response `I_Q`.

### Proof

Differentiate `F(t)=log(2 cosh r_t)` and use `r_t'=t/r_t` to obtain `(NQP.6)`.
Differentiating once more gives `(NQP.7)`.

Because `rho_t=e^{H_t-F(t)I}`,

\[
 \log\rho_t=tZ+bX-F(t)I.
\]

The transverse term `bX` cancels from `log rho_s-log rho_t`.  Taking the `rho_s` trace gives
`(NQP.8)`.  Add the two orientations and use `m'=I_Q` to obtain `(NQP.9)`.  Positivity in
`(NQP.7)` follows from `b>0`, `r_t>0`, and `tanh r_t>0`.  QED.

## 3. Cubic response and incompatible completions

### Theorem 3.1 — transverse mixing produces the critical cubic tail

The BKM response has the exact asymptotic

\[
 \boxed{\lim_{t\to\infty}t^3I_Q(t)=b^2.}
 \tag{NQP.10}
\]

Moreover, for `t>=1`,

\[
 \boxed{
 \sqrt{I_Q(t)}
 \le b\,t^{-3/2}+2e^{-t}.}
 \tag{NQP.11}
\]

Consequently both BKM--Fisher tails have finite length, and the entire real orbit has finite
BKM--Fisher length.  Nevertheless,

\[
 \boxed{
 J_Q(\rho_t,\rho_{-t})
 =\frac{4t^2}{r_t}\tanh r_t,
 \qquad
 \lim_{t\to\infty}\frac{J_Q(\rho_t,\rho_{-t})}{4t}=1.}
 \tag{NQP.12}
\]

Thus the quantum formation is Fisher-precompact and information-proper.

### Proof

In the first term of `(NQP.7)`,

\[
 \frac{t^3}{r_t^3}\tanh r_t\longrightarrow1.
\]

The second term multiplied by `t^3` tends to zero because `r_t>=t` and
`sech^2 r_t<=4e^{-2t}`.  This proves `(NQP.10)`.

For `t>=1`, `(NQP.7)` gives

\[
 I_Q(t)\le b^2t^{-3}+4e^{-2t}.
\]

Using `sqrt(x+y)<=sqrt x+sqrt y` proves `(NQP.11)`.  Its right side is integrable on `[1,infinity)`;
continuity handles the compact interval.  Since `I_Q` is even, the negative tail is identical.

Equations `(NQP.5)` and `(NQP.9)` give

\[
 J_Q(\rho_t,\rho_{-t})=4t\,m(t)
 =\frac{4t^2}{r_t}\tanh r_t.
\]

Now `t/r_t->1` and `tanh r_t->1`, proving `(NQP.12)`.  QED.

### Boundary laws

Formula `(NQP.4)` gives

\[
 \rho_t\longrightarrow\frac{I+Z}{2},
 \qquad
 \rho_{-t}\longrightarrow\frac{I-Z}{2}.
 \tag{NQP.13}
\]

The BKM path reaches these orthogonal pure-state boundary laws at finite length, while their
finite-parameter approximants have linearly divergent relative-entropy work.

## 4. Exact diagonal-observer response

Measure `Z`, retaining only the outcome `+1` or `-1`.  Put

\[
 q_t=\Pr_t(Z=+1)=\frac{1+m(t)}2.
 \tag{NQP.14}
\]

Reflection gives `q_{-t}=1-q_t`.

### Theorem 4.1 — observation changes the response exponent

The classical Fisher response of the observed Bernoulli family is

\[
 \boxed{
 I_Z(t)=\frac{(q_t')^2}{q_t(1-q_t)}
       =\frac{I_Q(t)^2}{1-m(t)^2}.}
 \tag{NQP.15}
\]

It satisfies

\[
 \boxed{
 \lim_{t\to\infty}t^4I_Z(t)=b^2.}
 \tag{NQP.16}
\]

Thus diagonal observation changes the response tail from `t^-3` to `t^-4`.  Its Fisher tail
collapses faster: the full tail is asymptotic to a constant times `T^-1/2`, while the observed
tail is asymptotic to a constant times `T^-1`.

### Proof

Since `q_t' = m'(t)/2=I_Q(t)/2` and

\[
 q_t(1-q_t)=\frac{1-m(t)^2}{4},
\]

equation `(NQP.15)` follows.

To find the denominator asymptotic, write

\[
 1-m(t)
 =\left(1-\frac{t}{r_t}\right)
  +\frac{t}{r_t}(1-\tanh r_t).
 \tag{NQP.17}
\]

The rationalized first term is

\[
 1-\frac{t}{r_t}=\frac{b^2}{r_t(r_t+t)},
\]

so `t^2(1-t/r_t)->b^2/2`.  The second term in `(NQP.17)` is exponentially small.  Hence

\[
 t^2(1-m(t))\longrightarrow\frac{b^2}{2},
 \qquad
 t^2(1-m(t)^2)\longrightarrow b^2.
 \tag{NQP.18}
\]

Combine `(NQP.10)`, `(NQP.15)`, and `(NQP.18)` to obtain `(NQP.16)`.  The tail-length rates follow
by integrating the square-root asymptotics.  QED.

## 5. Linear complete work, logarithmic observed work

The observed reflected Jeffreys work is

\[
 J_Z(t)=J\bigl(\operatorname{Bern}(q_t),\operatorname{Bern}(1-q_t)\bigr).
\]

### Theorem 5.1 — exact work deficit

For every `t>0`,

\[
 \boxed{
 J_Z(t)=2m(t)\log\frac{1+m(t)}{1-m(t)}.}
 \tag{NQP.19}
\]

Its asymptotic growth is

\[
 \boxed{
 \lim_{t\to\infty}\frac{J_Z(t)}{\log t}=4,}
 \tag{NQP.20}
\]

whereas complete quantum work satisfies `(NQP.12)`.  Therefore the nonnegative data-processing
deficit

\[
 \Delta_Z(t)=J_Q(\rho_t,\rho_{-t})-J_Z(t)
\]

obeys

\[
 \boxed{
 \lim_{t\to\infty}\frac{\Delta_Z(t)}{4t}=1.}
 \tag{NQP.21}
\]

The diagonal observer sees unbounded work, but only logarithmically; asymptotically all linear
formation work is hidden in the noncommutative information fibre.

### Proof

For Bernoulli parameters `q` and `1-q`, one directed KL divergence is

\[
 (2q-1)\log\frac{q}{1-q}.
\]

Both orientations agree.  Substitute `2q_t-1=m(t)` to obtain `(NQP.19)`.

Equation `(NQP.18)` gives

\[
 1-m(t)\sim\frac{b^2}{2t^2},
 \qquad
 1+m(t)\longrightarrow2.
\]

Therefore

\[
 \log\frac{1+m(t)}{1-m(t)}
 =2\log t+O(1),
\]

and `m(t)->1`, proving `(NQP.20)`.  Subtract `(NQP.20)` from the linear asymptotic `(NQP.12)` to
obtain `(NQP.21)`.  Nonnegativity is quantum relative-entropy data processing under measurement.
QED.

## 6. Neutral ancillary recovery

Let `tau` be any fixed faithful ancillary density matrix and form

\[
 \widehat\rho_t=\rho_t\otimes\tau.
\]

Then

\[
 \boxed{
 D_Q(\widehat\rho_s\Vert\widehat\rho_t)
 =D_Q(\rho_s\Vert\rho_t),}
 \tag{NQP.22}
\]

because `log(rho tensor tau)=log rho tensor I + I tensor log tau` and `Tr tau=1`.  Conjugation by
`X tensor I` implements reflection.  Hence every response, length, work, and deficit theorem above
lifts through common tensor recovery without change.

## 7. Mechanism and new leverage

This realization is not a classical escort written with matrices:

1. source generators `Z` and `bX` do not commute;
2. finite-parameter states at distinct parameters do not commute;
3. transverse eigenvector rotation changes exponential classical response decay to the cubic law
   `(NQP.10)`;
4. a natural commutative observer loses one full power of local response and changes linear work to
   logarithmic work.

It supplies a second PRCM realization and a quantitative fourth-organ prediction:

> in a transverse noncommutative formation, classical diagonal observation can remain
> Fisher-compact and work-unbounded while still missing asymptotically all complete selection work.

Therefore neither compact positive geometry nor unbounded observed work certifies sufficiency.
The exact growth grade of work matters.

## 8. Hostile conjecture loops

1. **PRCM is a Bernoulli artifact.**  False by the noncommuting family `(NQP.1)`--`(NQP.3)`.
2. **Finite Fisher length forces exponential response decay.**  False: `I_Q(t)~b^2t^-3`.
3. **Any unbounded observer work retains the selection scale.**  False: observed work is logarithmic
   while complete work is linear.
4. **Positive measurement preserves the local response exponent.**  False: exponent `3` becomes
   `4`.
5. **Common ancillary formation repairs observation loss.**  False: it is information-neutral and
   preserves the deficit.
6. **This proves an RH selector.**  False: no arithmetic source map or uniform complete-work bound
   is constructed.

## 9. Literature boundary

The quantum ingredients are classical/current:

1. quantum relative-entropy Hessians and Kubo--Mori information are standard; Wilde,
   [Quantum Fisher information matrices from Rényi relative entropies](https://arxiv.org/abs/2510.02218),
   gives a current systematic treatment;
2. Kubo--Mori Fisher information and variance comparisons are treated by Tóth,
   [Lower bounds on the quantum Fisher information based on the variance and various types of entropies](https://arxiv.org/abs/1701.07461);
3. qubit Pauli functional calculus is standard.

No priority claim is made for those ingredients.  Corpus and broad arXiv search found no exact
coupling of cubic BKM tail, finite Fisher completion, linear quantum work, quartic measurement
response, logarithmic observed work, and asymptotically linear deficit.  Field significance is this
single-law comparison.

## 10. Gates

- [x] noncommutative reflection action
- [x] exact quantum relative-entropy fusion identity
- [x] cubic BKM-response asymptotic and finite length
- [x] linear complete work
- [x] quartic observed-response asymptotic
- [x] logarithmic observed work and linear deficit
- [x] neutral tensor-recovery lift
- [x] hostile literature/correctness audit
- [ ] Lean formalization
- [ ] literal arithmetic realization

## Log

- 2026-08-12 — dependency-closed paper proof completed as second structurally distinct realization
  of polarized response-completion mechanics.

