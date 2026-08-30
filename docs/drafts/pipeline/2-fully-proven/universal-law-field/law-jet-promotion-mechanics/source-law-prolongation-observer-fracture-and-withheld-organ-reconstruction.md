# Source-law prolongation, observer fracture, and withheld-organ reconstruction

- **ID:** ULF-LJPM-1
- **Stage:** 2 — fully proven on paper
- **Type:** MECHANISM THEOREM / CROSS-ORGAN RESPONSE LAW
- **Source:** constitutive process mathematics; obstruction--promotion mechanics; prime
  Boolean--Mass--Hankel--quantum fusion
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN-FORMALIZED] [PRE-RH] [NOT RH]`
  `[STATIC RESPONSE-SCHEME PIVOT REJECTED] [WITHHELD RESPONSE GENERATED]`

## 1. Pivot: a static response ideal is not the missing field

For source coordinates `z_i` in a commutative source algebra, the kernel of polynomial evaluation
records every algebraic law among the coordinates. This is useful bookkeeping, but by itself it is
not a mechanism: it stores relations already present and predicts nothing outside the chosen
coordinate list.

The surviving operation is **source-law prolongation**. A legal source deformation turns each
coordinate into a response jet. Every source law then generates a triangular tower of higher laws.
When one coordinate enters with invertible leading coefficient, the tower reconstructs every
withheld response of that coordinate from the other organs. Observation is applied only after this
generation step. A nonfaithful observer can create laws; a faithful observer reflects exactly the
source-generated tower.

The mechanism is therefore

\[
 \boxed{
 \text{source relation}
 \longrightarrow \text{Hasse--Schmidt prolongation}
 \longrightarrow \text{triangular response reconstruction}
 \longrightarrow \text{observer elimination}.}
 \tag{LJP.1}
\]

This is not a claim that every corpus route is algebraic or finite type. It is a law-generation
primitive that can be used inside algebraic, analytic, differential, operator, or completed source
charts.

## 2. Static laws and observer fracture

Let `R` and `S` be commutative rings, let `S` be an `R`-algebra, let `I` be an organ set, and let

\[
 z:I\longrightarrow S.
\]

Evaluation defines

\[
 \operatorname{ev}_z:R[X_i\mid i\in I]\longrightarrow S,
 \qquad X_i\longmapsto z_i.
\]

Define the source-law ideal

\[
 \mathcal L(z)=\ker(\operatorname{ev}_z).
 \tag{LJP.2}
\]

Let `phi:S -> T` be an `R`-algebra homomorphism, interpreted as an observer.

### Theorem 2.1 — observer fracture law

\[
 \boxed{\mathcal L(z)\subseteq\mathcal L(\phi z).}
 \tag{LJP.3}
\]

If `phi` is injective, equality holds. If `phi` is noninjective, strict inclusion can occur already
with one coordinate.

### Proof

For every polynomial `P`, functoriality of evaluation gives

\[
 \operatorname{ev}_{\phi z}(P)=\phi(\operatorname{ev}_z(P)).
\]

Hence a source law remains an observed law. If `phi` is injective, vanishing after `phi` implies
vanishing before it. Conversely, if `0 != x in ker phi`, take `I` to be a singleton, `z=x`, and
`P=X`. Then `P` is not a source law but is an observed law. QED.

Thus observer-level closure is logically weaker than source law. This is the algebraic core of the
source/receiver firewall: observers may add relations but cannot certify their source provenance
without faithfulness.

## 3. Hasse response law

Let `K` be a commutative field. A divided response jet is a sequence `a=(a_n)_(n>=0)`, viewed as
the coefficient sequence of a formal source deformation

\[
 A(t)=\sum_{n\ge0}a_nt^n.
\]

For jets `a,b`, define their Hasse product

\[
 (a\star b)_n=\sum_{j=0}^n a_jb_{n-j}.
 \tag{LJP.4}
\]

This is the coefficient law for multiplication of formal response series. Ordinary derivative jets
are obtained by rescaling `a_n=A^(n)(0)/n!` in characteristic zero.

### Theorem 3.1 — all-order withheld-organ reconstruction

Let `q,m,h : N -> K`, let `c in K`, and assume the prolonged fusion law

\[
 \boxed{(q\star m)_n=c h_n\quad\text{for every }n\ge0.}
 \tag{LJP.5}
\]

If `m_0 != 0`, then every response of the withheld `q` organ is forced recursively:

\[
 \boxed{
 q_n=\frac{c h_n-\sum_{j=0}^{n-1}q_jm_{n-j}}{m_0}.}
 \tag{LJP.6}
\]

Consequently two `q` jets satisfying `(LJP.5)` with the same `m,h,c` are equal. In particular,
the zeroth law and the first promoted law are

\[
 q_0m_0=ch_0,
 \qquad
 q_1m_0+q_0m_1=ch_1.
 \tag{LJP.7}
\]

### Proof

Split the final summand from `(LJP.4)`:

\[
 (q\star m)_n
 =\sum_{j=0}^{n-1}q_jm_{n-j}+q_nm_0.
\]

Substitute `(LJP.5)` and divide by `m_0`. This proves `(LJP.6)`. Strong induction proves
uniqueness: equality below order `n` makes the lower sums equal, and multiplication by nonzero
`m_0` is cancellative. The two displayed low-order laws are the cases `n=0,1`. QED.

### Corollary 3.2 — promotion commutes with faithful change of coefficients

Every ring homomorphism transports `(LJP.5)` coefficientwise. An injective homomorphism also
reflects it. A noninjective observer may therefore display a closed response tower whose source
tower is not closed.

### Proof

Ring homomorphisms preserve finite sums, products, constants, and zero. Reflection under an
injective map is immediate. QED.

This is the exact promotion law absent from a static response scheme: an order-zero relation births
new constraints at every deformation depth, and one organ becomes an out-of-sample prediction.

## 4. Second laboratory: passive split history

Let `a(t)` be a visible formation amplitude and `d(t)` its conservative hidden amplitude, with

\[
 a(t)^2+d(t)^2=1.
 \tag{LJP.8}
\]

Write their divided jets as `a_n,d_n`. Prolongation gives

\[
 \boxed{
 \sum_{j=0}^n a_ja_{n-j}+\sum_{j=0}^n d_jd_{n-j}
 =\begin{cases}1,&n=0,\\0,&n>0.\end{cases}}
 \tag{LJP.9}
\]

If `d_0 != 0` and the characteristic is not two, every hidden response `d_n` is recursively
determined by `a_0,...,a_n` and `d_0,...,d_(n-1)`. At first order,

\[
 \boxed{a_0a_1+d_0d_1=0,
 \qquad d_1=-\frac{a_0}{d_0}a_1.}
 \tag{LJP.10}
\]

### Proof

Equation `(LJP.9)` is the coefficient identity for `(LJP.8)`. For `n>0`, the two endpoint terms
in the hidden square are `d_0d_n+d_nd_0=2d_0d_n`; every other hidden term has order below `n`.
Division by `2d_0` gives the recursion. The case `n=1`, divided by two, is `(LJP.10)`. QED.

This laboratory is structurally different from the four-organ fusion below: the withheld organ is
the forced defect channel of a conservative dilation, not a quantum-information quotient. The same
promotion rule predicts it.

## 5. Boolean--Mass--Hankel--QFI response prediction

Fix a finite Boolean source law `mu`, an intervention score `r`, parity statistic `f`, and clock
statistic `g`. Let `Cov_e` be covariance under the normalized affine tilt

\[
 \mu_e(\omega)
 =\frac{\mu(\omega)(1+er(\omega))}
 {\sum_\eta\mu(\eta)(1+er(\eta))}.
\]

Put

\[
 A(e)=\operatorname{Cov}_e(f,f),\quad
 B(e)=\operatorname{Cov}_e(f,g),\quad
 M(e)=C(e)=\operatorname{Cov}_e(g,g),
\]

\[
 H(e)=A(e)C(e)-B(e)^2,
 \qquad
 Q(e)=4\pi^2\left(A(e)-\frac{B(e)^2}{C(e)}\right).
 \tag{LJP.11}
\]

At the Bernoulli prime-clock point these are exactly the certified Boolean incidence capacity,
Mass energy, first Hankel determinant, and transverse QFI organs. If `C(0) != 0`, continuity gives
`C(e) != 0` near zero, and hence

\[
 \boxed{Q(e)M(e)=4\pi^2H(e)}
 \tag{LJP.12}
\]

near zero.

For any observables `u,v`, the exact affine-tilt response theorem gives

\[
 \left.\frac d{de}\right|_0\operatorname{Cov}_e(u,v)
 =\operatorname{Cov}_\mu
 \left(r,(u-Eu)(v-Ev)\right).
 \tag{LJP.13}
\]

Let `Q_1,M_1,H_1` denote the derivatives at zero. Differentiating `(LJP.12)` yields the promised
withheld fourth-organ theorem.

### Theorem 5.1 — four-organ first-response conservation

\[
 \boxed{Q_1M_0+Q_0M_1=4\pi^2H_1.}
 \tag{LJP.14}
\]

Here

\[
 M_1=\operatorname{Cov}_\mu(r,(g-Eg)^2),
\]

\[
 H_1=A_1C_0+A_0C_1-2B_0B_1,
 \tag{LJP.15}
\]

and the previously certified QFI response is recovered, rather than assumed, by

\[
 \boxed{Q_1=\frac{4\pi^2H_1-Q_0M_1}{M_0}.}
 \tag{LJP.16}
\]

### Proof

The covariance derivatives are `(LJP.13)`. Product and square differentiation give `(LJP.15)`.
Since `C(0) != 0` and `C` is differentiable, it remains nonzero in a neighbourhood of zero, where
`(LJP.12)` is an algebraic identity. Differentiate it and use uniqueness of the derivative. Division
by `M_0=C(0)` gives `(LJP.16)`. QED.

The prediction is out of sample in the required sense: the QFI response is forced by incidence,
Mass, and Hankel responses. It was not used to define those three organs. Conversely, measuring QFI,
Mass, and one response predicts the other Hankel response. The all-order formal version is exactly
Theorem 3.1.

## 6. Field laws exposed

The theorem package supports a narrower and harder field interpretation than a response-scheme
metaphor.

1. **Laws generate laws.** A source relation is accepted only together with its least closure under
   legal source deformations.
2. **Promotion is triangular when a leading port is invertible.** This is the exact condition for
   withheld-organ prediction.
3. **Observation is lax.** Observer kernels can create apparent laws. Faithful observers alone
   reflect source closure.
4. **No-gos are promotion fractures.** A route wall may mean that prolongation does not descend,
   that its leading port becomes singular, or that its response tower is not globally admitted.
5. **Positive shadows are downstream.** QFI and Gram/Hankel quantities can be forced readings of
   one prolonged law while losing signs or word order.
6. **Hypertranscendence is not renamed noncompactness.** The defensible link is only that no finite
   differential presentation may carry the complete promotion tower.
7. **Recurrence is compatible with open promotion history.** A character or positive observer may
   close while the source deformation tower remains unbounded in depth.

## 7. Exact RH architecture produced by this theorem

This card does not prove RH. It changes the missing theorem from “find another receiver” to one
specific source-law construction.

Construct, before choosing any Xi zero, a coefficient-faithful Euler--Gamma source deformation with
four typed coordinates:

\[
 (\text{reflection-odd orientation},\ \text{incidence},\
   \text{singular admission mass},\ \text{completed source response}).
\]

The required source theorem must prove:

1. their relation ideal is stable under the legal source Hasse--Schmidt deformation;
2. one prolonged relation is triangular in the reflection-odd orientation coordinate;
3. its leading singular-admission port is nonzero and uniformly invertible in the source-generated
   completion;
4. the remaining three coordinates are globally admitted and the physical zero law annihilates
   their deciding combination;
5. the resulting orientation jet is coefficient-faithful and proper, so its vanishing forces the
   neutral displacement.

Then Theorem 3.1 reconstructs the full signed orientation tower, observer faithfulness prevents a
receiver-created false law, and the existing properness/selection receivers force the critical
line. The open burden is the literal source relation and its uniform leading port—not another
positivity reformulation of RH.

## 8. Hostile boundaries and falsifiers

1. A relation chosen after a zero is specified is not a source law.
2. A relation visible only after a noninjective observer is not admissible provenance.
3. If the leading coefficient vanishes or loses its uniform lower bound cofinally, triangular
   reconstruction does not yield selection.
4. Finite-order closure does not imply admission of the complete tower.
5. Polynomial/Hasse closure does not imply hypertranscendence or properness.
6. The mechanism fails as a field advance if its predicted QFI response disagrees with the
   independently certified tilt-response theorem.
7. It also fails if no second structurally different source law, such as passive split history,
   exhibits the same promotion/reconstruction law.

## 9. Parent mathematics and corpus delta

Polynomial relation ideals, Hasse--Schmidt derivations, jet schemes, differential elimination,
formal power series, and implicit statistical models are established mathematics. Relevant parents
include Vojta's Hasse--Schmidt construction of jet spaces, algebraic-statistical model invariants,
and differential elimination of dynamical invariants.

The corpus delta is the mechanism-level coupling:

\[
 \boxed{
 \text{source-proven organ fusion}
 \Longrightarrow
 \text{all-order promotion tower}
 \Longrightarrow
 \text{withheld-organ reconstruction}
 \Longrightarrow
 \text{observer-provenance test}.}
 \tag{LJP.17}
\]

Its first concrete prediction is `(LJP.14)--(LJP.16)` across Boolean incidence, Mass, Hankel, and
QFI; its second laboratory is the forced passive defect response `(LJP.9)--(LJP.10)`.

## Gates

- [x] generic source-law/observer-fracture theorem
- [x] all-order Hasse product promotion law
- [x] triangular withheld-organ reconstruction and uniqueness
- [x] second passive-history laboratory
- [x] exact four-organ first-response prediction on paper
- [x] unconditional Lean formalization
- [ ] literal Euler--Gamma prolonged relation with signed orientation as withheld coordinate
- [ ] coefficient-faithful singular admission and cofinal leading-port lower bound
- [ ] RH selection only after preceding gates

## Log

- 2026-08-30 — generic response-scheme proposal rejected as static repackaging after collision with
  source-response signatures, differential relation ideals, and the corpus anti-theatre rule.
- 2026-08-30 — promoted only the deformation-stable relation mechanism; proved all-order triangular
  reconstruction, passive-history prediction, and the Boolean--Mass--Hankel--QFI response law.
- 2026-08-30 — formalized the closed mechanism and both laboratories in
  `GaloisForLFunctions.HTGeometry.SourceLawJetPromotion`; direct elaboration and leaf build pass,
  and all audited theorems depend only on Lean/mathlib foundations.
