# Mutational visible recurrence, open lineage, and conserved linearization law

- **ID:** ULF-SEGM-1
- **Stage:** 2-fully-proven
- **Type:** MECHANISM THEOREM / STRUCTURED-ENDOGENEITY CALIBRATION
- **Statement:** One fixed local mutation law has a period-two visible compatibility rulebook and
  an unbounded positive semantic lineage; a transported invariant forces exact linearization and
  makes every future response predictable.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [CLASSICAL CLUSTER INGREDIENTS] [LEAN-CERTIFIED] [NOT RH]

## 1. Certified boundary addressed

Fixed exact rule--test polarity has no open genesis: serial revision is idempotent and synchronous
revision is eventually period two. Arbitrary state-indexed compatibility has the opposite defect:
it realizes every transition system and predicts nothing.

This theorem constructs a strict middle mechanism. Compatibility changes by one fixed local
mutation rule. The observed rulebook is recurrent, but a transported semantic certificate forces
an open and predictable lineage.

## 2. Source law

Let \((x_n)_{n\geq0}\) be the positive sequence beginning

\[
  x_0=x_1=1
  \tag{MG.1}
\]

and obeying the rank-two exchange law

\[
  \boxed{x_{n+2}x_n=x_{n+1}^2+1.}
  \tag{MG.2}
\]

Equivalently,

\[
  x_{n+2}=\frac{x_{n+1}^2+1}{x_n}.
  \tag{MG.3}
\]

The visible rank-two compatibility orientation changes sign at every mutation:

\[
  B_{n+1}=-B_n.
  \tag{MG.4}
\]

Hence \(B_{n+2}=B_n\).

## 3. Transported certificate

For positive \(a,b\), define

\[
  H(a,b)=\frac{a^2+b^2+1}{ab}.
  \tag{MG.5}
\]

### Theorem 3.1 -- exchange transports the certificate

If \(a,b,c>0\) and

\[
  ac=b^2+1,
  \tag{MG.6}
\]

then

\[
  \boxed{H(a,b)=\frac{a+c}{b}=H(b,c).}
  \tag{MG.7}
\]

#### Proof

Using \(b^2+1=ac\),

\[
 H(a,b)
 =\frac{a^2+ac}{ab}
 =\frac{a+c}{b}.
\]

The same identity gives

\[
 H(b,c)
 =\frac{ac+c^2}{bc}
 =\frac{a+c}{b}.
\]

Thus the certificate is transported exactly through mutation. QED.

### Corollary 3.2 -- forced linearization

For the initial pair `(MG.1)`,

\[
  H(x_0,x_1)=3.
  \tag{MG.8}
\]

Theorem 3.1 propagates this value to every adjacent pair. Therefore

\[
  \frac{x_n+x_{n+2}}{x_{n+1}}=3
\]

and

\[
  \boxed{x_{n+2}=3x_{n+1}-x_n.}
  \tag{MG.9}

No future transition coefficient was supplied. The nonlinear local exchange and its transported
certificate predict one constant-coefficient linear recurrence.

## 4. Converse reconstruction

### Theorem 4.1 -- the linear recurrence reconstructs mutation

Let `(x_n)` satisfy `(MG.1)` and `(MG.9)`. Then for every \(n\geq0\),

\[
  \boxed{x_{n+2}x_n-x_{n+1}^2=1.}
  \tag{MG.10}
\]

Hence the linearized process reconstructs the nonlinear exchange `(MG.2)` exactly.

#### Proof

Set

\[
  Q_n=x_{n+2}x_n-x_{n+1}^2.
\]

From \(x_2=3x_1-x_0=2\),

\[
  Q_0=2\cdot1-1=1.
\]

Write \(a=x_n\), \(b=x_{n+1}\), and \(c=x_{n+2}=3b-a\). One more recurrence step is
\(x_{n+3}=3c-b\). Therefore

\[
\begin{aligned}
 Q_{n+1}
 &= (3c-b)b-c^2\\
 &=3bc-b^2-c^2\\
 &=3ab-a^2-b^2\\
 &=(3b-a)a-b^2\\
 &=Q_n,
\end{aligned}
\]

where the middle equality follows by substituting \(c=3b-a\). Induction gives \(Q_n=1\).
QED.

Theorems 3.1 and 4.1 give a two-way mechanism law:

\[
  \text{nonlinear exchange + initial certificate}
  \quad\Longleftrightarrow\quad
  \text{linear recurrence + Cassini invariant}.
  \tag{MG.11}
\]

## 5. Positive open lineage

### Theorem 5.1 -- recurrent rulebook, open semantics

The sequence `(MG.1)--(MG.2)` satisfies

\[
  x_2=2,
  \qquad
  0<x_n<x_{n+1}quad(n\geq1),
  \tag{MG.12}
\]

and more strongly

\[
  \boxed{x_{n+2}>2x_{n+1}\quad(n\geq1).}
  \tag{MG.13}

Consequently `(x_n)` is unbounded and never eventually periodic, while `(B_n)` has exact period
two.

#### Proof

The first mutation gives \(x_2=2\). Suppose \(0<a<b\) for two consecutive values. By `(MG.9)`,

\[
  c=3b-a>2b>0.
\]

Thus \(0<b<c\), and induction proves `(MG.12)--(MG.13)`. Iterating `(MG.13)` makes the
lineage unbounded. A strictly increasing tail cannot be eventually periodic. Equation `(MG.4)`
gives \(B_{n+2}=B_n\). QED.

## 6. Exact mechanism conclusion

This system lies strictly between the two certified vacuity boundaries.

1. It is not fixed-polarity revision: mutation changes the compatibility orientation.
2. It is not arbitrary endogenous compatibility: one exchange polynomial and one initial pair
   determine the full future.
3. Its observer can be recurrent while its semantic law history is open.
4. The open coordinate is not an appended counter. It is a positive response constrained by the
   exchange equation and a transported invariant.
5. The conserved certificate converts local nonlinear repair into a withheld global prediction.

This suggests one new field law.

> **Certificate-bearing mutation law.** A structured endogenous revision is predictive when a
> source-fixed local exchange transports a certificate that, together with the recurrent
> rulebook, determines the next semantic response.

The certificate is neither the endpoint nor an arbitrary metric. It is the conserved information
that prevents endogenous compatibility from becoming a universal transition oracle.

## 7. Sharp finite/open bifurcation

Replacing the square in `(MG.2)` by the first power gives

\[
  x_{n+2}x_n=x_{n+1}+1.
  \tag{MG.14}
\]

From `(1,1)` the ordered pairs follow

\[
 (1,1)\to(1,2)\to(2,3)\to(3,2)\to(2,1)\to(1,1).
 \tag{MG.15}
\]

Thus a local change in interaction exponent separates finite semantic recurrence from open
lineage even though the visible compatibility orientation is period two in both cases. This is the
smallest genesis-phase calibration; it is not needed for the proof of Theorems 3.1--5.1.

## 8. Hostile no-go loops

1. **Compatibility recurrence forces semantic termination -- false.** Equations `(MG.4)` and
   `(MG.13)` give the counterexample.
2. **Any changing compatibility is non-predictive -- false.** The transported certificate forces
   `(MG.9)`.
3. **Open lineage requires arbitrary vocabulary injection -- false.** Each successor is generated
   by the same local exchange.
4. **Positivity selects the lineage by itself -- false.** Positivity supplies admission; `(MG.2)`
   and `(MG.7)` supply selection.
5. **Endpoint rulebook plus compatibility period determines growth -- false.** Exponents one and
   two have the same period-two orientation but finite and open semantic phases.
6. **This establishes the universal field -- false.** It is one exact structured-endogeneity
   calibration. General certificate classification and a second non-cluster realization remain
   open.

## 9. Parent boundary

Rank-two cluster mutation, the Laurent phenomenon, affine cluster recurrences, frieze
linearization, and mutation invariants are established mathematics. Primary parents include:

- Fomin--Zelevinsky, *Cluster algebras I: Foundations*, arXiv:math/0104151;
- Musiker--Propp, *Combinatorial interpretations for rank-two cluster algebras of affine type*,
  arXiv:math/0602408;
- Reutenauer, *Linearly recursive sequences and Dynkin diagrams*, arXiv:1204.5145;
- Nobe, *Generators of rank 2 cluster algebras of affine types via linearization of seed
  mutations*, arXiv:1808.08125;
- Chen--Li, *Mutation invariants of cluster algebras of rank 2*, arXiv:2401.09704.

No novelty is claimed for the recurrence or invariant. The field-level delta is the exact placement
of this classical mechanism between fixed-polarity collapse and arbitrary endogenous vacuity, with
the transported certificate identified as the predictive resource.

## 10. Scope and next theorem

1. The theorem is rank two and affine.
2. No general cluster Laurent-positivity theorem is reproved.
3. No topology, HT, physical clock, action, arithmetic source, or RH endpoint is used.
4. Visible recurrence depends on forgetting the semantic seed; the full seed does not recur.
5. The next mechanism theorem must characterize certificate-bearing mutations independently of
   cluster coordinates and prove termination/open-lineage alternatives under a resource law.

## Lean certification

Module:
`GaloisForLFunctions.HTGeometry.ConstitutiveMutationalGenesis`.

Lean certifies over `ℤ`, without division:

1. the linear recurrence from initial values `1,1`;
2. Cassini invariant `(MG.10)`;
3. the algebraic certificate
   \[
     x_n^2+x_{n+1}^2+1=3x_nx_{n+1};
   \]
4. strict positive growth after the first step;
5. exact period two of the visible sign rulebook;
6. a local cancellation theorem showing that exchange plus the certificate forces
   `c=3*b-a` whenever `a≠0`.

It also certifies explicit threshold escape, absence of every positive semantic period, sign
reversal, exact visible period two, and one bundled mechanism capstone. Direct foreground
elaboration passes. The formal lint gate passes. The dedicated Universal Law Field umbrella build
passes all `11,433` jobs. Axiom audit of every load-bearing declaration reports only `propext`,
`Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, `admit`, `opaque`, or `unsafe`
declaration is used.

## Log

- 2026-08-10 -- dependency-closed paper proof completed after corpus collision killed an earlier
  attenuated-commutator proposal as regression.
- 2026-08-10 -- exact exchange, certificate, linearization, growth, nonperiodicity, and visible
  recurrence formalized and wired into the Universal Law Field umbrella.
