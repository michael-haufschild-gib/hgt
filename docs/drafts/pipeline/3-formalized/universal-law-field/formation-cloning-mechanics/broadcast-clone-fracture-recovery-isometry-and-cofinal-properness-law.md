# Broadcast--clone fracture, recovery isometry, and cofinal formation properness law

- **ID:** ULF-FCM-1
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT FORMATION LAW + GLOBAL PROPERNESS THEOREM
- **Source:** `../../../../1-in-progress/rh-current-frontier-map.md`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [FINITE MARKOV FORM]`
  `[SOURCE DIAGONAL VS INDEPENDENT FORMATION] [COMMON-RECOVERY INVARIANT]`
  `[FUNCTIONAL-EQUATION EQUIVARIANT] [COFINAL PROPERNESS] [SELECTION GATE]`
  `[LEAN FULLY FORMALIZED] [NO OPEN PAPER CLAUSE]`
- **Statement:** Deterministic source copying always broadcasts a probability packet, but one
  parameter-independent Markov formation can produce two independent copies of two packets only
  when those packets are identical or mutually singular.  Common recovery and functional-equation
  reflection preserve this obstruction exactly, and approximate cofinal cloning has a positive
  Hellinger error floor throughout the nonsingular nonneutral chamber.

## 1. The missing mechanism is an interchange law

The corpus repeatedly uses two operations which look like "copying" but are not the same law.

For a finite state space `X` and a probability packet `p`, the source diagonal is

\[
 \Delta_*p(x_1,x_2)=\mathbf 1_{x_1=x_2}p(x_1).
 \tag{FC.1}
\]

Both marginals equal `p`.  This is deterministic copying of one realized source value.  It produces
perfectly correlated replicas.

Independent packet formation is

\[
 (p\boxtimes p)(x_1,x_2)=p(x_1)p(x_2).
 \tag{FC.2}
\]

It uses fresh randomness.  Except for a Dirac packet, `(FC.1)` and `(FC.2)` are different.  The
field primitive is therefore not a new carrier but the **broadcast--clone interchange problem**:

\[
 \boxed{
 \text{source diagonal broadcast}
 \quad\Longrightarrow?\quad
 \text{independent observer formation}.}
 \tag{FC.3}
\]

The theorem below classifies when a single source operation can perform this interchange for more
than one possible law.  It also identifies a quantitative obstruction when exact interchange is
impossible.

## 2. Hellinger laws

For probability packets `p,q` on `X`, define affinity and root Hellinger distance by

\[
 A(p,q)=\sum_{x\in X}\sqrt{p(x)q(x)},
 \qquad
 h(p,q)=\sqrt{2-2A(p,q)}.
 \tag{FC.4}
\]

Then `0 <= A <= 1`, and

\[
 A(p,q)=1\iff p=q,
 \qquad
 A(p,q)=0\iff p\perp q.
 \tag{FC.5}
\]

For a Markov kernel `K:X -> Y`, Cauchy--Schwarz on every output fibre gives data processing

\[
 A(Kp,Kq)\ge A(p,q),
 \qquad h(Kp,Kq)\le h(p,q).
 \tag{FC.6}
\]

Independent products multiply affinity:

\[
 A(p^{\boxtimes d},q^{\boxtimes d})=A(p,q)^d.
 \tag{FC.7}
\]

### Proof

For one output `y`, apply Cauchy--Schwarz to

\[
 a_x=\sqrt{p(x)K(x,y)},\qquad b_x=\sqrt{q(x)K(x,y)}.
\]

This gives

\[
 \sqrt{(Kp)(y)(Kq)(y)}
 \ge\sum_x K(x,y)\sqrt{p(x)q(x)}.
\]

Sum in `y` and use `sum_y K(x,y)=1`; this is `(FC.6)`.  Equation `(FC.7)` is
Fubini's theorem applied to the product of the `d` square-root factors.  Equation `(FC.5)` follows
from equality in Cauchy--Schwarz for the unit vectors `sqrt p,sqrt q`, and from the fact that every
summand in `(FC.4)` is nonnegative.  QED.

## 3. Exact formation-cloning classification

Call a Markov kernel

\[
 C:X\longrightarrow X^d
\]

a common independent `d`-formation for `p,q` if

\[
 Cp=p^{\boxtimes d},\qquad Cq=q^{\boxtimes d}.
 \tag{FC.8}
\]

### Theorem 3.1 -- two-packet cloning rigidity

Let `d >= 2`.  A common independent `d`-formation for `p,q` exists if and only if

\[
 \boxed{p=q\quad\text{or}\quad p\perp q.}
 \tag{FC.9}
\]

Equivalently, one source operation can independently replicate two possible packets exactly if and
only if one observation either contains no distinction or identifies the packet with certainty.

### Proof

Assume `(FC.8)`.  Put `a=A(p,q)`.  Data processing and product multiplicativity give

\[
 a\le A(Cp,Cq)=A(p^{\boxtimes d},q^{\boxtimes d})=a^d.
 \tag{FC.10}
\]

For `0 <= a <= 1` and `d >= 2`, `(FC.10)` forces `a=0` or `a=1`.  Equation `(FC.5)` gives
`(FC.9)`.

Conversely, if `p=q`, ignore the input and prepare `p^{\boxtimes d}`.  If `p` and `q` are singular,
choose disjoint full-measure supports `P,Q`.  On `P`, prepare `p^{\boxtimes d}`; on `Q`, prepare
`q^{\boxtimes d}`; define the kernel arbitrarily off `P union Q`.  This one kernel satisfies
`(FC.8)`.  QED.

### Corollary 3.2 -- strict-interior no-formation law

If

\[
 0<A(p,q)<1,
 \tag{FC.11}
\]

then no common independent replication kernel exists.  This is stronger than a finite-information
argument: it also covers overlapping pairs with infinite directed relative entropy.

## 4. The source diagonal is broadcast, not clone

For every `p`, the diagonal kernel `x -> (x,x)` has both marginals equal to `p`.  It is therefore a
universal broadcaster.  It equals independent formation exactly for Dirac packets.

More quantitatively,

\[
 A(\Delta_*p,p^{\boxtimes d})
 =\sum_x p(x)^{(d+1)/2}
 =\exp\!\left(-\frac{d-1}{2}H_{(d+1)/2}(p)\right).
 \tag{FC.12}
\]

Thus the broadcast--clone gap is exactly a Renyi entropy of the packet.  The gap does not come from
a missing label, quotient, or completion.  It is the cost of replacing shared randomness by fresh
independent randomness.

## 5. Common recovery is information-neutral

Let `kappa(x,h)` be a parameter-independent Markov recovery kernel and retain the recovered base:

\[
 \widehat p(x,h)=p(x)\kappa(x,h),
 \qquad
 \widehat q(x,h)=q(x)\kappa(x,h).
 \tag{FC.13}
\]

Then

\[
 \boxed{A(\widehat p,\widehat q)=A(p,q),
 \qquad h(\widehat p,\widehat q)=h(p,q).}
 \tag{FC.14}
\]

Indeed,

\[
 \sum_{x,h}\sqrt{p(x)q(x)}\kappa(x,h)
 =\sum_x\sqrt{p(x)q(x)}.
\]

Consequently the three chambers in Theorem 3.1 -- identical, overlapping nonidentical, and
singular -- are invariant under every common recovery lift.  Adding latent history through a split
kernel cannot create independent formation and cannot hide its impossibility.

The existing packet-lift theorem proves the parallel KL statement, strict action composition, and
functional-equation involution in
`functional-equation-split-formation-lift-information-isometry-and-work-no-go.md`.  Equation
`(FC.14)` supplies the missing affinity form needed for clone classification.

## 6. Functional-equation equivariance

Let `R:X -> X` be an involutive bijection.  Coordinatewise action on products satisfies

\[
 R_*^{\boxtimes d}(p^{\boxtimes d})=(R_*p)^{\boxtimes d},
 \qquad
 R_*^{\boxtimes d}(\Delta_*p)=\Delta_*(R_*p),
 \tag{FC.15}
\]

and permutation of the summands in `(FC.4)` gives

\[
 A(R_*p,R_*q)=A(p,q).
 \tag{FC.16}
\]

Hence functional-equation reflection preserves both copy laws and their fracture.  Its lift through
common recovery remains information-neutral.  Reflection can exchange the two packets; it cannot
turn broadcast into independent formation.

## 7. Quantitative global formation properness

Exact cloning is not needed for a cofinal obstruction.  Let `C:X -> X^d` be any Markov kernel and
put

\[
 r=Cp,\qquad s=Cq,
\]

\[
 \varepsilon_p=h(r,p^{\boxtimes d}),
 \qquad
 \varepsilon_q=h(s,q^{\boxtimes d}).
 \tag{FC.17}
\]

### Theorem 7.1 -- unavoidable independent-formation defect

Writing `a=A(p,q)`, every attempted common formation satisfies

\[
 \boxed{
 \varepsilon_p+\varepsilon_q
 \ge \sqrt{2-2a^d}-\sqrt{2-2a}.}
 \tag{FC.18}
\]

The right-hand side is strictly positive exactly when `0<a<1` and `d>=2`.

### Proof

The Hellinger metric triangle inequality and data processing give

\[
\begin{aligned}
 h(p^{\boxtimes d},q^{\boxtimes d})
 &\le h(p^{\boxtimes d},r)+h(r,s)+h(s,q^{\boxtimes d})\\
 &\le \varepsilon_p+h(p,q)+\varepsilon_q.
\end{aligned}
\]

Use `(FC.4)` and `(FC.7)` and rearrange.  QED.

### Corollary 7.2 -- cofinal properness

Let `d_n -> infinity`.  If one has kernels `C_n:X -> X^{d_n}` with

\[
 h(C_np,p^{\boxtimes d_n})+h(C_nq,q^{\boxtimes d_n})\longrightarrow0,
 \tag{FC.19}
\]

then `p=q` or `p \perp q`.  Indeed, for `0<a<1`, the lower bound in `(FC.18)` tends to

\[
 \sqrt2-\sqrt{2-2a}>0.
 \tag{FC.20}
\]

This is a global formation/properness theorem: the overlapping nonneutral chamber is separated
from asymptotically exact independent replication by a uniform positive wall.  Equation `(FC.14)`
shows that the wall survives every common recovery completion unchanged.

## 8. Fusion law and fourth-organ prediction

The theorem closes one nontrivial four-organ exchange:

| Organ | Exact law |
|---|---|
| source execution | diagonal comultiplication gives universal correlated broadcast |
| packet formation | monoidal product asks for fresh independent replicas |
| recovery/sufficiency | common split recovery preserves affinity exactly |
| functional equation | involution is equivariant for both formations and preserves the gap |
| cofinal history | approximate independent replication has the positive properness wall `(FC.18)` |

The fourth-organ prediction is now exact.  Any closed/recurrent observer which appears to return
after producing arbitrarily many independent replicas of an overlapping reflected pair must do at
least one of the following:

1. retain an external randomness/history source not present in the returned packet;
2. pay the nonvanishing formation error `(FC.18)`;
3. drive the reflected packets into mutually singular sectors; or
4. reach the neutral fixed packet.

There is no fifth option inside Markov formation.  This explains why compact observed recurrence
can coexist with open lifted history: fresh independence cannot be recycled from one overlapping
packet by a lossless return map.

## 9. Selection corollary

Let `(p_a)_{a\in I}` be an identifiable reflected family with

\[
 R_*p_a=p_{-a},
 \qquad p_a=p_{-a}\iff a=0,
 \tag{FC.21}
\]

and suppose `p_a,p_{-a}` have common positive support.  If one source-produced Markov operation is a
common independent formation for `p_a,p_{-a}`, then

\[
 \boxed{a=0.}
 \tag{FC.22}
\]

Common support excludes singularity; Theorem 3.1 forces equality; identifiability gives `a=0`.

For an RH realization, `(FC.22)` is a genuine selector, but not yet an RH proof.  The remaining
arithmetic theorem is now sharply typed:

> Construct from the pre-zero source law an independence-producing comultiplication on the two
> reflected packets, or an asymptotically exact cofinal substitute.

The canonical source diagonal is insufficient: it broadcasts but does not clone.  This is stronger
than saying "find a source-native relation."  It specifies the missing operation, the exact
interchange law it must satisfy, the quantitative defect when it fails, and the only terminal
chambers.

## 10. Hostile boundaries

1. A parameter-dependent kernel can always ignore its input and prepare the requested product.
   One common kernel for both packets is load-bearing.
2. Broadcasting only requires correct marginals and is always possible classically.  Replacing
   independent formation by broadcasting destroys the theorem.
3. Singular packets are cloneable: one sample identifies the packet.  Therefore cloneability alone
   does not select the center without an independently proved common-support/equivalence law.
4. A source of fresh external randomness can form independent copies when the packet parameter is
   known.  The theorem says that one sample does not reveal an overlapping parameter exactly.
5. Common recovery must retain the base coordinate.  A lossy observer can increase affinity and may
   erase the obstruction.
6. Functional-equation equivariance is conservative.  It transports the fracture but does not
   generate the missing independent formation.
7. The theorem supplies no pre-zero arithmetic cloner.  Treating product formation as already
   source-generated would be circular.

## 11. Parent mathematics and corpus delta

Markov categories distinguish deterministic copy maps from independent tensor products; see
T. Fritz, *A synthetic approach to Markov kernels, conditional independence and theorems on
sufficient statistics*, Advances in Mathematics 370 (2020),
[arXiv:1908.07021](https://arxiv.org/abs/1908.07021).  Divergence-enriched Markov categories are
developed by P. Perrone, *Markov Categories and Entropy*,
[arXiv:2212.11719](https://arxiv.org/abs/2212.11719).  Generic probabilistic no-cloning and the
equivalence between cloneability and distinguishability are established by H. Barnum, J. Barrett,
M. Leifer, and A. Wilce, *Cloning and Broadcasting in Generic Probabilistic Theories*,
[arXiv:quant-ph/0611295](https://arxiv.org/abs/quant-ph/0611295).

The contribution here is the corpus-level fusion: exact finite Hellinger proof, split-recovery
isometry, functional-equation equivariance, quantitative cofinal properness, and the resulting
typed RH producer gate.  No claim is made that classical no-cloning itself is new.

## 12. Lean certificate

The full finite theorem surface is formalized in
`GaloisForLFunctions.HTGeometry.FormationCloneRigidityLaw` and
`GaloisForLFunctions.HTGeometry.FormationCloneRigidityCompletion`:

- Euclidean root-Hellinger metric, exact affinity formula, triangle inequality, and Markov data
  processing;
- arbitrary finite independent powers and exact affinity multiplicativity `(FC.7)`;
- exact clone-defect wall `(FC.18)`, its strict positivity, and cofinal properness `(FC.19)`;
- affinity endpoint classification `(FC.5)` and the full common-cloner existence iff theorem
  `(FC.9)`, including explicit preparation and singular-support kernels;
- diagonal broadcast, all coordinate marginals, equality with independent formation iff the
  packet is Dirac, and the exact Rényi fracture `(FC.12)`;
- exact affinity and root-Hellinger common-recovery isometries `(FC.14)`;
- packet, independent-power, diagonal, affinity, and Hellinger equivariance under every bijective
  reflection `(FC.15)--(FC.16)`;
- reflected-family selection both from nonsingularity and from the paper's literal common-positive
  support hypothesis `(FC.21)--(FC.22)`.

Direct source checks are clean and the final targeted build
`lake build GaloisForLFunctions.HTGeometry.FormationCloneRigidityCompletion` passes.  The module is
wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`.  Kernel axiom audits of all capstone
theorems report only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no declaration
uses `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `decide`, or `native_decide`.

## Log

- 2026-08-14 — Full Lean closure: arbitrary-depth product affinity, exact iff cloner construction, diagonal/Dirac/Renyi fracture, Hellinger defect and cofinal properness, split-recovery isometry, reflection equivariance, common-positive selector; targeted build and standard-only axiom audit pass.
