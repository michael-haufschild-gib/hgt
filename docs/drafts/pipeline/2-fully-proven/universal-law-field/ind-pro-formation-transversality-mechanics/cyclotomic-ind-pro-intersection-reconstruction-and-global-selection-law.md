# Cyclotomic ind--pro intersection, reconstruction, and global selection law

- **ID:** ULF-IPFTM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE FORMATION / HISTORY TRANSVERSALITY
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [SOURCE IND-SYSTEM] [PRO-HISTORY] [TRIVIAL INTERSECTION] [EXACT RECONSTRUCTION] [GLOBAL PROPERNESS] [RH-EQUIVALENT LANDING GATE] [NO LEAN IN THIS PASS]

## 1. Two variances of the same finite roots

Let

\[
 \mu_n=\{z\in\mathbb C^\times:z^n=1\}.
\]

For \(n\mid m\), define formation inclusion and history reduction by

\[
 i_{n,m}:\mu_n\hookrightarrow\mu_m,
 \qquad i_{n,m}(z)=z,
 \tag{IPT.1}
\]

\[
 r_{m,n}:\mu_m\longrightarrow\mu_n,
 \qquad r_{m,n}(z)=z^{m/n}.
 \tag{IPT.2}
\]

They satisfy strict composition in opposite directions.  The filtered formation source is
\(\mu_\infty=\bigcup_n\mu_n\).  A pro-history is a family

\[
 z=(z_n)_{n\ge1},
 \qquad z_n\in\mu_n,
 \qquad z_m^{m/n}=z_n\quad(n\mid m).
 \tag{IPT.3}
\]

## 2. Common realization

Call a pro-history **ind-formed** if there exist a birth depth \(d\) and a root
\(\xi\in\mu_d\) such that

\[
 z_m=i_{d,m}(\xi)=\xi
 \qquad\text{for every }d\mid m.
 \tag{IPT.4}
\]

This is exactly what it means for one element born in a filtered stage to represent the same
history on the cofinal tail of multiples of its birth depth.

### Theorem 2.1 — trivial ind--pro intersection

A pro-history is ind-formed if and only if

\[
 \boxed{z_n=1\quad\text{for every }n.}
 \tag{IPT.5}
\]

In fact, common realization at one birth depth and its double already forces the birth value to be
one.

### Proof

Suppose (IPT.4) holds.  Then

\[
 z_d=\xi,
 \qquad z_{2d}=\xi.
\]

Pro-coherence gives

\[
 z_d=r_{2d,d}(z_{2d})=z_{2d}^2,
\]

so \(\xi=\xi^2\).  Since \(\xi\) lies in a group, \(\xi=1\).

For arbitrary \(n\), let \(m=\operatorname{lcm}(n,d)\).  It is a multiple of \(d\), hence
\(z_m=1\).  Pro-coherence gives

\[
 z_n=z_m^{m/n}=1.
\]

The identity family plainly satisfies both variances. ∎

The theorem is not a cardinality argument.  It is an incompatibility of two composition laws:
inclusion preserves a formed element, while reduction raises it to the refinement degree.

## 3. Charge histories and reconstruction

For \(q\in\mathbb Z\), define

\[
 z_n(q)=e^{2\pi i q/n}.
 \tag{IPT.6}
\]

Then \(z(q)\) is a pro-history because

\[
 z_m(q)^{m/n}=z_n(q).
\]

### Corollary 3.1 — integral charge selection

The charge history \(z(q)\) is ind-formed if and only if \(q=0\).

### Proof

Theorem 2.1 gives \(z_n(q)=1\) for all \(n\).  Hence every positive integer divides \(q\), so
\(q=0\).  The converse is immediate. ∎

### Theorem 3.2 — joint reconstruction from either variance defect

The complete pro-history reconstructs \(q\): if \(z_n(q)=z_n(q')\) for every \(n\), then
\(q=q'\).  The complete inclusion-defect family also reconstructs \(q\).  In additive coordinates
\(C_n=\mathbb Z/n\mathbb Z\), the doubling defect is

\[
 \Delta_{n,2n}(q)=[-q]_{2n},
 \tag{IPT.7}
\]

and for \(n>|q|\) its centered representative is \(-q\).

### Proof

Equality of pro-histories says \(e^{2\pi i(q-q')/n}=1\) for every \(n\), so every \(n\) divides
\(q-q'\), forcing equality.  Formula (IPT.7) is ULF-DFPM-5; the centered representative proves
the second claim. ∎

Thus the intersection test is lossless: it selects zero without first quotienting away the charge.

## 4. Actual rational-Witt source formation

The corpus theorem `deninger-rational-witt-coherent-cyclotomic-descent` starts with independently
chosen finite cyclotomic embeddings and proves that their images inside one common complexified
rational-Witt presentation have unique injective, strictly composable transitions.  Its source is
the filtered union

\[
 \mathscr W_{p,\mathrm{fin}}
 =\varinjlim_{(n,p)=1}\mathbb C[C_n].
 \tag{IPT.8}
\]

On group-like basis elements, those transitions are precisely inclusion of the represented root
inside the common ambient root group, up to the already recorded finite cyclotomic coordinate
gauge.  Therefore every group-like element of (IPT.8) is born at finite depth and has a constant
ind-tail in the coordinate-free ambient-root sense used in (IPT.4).

For completeness, a group-like element of a finite complex group algebra is one basis group
element.  Write \(x=\sum_g a_g[g]\).  The equation
\(\Delta x=x\otimes x\) says \(a_ga_h=0\) for \(g\ne h\) and \(a_g^2=a_g\); over
\(\mathbb C\), every \(a_g\) is \(0\) or \(1\).  The counit equation
\(\varepsilon(x)=1\) leaves exactly one nonzero coefficient.  Hence no hidden linear combination
enters the group-like landing theorem.

### Corollary 4.1 — rational-Witt group-like landing no-go

No nonzero integral charge history can be represented by one group-like element of the finite-stage
rational-Witt cyclotomic source compatibly at every root depth.  The only common landing is the
unit group-like element.

This is a theorem about the already constructed source formation, not a proposed topology.

### Prime-to-\(p\) scope

At a fixed characteristic \(p\), (IPT.8) uses depths prime to \(p\).  The same proof survives.
If \(p\ne2\), use the doubling of a birth depth.  If \(p=2\), compare the multipliers \(3\) and
\(5\): common realization gives \(\xi^3=\xi=\xi^5\), hence \(\xi^2=1\); its order is odd, so
\(\xi=1\).  Cofinality of prime-to-\(p\) multiples then forces the whole prime-to-\(p\) history to
be trivial.

## 5. Operator-topological shadow

ULF-DFPM-4 and ULF-DFPM-5 attach regular Hilbert packets to the finite inclusion defects.  Their
Hilbert direct sum obeys

\[
 V_q-I\text{ compact}
 \Longleftrightarrow q=0,
 \qquad
 \|\pi(V_q)-1\|=2\quad(q\ne0).
 \tag{IPT.9}
\]

Hence:

\[
 \boxed{
 \text{common ind--pro realization}
 \Longleftrightarrow
 \text{zero crossed defect}
 \Longleftrightarrow
 \text{compact global regular formation}.}
 \tag{IPT.10}
\]

This is one mechanism with algebraic, reconstructive, and operator-topological shadows.

## 6. Functional equation and information neutrality

The functional-equation action of ULF-PFM-2 lifts through every common recovery kernel and
preserves KL information.  Holomorphic reflection transports local divisor order with
multiplicity, so it also transports the pro-history (IPT.6).  Therefore it preserves both sides of
the ind--pro fracture.

Information-neutrality is now classified exactly:

\[
 \text{functional equation}
 \quad\text{acts within the pro-history space, while}\quad
 \text{source formation asks for ind landing}.
\]

The functional equation cannot repair a failure of common realization.

## 7. Divisor and RH specialization

Let \(R\) be a meromorphic formation transfer and, on a small contour \(\Gamma\), put

\[
 q_\Gamma=\frac1{2\pi i}\int_\Gamma(-d\log R).
\]

### Corollary 7.1 — group-like source landing selection

If every local history

\[
 \bigl(e^{2\pi iq_\Gamma/n}\bigr)_n
\]

lands as one group-like ind-formed element of the rational-Witt cyclotomic source, then the divisor
of \(R\) vanishes.

For the Euler-shell transfer \(R_{m,r}\) on \(\Re s>1/2\), that source-landing statement implies RH.

### Proof

Corollary 4.1 forces every \(q_\Gamma=0\).  Small contour charges are local divisor orders, so the
divisor vanishes.  ULF-DFPM-1 identifies the strict-right divisor of \(R_{m,r}\) with the
nontrivial zeta-zero divisor, including multiplicity; functional-equation reflection yields RH. ∎

This is not an RH proof.  What remains is no longer “invent a root” or “choose a properness norm.”
It is one exact comparison:

> show that the literal Euler-shell formation holonomy is group-like in the already constructed
> rational-Witt filtered cyclotomic source.

The statement is potentially false; if so, its failure identifies the missing source completion
rather than another analytic endpoint.

## 8. Hostile boundaries

1. **Ind and pro limits of the same finite groups coincide.** False; Theorem 2.1 gives their
   sharp common-realization boundary.
2. **Every pro-history is born at finite depth.** False; nonzero charge histories are explicit
   counterexamples.
3. **Every root-stack section is ind-formed.** False; root stacks naturally retain pro-compatible
   ramified histories.
4. **A general rational-Witt vector is group-like.** False.  Group-like provenance is load-bearing;
   arbitrary linear combinations can hide root labels.
5. **Prime-to-\(p\) stages weaken selection.** False for group-like histories, by the argument in
   Section 4.
6. **Functional equation creates ind landing.** False.  It is a neutral symmetry of the pro data.
7. **The Euler-shell holonomy landing is already proved.** False.  Existing source theorems build
   the filtered cyclotomic carrier, not the comparison from formation divisor to one group-like
   carrier element.
8. **This is merely the statement that an integer divisible by all \(n\) is zero.** That is only
   Corollary 3.1.  The field theorem is the coordinate-free intersection (IPT.5), valid for every
   pro-history, plus its actual rational-Witt source realization and global properness shadow.

## 9. Parent mathematics and status

Ind/pro objects, cyclotomic groups, group algebras, and rational Witt vectors are established.
Christopher Deninger's rational-Witt source is the external parent; see *Rational Witt vectors and
associated sheaves*, arXiv:2508.05329.  The strict finite-stage source system used here is the
corpus theorem `deninger-rational-witt-coherent-cyclotomic-descent`.

The exact advance is a source-specific mechanism: filtered formation and inverse-limit history
have trivial group-like intersection, their mismatch is coefficient-faithful, and the regular
packet turns it into maximal Calkin noncompactness.  No external novelty claim is needed.

No Lean was written or built in this research pass.
