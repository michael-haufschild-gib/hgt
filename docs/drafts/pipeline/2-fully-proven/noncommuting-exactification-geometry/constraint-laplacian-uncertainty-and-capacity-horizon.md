# Constraint Laplacian, exactification uncertainty, and the capacity horizon

- **ID:** `constraint-laplacian-uncertainty-and-capacity-horizon`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper proof)
- **Program:** `noncommuting-exactification-geometry`
- **Scientific status:** `[UNCONDITIONAL] [GENERAL FUNCTIONAL-ANALYTIC CORE]`
- **Scope:** finitely many closed linear constraint sectors in a Hilbert mediator, plus nested
  closed convex affine constraints
- **Novelty discipline:** Friedrichs angles, closed-range theory, two-projection normal forms, and
  weak compactness are classical. New payload is the exactification trichotomy, the separation of
  exchange curvature from precision, and their use as a typed representation law for the HGT
  obstruction families. No classical lemma is relabeled as a new theorem of functional analysis.

## 1. Problem

Suppose several exact mathematical representations of one source have different types: arithmetic,
spectral, geometric, functional, positive, or topological. To compare them, place their compatible
presentations in a common Hilbert mediator \(H\). Observer \(i\) accepts a closed linear subspace
\(U_i\subseteq H\). Let \(P_i\) be its orthogonal projector.

Three questions must be kept separate.

1. Does a jointly exact presentation exist?
2. If it does not, is approximate joint exactness uniformly forbidden or arbitrarily well
   approximable?
3. Does applying observer exactifications in opposite orders give the same result?

Ordinary commutators answer only the third question. The first two are controlled by a different
operator.

## 2. Constraint Laplacian

For closed subspaces \(U_1,\ldots,U_m\subseteq H\), define

\[
W=\bigcap_{i=1}^m U_i,
\qquad
T:H\longrightarrow\bigoplus_{i=1}^m U_i^\perp,
\qquad
Tx=(P_{U_i^\perp}x)_{i=1}^m,                                  \tag{2.1}
\]

and the **constraint Laplacian**

\[
\Delta=T^*T=\sum_{i=1}^m(I-P_i).                               \tag{2.2}
\]

Its quadratic form is the total precision defect

\[
\mathcal E(x)=\langle\Delta x,x\rangle
=\sum_{i=1}^m\operatorname{dist}(x,U_i)^2.                     \tag{2.3}
\]

The transverse uncertainty constant is

\[
\mu(U_1,\ldots,U_m)
=\inf_{\substack{x\perp W\\\|x\|=1}}\mathcal E(x).          \tag{2.4}
\]

## 3. Exactification trichotomy

### Theorem 3.1 — joint exactness, uniform uncertainty, and mirage

For the data above:

1. \(\ker\Delta=\ker T=W\).
2. The following are equivalent:
   - \(\mu(U_1,\ldots,U_m)>0\);
   - \(T\) is bounded below on \(W^\perp\);
   - \(\operatorname{ran}T\) is closed;
   - \(U_1^\perp+\cdots+U_m^\perp\) is closed.
3. If \(\mu=0\), there is a sequence \(x_n\in W^\perp\), \(\|x_n\|=1\), such that

   \[
   \sum_i\operatorname{dist}(x_n,U_i)^2\longrightarrow0.       \tag{3.1}
   \]

   Thus every observer becomes asymptotically sharp although no nonzero transverse vector is
   jointly exact.

#### Proof

From (2.3), \(\Delta x=0\) implies
\(0=\langle\Delta x,x\rangle=\sum_i\|P_{U_i^\perp}x\|^2\).
Hence \(x\in U_i\) for every \(i\), so \(x\in W\). The converse is immediate. This proves
part 1.

By definition,

\[
\|Tx\|^2=\mathcal E(x).
\]

Therefore \(\mu>0\) exactly when \(T\) is bounded below on
\((\ker T)^\perp=W^\perp\). The closed-range theorem for bounded operators between Hilbert
spaces says that this is equivalent to \(\operatorname{ran}T\) being closed, and also equivalent
to \(\operatorname{ran}T^*\) being closed. Directly from (2.1),

\[
T^*(y_1,\ldots,y_m)=\sum_i y_i,
\]

so \(\operatorname{ran}T^*=U_1^\perp+\cdots+U_m^\perp\). This proves part 2.

If \(\mu=0\), the definition of the infimum gives unit vectors \(x_n\in W^\perp\) with
\(\mathcal E(x_n)\to0\), which is (3.1). ∎

### The three regimes

The theorem gives a sharp trichotomy.

1. **Joint sector:** \(W\neq0\). Nonzero jointly exact presentations exist.
2. **Hard incompatibility:** after removing \(W\), \(\mu>0\). Every nonzero transverse
   presentation pays a uniform precision cost.
3. **Capacity horizon:** after removing \(W\), \(\mu=0\). No nonzero transverse joint
   presentation exists, but arbitrarily convincing approximate ones do. The failure is exactly a
   nonclosed range.

Regime 3 explains why every finite truncation can appear solvable while completion kills the exact
object. It is not logical inconsistency; it is loss of closed range.

## 4. Pairwise uncertainty and the Friedrichs angle

For two closed subspaces \(U,V\), put \(W=U\cap V\). Their Friedrichs cosine is

\[
c_F(U,V)
=\sup\left\{|\langle u,v\rangle|:
u\in U\ominus W,\ v\in V\ominus W,\ \|u\|=\|v\|=1\right\}.    \tag{4.1}
\]

### Theorem 4.1 — sharp pairwise precision law

For every \(x\in W^\perp\),

\[
\operatorname{dist}(x,U)^2+
\operatorname{dist}(x,V)^2
\geq (1-c_F(U,V))\|x\|^2.                                    \tag{4.2}
\]

The best constant in (4.2) is \(1-c_F(U,V)\). In particular,

\[
\mu(U,V)=1-c_F(U,V).                                           \tag{4.3}
\]

Moreover, if \(x\in U\ominus W\), then the literal one-sharp tradeoff is

\[
\operatorname{dist}(x,V)^2
\geq (1-c_F(U,V)^2)\|x\|^2.                                  \tag{4.4}
\]

Finally,

\[
c_F(U,V)<1
\quad\Longleftrightarrow\quad
U+V\text{ is closed}.                                         \tag{4.5}
\]

#### Proof

Let \(P,Q\) be the orthogonal projectors onto \(U,V\). Since \(x\perp W\), both
\(Px\in U\ominus W\) and \(Qx\in V\ominus W\). Put
\(a=Px\), \(b=Qx\), and \(c=c_F(U,V)\). Then

\[
|\langle a,b\rangle|\leq c\|a\|\|b\|.
\]

Writing \(s=\|a\|^2+\|b\|^2\), we have

\[
\|a+b\|^2
\leq s+2c\|a\|\|b\|
\leq(1+c)s.                                                    \tag{4.6}
\]

Also

\[
s=\langle a+b,x\rangle
\leq\|a+b\|\|x\|.
\]

Combining with (4.6) gives \(s\leq(1+c)\|x\|^2\). Therefore

\[
\begin{aligned}
\operatorname{dist}(x,U)^2+
\operatorname{dist}(x,V)^2
&=2\|x\|^2-\|Px\|^2-\|Qx\|^2\\
&\geq(1-c)\|x\|^2,
\end{aligned}
\]

proving (4.2).

The standard two-subspace norm identity

\[
\left\|(P+Q)|_{W^\perp}\right\|=1+c_F(U,V)                   \tag{4.7}
\]

follows from the preceding upper bound and the following matching lower bound. Choose unit
vectors \(u_n\in U\ominus W\), \(v_n\in V\ominus W\), and phases so that
\(r_n=\langle u_n,v_n\rangle\geq0\) and \(r_n\to c\). Put \(x_n=u_n+v_n\). Then

\[
\|x_n\|^2=2(1+r_n),
\qquad
\|P x_n\|\geq|\langle Px_n,u_n\rangle|=1+r_n,
\]

and likewise \(\|Qx_n\|\geq1+r_n\). Therefore the Rayleigh quotient satisfies

\[
\frac{\langle(P+Q)x_n,x_n\rangle}{\|x_n\|^2}
=\frac{\|Px_n\|^2+\|Qx_n\|^2}{\|x_n\|^2}
\geq1+r_n.
\]

Letting \(n\to\infty\) proves the lower bound `1+c`, hence (4.7). Since
\(\Delta=2I-P-Q\), (4.7) makes the lower bound optimal and proves (4.3).

If \(x\in U\ominus W\), then \(Qx\in V\ominus W\) and
\(\|Qx\|\leq c\|x\|\). Hence

\[
\operatorname{dist}(x,V)^2
=\|x\|^2-\|Qx\|^2
\geq(1-c^2)\|x\|^2,
\]

which is (4.4).

For (4.5), apply Theorem 3.1 to \(m=2\), use (4.3), and note that
\(U^\perp+V^\perp\) is closed if and only if \(U+V\) is closed. Equivalently, this is the
classical closed-sum characterization by the Friedrichs angle. ∎

## 5. Exchange curvature is not uncertainty

Define the pairwise **exchange curvature**

\[
\Omega_{ij}=[P_i,P_j]=P_iP_j-P_jP_i.                           \tag{5.1}
\]

It measures order dependence of sequential exactification. It does not determine joint exactness
or the precision gap.

### Proposition 5.1 — independence of incidence and exchange curvature

All four combinations occur, even in finite dimension:

1. \(\Omega=0\) and \(U\cap V\neq0\): take \(U=V\neq0\).
2. \(\Omega=0\) and \(U\cap V=0\): take nonzero orthogonal subspaces.
3. \(\Omega\neq0\) and \(U\cap V=0\): take two nonorthogonal distinct lines in
   \(\mathbb R^2\).
4. \(\Omega\neq0\) and \(U\cap V\neq0\): in \(\mathbb R^3\), take
   \(U=\operatorname{span}(e_1,e_2)\) and
   \(V=\operatorname{span}(e_1,\cos\theta e_2+\sin\theta e_3)\) with
   \(0<\theta<\pi/2\).

#### Proof

The first two pairs have commuting orthogonal projections. Distinct nonorthogonal lines have
noncommuting projections and trivial intersection. In the fourth example, the common line is
\(\mathbb R e_1\); on \(\operatorname{span}(e_2,e_3)\) the projections reduce to the
third example and therefore do not commute. ∎

### Proposition 5.2 — equal curvature norm, unequal uncertainty

For any \(0<\theta<\pi/2\), let \(U=\mathbb R e_1\) and
\(V_\theta=\mathbb R(\cos\theta,\sin\theta)\). Then

\[
\|[P_U,P_{V_\theta}]\|=\sin\theta\cos\theta,                  \tag{5.2}
\]

while

\[
\mu(U,V_\theta)=1-\cos\theta.                                 \tag{5.3}
\]

The angles \(\theta\) and \(\pi/2-\theta\) have equal commutator norms but, unless
\(\theta=\pi/4\), different uncertainty constants.

#### Proof

In the standard basis,

\[
P_U=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
P_{V_\theta}=\begin{pmatrix}
\cos^2\theta&\sin\theta\cos\theta\\
\sin\theta\cos\theta&\sin^2\theta
\end{pmatrix}.
\]

Their commutator has off-diagonal entries
\(\pm\sin\theta\cos\theta\), proving (5.2). Their Friedrichs cosine is
\(\cos\theta\), so (5.3) follows from Theorem 4.1. Replacing \(\theta\) by
\(\pi/2-\theta\) leaves (5.2) unchanged and replaces the gap by
\(1-\sin\theta\). ∎

### Consequence

The Heisenberg analogy must be stated carefully. Noncommutativity is neither necessary nor
sufficient for lack of a joint exact sector, and its norm does not determine the precision gap.
Any general exactification geometry needs at least two tensors:

1. the constraint Laplacian \(\Delta\), controlling incidence, uncertainty, and closure;
2. the exchange curvature \(\Omega_{ij}\), controlling route order.

## 6. One angle operator casts several pairwise shadows

The classical two-projection normal form explains why apparently unrelated no-gos often occur
together. On the generic part of a pair of closed subspaces, there is a Hilbert space \(K\) and a
positive contraction \(0<C<I\), with
\(S=(I-C^2)^{1/2}\), such that

\[
P=\begin{pmatrix}I&0\\0&0\end{pmatrix},\qquad
Q=\begin{pmatrix}C^2&CS\\CS&S^2\end{pmatrix}.                 \tag{6.1}
\]

Then

\[
[P,Q]=\begin{pmatrix}0&CS\\-CS&0\end{pmatrix},               \tag{6.2}
\]

and the two spectral branches of \(\Delta=2I-P-Q\) are

\[
1-C,\qquad 1+C.                                                 \tag{6.3}
\]

Thus the single angle operator \(C\), together with the four incidence summands
\(U\cap V\), \(U\cap V^\perp\), \(U^\perp\cap V\), and
\(U^\perp\cap V^\perp\), determines:

- joint exactness;
- the uncertainty spectrum;
- exchange curvature;
- closedness of the sum;
- convergence rate of alternating exactification.

The commutator sees only \(CS\) and loses information because
\(C\) and \((I-C^2)^{1/2}\) give the same product. The full angle operator is therefore the
minimal pairwise representation object, not the scalar commutator.

## 7. Affine capacity horizon

Linear uncertainty does not cover the second major failure mode: every finite collection of
inhomogeneous constraints may have an exact solution while the full infinite collection has none.

### Theorem 7.1 — nested convex capacity criterion

Let

\[
C_1\supseteq C_2\supseteq\cdots
\]

be nonempty closed convex subsets of a Hilbert space \(H\). Then

\[
\bigcap_{n\geq1}C_n\neq\varnothing
\quad\Longleftrightarrow\quad
\sup_n\operatorname{dist}(0,C_n)<\infty.                      \tag{7.1}
\]

#### Proof

If \(x\in\bigcap_n C_n\), then
\(\operatorname{dist}(0,C_n)\leq\|x\|\) for every \(n\).

Conversely, suppose the supremum in (7.1) is at most \(R\). Every nonempty closed convex
subset of a Hilbert space has a unique nearest point to zero, so each
\(C_n\cap\overline B_R\) is nonempty. It is convex and norm closed, hence weakly closed.
The closed ball \(\overline B_R\) is weakly compact. The sets
\(C_n\cap\overline B_R\) are nested nonempty weakly closed subsets of a compact space, so
their intersection is nonempty. ∎

### Example 7.2 — perfect finite consistency with no global point

In \(\ell^2(\mathbb N)\), define

\[
C_n=\left\{x:x_k=\frac1{\sqrt{k}}\text{ for }1\leq k\leq n\right\}.
\]

Each \(C_n\) is a nonempty closed affine subspace, and the family is nested. But

\[
\operatorname{dist}(0,C_n)^2=\sum_{k=1}^n\frac1k\longrightarrow\infty.
\]

Therefore the full intersection is empty although every finite constraint problem is exactly
solvable. The missing global object escapes every bounded-capacity region.

### Meaning

Finite consistency is not enough. One also needs a uniform capacity bound. This is the affine
counterpart of the linear closed-range condition. It precisely separates a genuine inverse-limit
object from a sequence of finite shadows whose norm, energy, mass, or source cost diverges.

## 8. Corpus interpretation atlas

This section is an interpretation, not an assertion that every corpus card has already been placed
inside one canonical Hilbert mediator.

| Corpus phenomenon | Exactification-geometric shadow | Required datum not to forget |
|---|---|---|
| finite modal truncations invertible, limiting range dense nonclosed | \(\mu=0\), trivial transverse kernel, nonclosed normal range | closure versus literal range |
| dense proper source radical | capacity-horizon regime | source topology and provenance |
| positive finite cutoffs with divergent total mass | affine sets \(C_n\) with unbounded distance/capacity | uniform mass bound |
| positivity plus raw Stokes forces boundary zero | hard joint exactness collapse | cochain form before quotient |
| opposite orientations share the same completed ring | commuting or identical scalar shadow with distinct incidence/orientation flags | bipolar provenance |
| source image differs from reflected radical | same cycle condition, different boundary subspace | full flag \(B\subseteq Z\) |
| finite differential data misses HT | no finite-stage constraint Laplacian can classify the tail | infinite pro-jet base |

The table gives testable obligations. For each route, a later card must construct the mediator,
identify its \(U_i\), and compute or bound \(\mu\). Merely placing a no-go in a row earns no
theorem credit.

## 9. Hostile review

### Attack A — generic noncommutativity has been renamed curvature

No. Proposition 5.1 proves that curvature and joint exactness are independent. The theory keeps
both and refuses the claim that coupling implies noncommutativity.

### Attack B — every incompatibility gets a positive uncertainty bound

False. Theorem 3.1 has a separate \(\mu=0\) regime. Nonclosed range permits arbitrarily sharp
approximate joint presentations without a true one.

### Attack C — finite consistency implies a limit by compactness

Only with bounded capacity. Example 7.2 shows exact finite consistency and empty inverse limit.
Theorem 7.1 identifies the missing hypothesis exactly.

### Attack D — the Hilbert mediator is canonical

Not yet. This theorem is conditional on a source-defined mediator and closed observer sectors.
Constructing that mediator for heterogeneous arithmetic, spectral, and geometric observers is the
main open representability problem. Inserting one ad hoc would be theatre.

### Attack E — this is already RH leverage

No. The theorem explains and classifies obstruction shapes. RH leverage requires a source-native
mediator in which one live RH obstruction acquires a computable nonzero gap, a controlled
capacity horizon, or a new joint kernel. That remains open.

## 10. Novelty and significance verdict

- **Classical mathematical core:** closed-range theorem, Friedrichs angle, two-projection normal
  form, weak compactness of Hilbert balls.
- **New representation law:** exactification problems require a constraint Laplacian and exchange
  curvature as independent tensors; their joint state separates exactness, hard uncertainty,
  nonclosed-range mirage, and order holonomy.
- **New positive survivor from prior no-gos:** finite consistency fails precisely by capacity escape
  in nested closed convex Hilbert constraints; finite approximation alone is not evidence for a
  global object.
- **Significance ceiling:** high explanatory value and a concrete calculation protocol; no claim
  yet of solving an RH route or constructing the universal heterogeneous mediator.

## 11. Lean return notes

Do not write Lean in this phase. Likely later decomposition:

1. finite-family positive-semidefinite operator and kernel-of-sum theorem;
2. closed-range equivalences, probably requiring existing Hilbert-space operator library;
3. two-dimensional line calculations for independence counterexamples;
4. nested weakly compact intersection theorem;
5. \(\ell^2\) harmonic-capacity example.

Search existing formal files for orthogonal projections, closed ranges, Friedrichs angles, weak
compactness, and \(\ell^2\) before selecting edit targets. No path is asserted here.
