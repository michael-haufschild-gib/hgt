# Unbounded observer fibre, uniform reconstruction, and serial irreversibility law

- **ID:** ULF-DISTORTION-1
- **Stage:** 5-failed
- **Type:** FAILED THEOREM / POSITIVE SURVIVOR EXTRACTED
- **Source:** hysteretic-parallax pivot
- **Statement:** A metric observer admits uniformly accurate reconstruction only if every fibre has uniformly bounded radius; serial observation can never repair earlier fibre distortion.
- **Status:** [REJECTED BY LEAN-GUIDED COUNTEREXAMPLE] [SERIAL RADIUS CLAIM FALSE]
  [PAIRWISE-DIAMETER SURVIVOR LEAN-FORMALIZED]

## Failure notice

Equation (5) is false for the internal-centre radius (2).  On the three-point path
\(\{-1,0,1\}\), let the finer observer have fibres \(\{-1,1\}\) and \(\{0\}\), and let the
serially coarser observer merge them.  Every legal centre of the endpoint fibre has worst error
two, whereas the merged fibre may choose the new centre zero and has worst error one.  Thus serial
coarsening can decrease the proposed radius.

The closed counterexample and correct survivor are formalized in
`formal/GaloisForLFunctions/HTGeometry/ConstitutiveReconstructionNoGo.lean`.  What survives is:

- serial postprocessing preserves every previously indistinguishable source pair;
- pair distance is unchanged;
- any uniform \(C\)-reconstructor forces every hidden pair distance to be at most \(2C\).

The historical argument below is retained to show the rejected step.  It must not be cited as a
proved theorem.

## 1. Setup

Let \((X,d)\) be a metric space and let \(q:X\to Y\) be a surjection of sets. A section
\(s:Y\to X\) is a **uniform \(C\)-reconstructor** when

\[
q\circ s=\operatorname{id}_Y,
\qquad
d(x,s(qx))\le C
\quad\text{for every }x\in X.
\tag{1}
\]

For a nonempty subset \(F\subseteq X\), define its internal radius

\[
\operatorname{rad}_X(F)=\inf_{c\in F}\sup_{x\in F}d(x,c).
\tag{2}
\]

Define the reconstruction radius

\[
\mathfrak R(q)=\sup_{y\in Y}\operatorname{rad}_X(q^{-1}(y))in[0,\infty].
\tag{3}
\]

## 2. Exact reconstruction theorem

The infimum of all constants \(C\) for which a uniform \(C\)-reconstructor exists is
\(\mathfrak R(q)\). In particular:

1. if the fibre diameters are unbounded, then \(\mathfrak R(q)=\infty\) and no uniformly accurate
   reconstruction exists;
2. every uniform \(C\)-reconstructor forces

   \[
   \operatorname{diam}(q^{-1}(y))\le2C
   \quad\text{for every }y;
   \tag{4}
   \]

3. if \(r:Y\to Z\) is another surjection, then

   \[
   \mathfrak R(r\circ q)\ge\mathfrak R(q).
   \tag{5}
   \]

Thus later serial observation cannot repair an earlier loss of uniform reconstructibility.

### Proof

Given a section \(s\), its least reconstruction error is

\[
E(s)=\sup_{y\in Y}\sup_{x\in q^{-1}(y)}d(x,s(y)).
\]

For each \(y\), the point \(s(y)\) lies in \(q^{-1}(y)\), so
\(E(s)\ge\operatorname{rad}_X(q^{-1}(y))\). Taking the supremum gives
\(E(s)\ge\mathfrak R(q)\).

Conversely, for every \(\varepsilon>0\) and every \(y\), choose
\(c_y\in q^{-1}(y)\) whose maximal distance from that fibre is at most
\(\operatorname{rad}_X(q^{-1}(y))+\varepsilon\). The section \(s(y)=c_y\) then has
\(E(s)\le\mathfrak R(q)+\varepsilon\). Taking the infimum over sections and then
\(\varepsilon\downarrow0\) proves the equality.

If (1) holds and \(x,x'\) lie in one fibre, the triangle inequality gives

\[
d(x,x')\le d(x,s(qx))+d(s(qx'),x')\le2C,
\]

which proves (4). Finally, every \(q\)-fibre is contained in an \((r\circ q)\)-fibre. The radius of
the larger fibre is at least the radius of the smaller one after taking the supremum over all
\(q\)-fibres, which proves (5). QED.

## 3. Native examples

### 3.1 Finite recurrence with open lift

For \(q:\mathbb Z\to\mathbb Z/m\) with the word metric on \(\mathbb Z\), every fibre is an
arithmetic progression of infinite diameter. Hence \(\mathfrak R(q)=\infty\): a periodic observer
cannot uniformly reconstruct the open integer history.

### 3.2 Stable cancellation

For

\[
q:\mathbb N^2\to\mathbb Z,
\qquad
q(a,b)=a-b,
\]

with the \(\ell^1\) metric, the zero fibre contains \((n,n)\) at distance \(2n\) from \((0,0)\).
Thus stable signed defect has infinite reconstruction radius for positive ordered defect.

### 3.3 Logarithmic phase lift

For \(q:\mathbb R\to S^1\), \(q(t)=e^{it}\), with the Euclidean metric upstairs, every fibre is
\(t_0+2\pi\mathbb Z\) and has infinite diameter. Closed phase does not uniformly reconstruct the
logarithmic history.

### 3.4 Infinite hidden observer space

For a bounded projection \(P:H\to H_0\) from an infinite-dimensional Hilbert space with nonzero
kernel, every fibre is an affine copy of \(\ker P\) and has infinite diameter. No bounded-error
section reconstructs arbitrary hidden vectors from the projection.

## 4. Field consequence

The theorem identifies one coordinate-free meaning of “closed observer projection with open lifted
history”: the observer functor has infinite reconstruction radius. This is not curvature or
holonomy. It is coarse noninvertibility.

The quantity \(\mathfrak R\) is a first parallax invariant. Finer candidates include fibre growth,
lifting-energy profiles, persistent kernels, extension classes, and monodromy. These refinements must
be derived from the same enriched observer functor rather than stored independently.

## 5. Hostile scope

- The result depends on the source metric/coarse structure. Replacing an unbounded metric by a
  bounded equivalent topology destroys the conclusion.
- Infinite reconstruction radius detects quantitative loss, not extension or phase data inside a
  bounded fibre.
- A section may exist set-theoretically even when no uniform reconstructor exists.
- Coarse quotient and metric-fibration theory are established parent mathematics. The theorem is a
  bridge and field discriminator, not an external novelty claim.

## 6. External parents

- Zhang, `Coarse Quotient Mappings between Metric Spaces`, arXiv:1403.1934.
- Asao, `Magnitude and magnitude homology of filtered set enriched categories`, arXiv:2303.05677.

## Log

- 2026-08-09 — exact reconstruction-radius and serial irreversibility law recorded.
- 2026-08-09 — Lean-guided three-point counterexample rejected serial radius monotonicity; exact
  hidden-pair/diameter survivor formalized.
