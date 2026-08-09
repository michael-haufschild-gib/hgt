# Irreducible \(n\)-ary law, proper-face invisibility, and unbounded interaction spectrum

- **Stage:** 2 — fully proved on paper
- **Status:** [PAPER-PROVED] [SPECULATIVE FIELD SURVIVOR]
  [OPERADIC LAW GENESIS] [ALL PROPER FACES ABELIAN]
  [UNBOUNDED INTERACTION SPECTRUM] [NOT RH] [NO LEAN]

## 1. Finite interaction law

Fix \(n\geq3\). Let \(V^{(n)}\) be the graded vector space with

\[
 V^{(n)}_0=\operatorname{span}\{x_1,\ldots,x_n\},
 \qquad
 V^{(n)}_{2-n}=kz,
\tag{IL.1}
\]

and no other components. Define an uncurved \(L_\infty\) structure by

\[
 \ell_n(x_1,\ldots,x_n)=z
\tag{IL.2}
\]

with graded antisymmetric extension, and set every other bracket to zero. Also set \(\ell_n=0\)
whenever one input is \(z\).

Each generator \(x_i\) is called a color. For \(S\subseteq\{1,\ldots,n\}\), the \(S\)-face is the
subspace spanned by \(z\) and the \(x_i\) with \(i\in S\), with the restricted brackets.

## 2. Theorem

### Theorem 2.1 — irreducible proper-face-invisible law

The operations above define a minimal \(L_\infty\) algebra. Every proper color-face
\(S\subsetneq\{1,\ldots,n\}\) is abelian, while the total \(L_\infty\) algebra is not homotopy
abelian.

Thus:

\[
 \boxed{
 \text{every proper observer face is law-trivial}
 \quad\centernot\Longrightarrow\quad
 \text{the total law is trivial}.}
\tag{IL.3}
\]

The first nonzero minimal operation has arity \(n\) and is exactly (IL.2). Its structured
conjugacy class is invariant under \(L_\infty\) equivalence.

### Corollary 2.2 — exact interaction order

Define the interaction order of a minimal law \(Q\) by

\[
 \iota(Q)=\inf\{r\geq2:\ell_r\neq0\}.
\tag{IL.4}
\]

Then

\[
 \iota(V^{(n)})=n.
\tag{IL.5}
\]

Every observer retaining fewer than \(n\) colors or truncating operations below arity \(n\)
reports an abelian law.

### Theorem 2.3 — unbounded interaction spectrum

Let

\[
 V_\infty=\prod_{n\geq3}V^{(n)}
\tag{IL.6}
\]

with the product filtration, and let \(Q_\infty\) be the product of the brackets (IL.2). Then:

1. \(Q_\infty^2=0\);
2. for every \(N\), the arity-\(N\) observer kills all interactions of orders \(n>N\);
3. the invisible tail contains
   \[
   \prod_{n>N}kz_n;
   \tag{IL.7}
   \]
4. over \(k=\mathbb R\), the product topology on the full interaction-output space
   \(\prod_{n\geq3}\mathbb Rz_n\) is not locally compact.

Hence unbounded interaction order supplies a noncompact source of observer escape that is distinct
from curvature, orbit density, and ordinary infinite-dimensional tangent rank.

## 3. Proof

The only potentially nonzero \(L_\infty\) identity is a composite in which one copy of
\(\ell_n\) is inserted into another. The inner operation outputs \(z\), while every operation with
a \(z\)-input was defined to vanish. Therefore every composite is zero and all \(L_\infty\)
identities hold. Since \(\ell_1=0\), the law is minimal.

A proper color-face omits at least one of the required inputs in (IL.2), so every restricted
bracket vanishes. On the total space, (IL.2) is nonzero. A minimal \(L_\infty\) algebra
quasi-isomorphic to an abelian one is isomorphic to the zero minimal structure; equivalently, an
invertible linear term conjugates the first nonzero minimal operation and cannot annihilate it.
Thus the total law is not homotopy abelian.

The product law squares to zero componentwise. Arity truncation at \(N\) removes every
\(\ell_n\) with \(n>N\), proving (IL.7). An infinite product of nonzero finite-dimensional real
vector spaces is not locally compact: every basic neighborhood leaves infinitely many unrestricted
coordinates and has no compact closure.

## 4. Contextuality versus interaction

The connected-parity contextual model and Theorem 2.1 have identical proper-face blindness but
opposite global ontologies:

- **contextuality:** no global deterministic law exists;
- **irreducible interaction:** a global law exists, but it is a genuinely higher operation.

Therefore proper-face blindness alone cannot decide whether the universal object is
nonclassical-without-points or higher-interacting-with-points. Any universal field must retain this
distinction.

## 5. Operadic interpretation

The law (IL.2) is an algebra over the \(L_\infty\) operad with one irreducible \(n\)-ary generator.
Equivalently, it is a Maurer--Cartan coderivation supported in arity \(n\). Its proper color
restrictions kill the twisting morphism, while the total color set retains it.

This makes law generation operadic:

- colors are observer types;
- the twisting morphism is the sourced interaction;
- proper-face formality is restriction of colors;
- unbounded arity is an infinite bar/cobar interaction tower.

## 6. Conjecture loops

1. **Pairwise or lower-face laws determine the total law — false.** Theorem 2.1 refutes this at
   every arity.
2. **A higher operation can be removed by nonlinear coordinates — false for the first nonzero
   minimal operation.**
3. **Proper-face blindness implies contextuality — false.** Here a global law exists.
4. **Unbounded interaction order is ordinary tangent dimension — false.** Each finite block can
   have finite tangent dimension; the new invariant is arity support.
5. **Unbounded interaction order equals differential hypertranscendence — open.** A comparison
   requires a source-native functor from differential prolongations to operadic arity.

## 7. Parent boundary

Minimal \(L_\infty\) algebras, coderivations, operadic deformation theory, and first-nonzero
operation invariance are established machinery. This theorem is an elementary native calibration.
Its field significance is the exact separation between contextual obstruction and irreducible
higher interaction, not a priority claim.

## 8. Sharp scope

1. The models are formal algebraic laws, not analytic dynamics.
2. Product nonlocal compactness uses the product topology and infinitely many nonzero blocks.
3. No cyclic pairing, positivity, recurrence, cost, or arithmetic realization is supplied.
4. A general law with many brackets need not decompose into independent blocks (IL.6).
5. No proof endpoint or RH statement is used.

