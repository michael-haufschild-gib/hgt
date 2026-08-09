# Natural power intervention, inverse-depth normalization, and no-selection law

- **ID:** ULF-NPG-PIN-1
- **Stage:** 3 — formalized in Lean 4
- **Type:** universal-law-field theorem / source-intervention classification
- **Status:** [LEAN-CERTIFIED] [ROUTE-INDEPENDENT]
  [SOURCE-NATURAL CLASSIFICATION] [RADIAL NO-SELECTION] [NOT RH]

## 1. Free commutative source

For a set \(X\), let

\[
\mathsf M(X)=\mathbb N^{(X)}
\]

be the free commutative monoid of finite multisets on \(X\). Every map \(f:X\to Y\) induces the
pushforward monoid homomorphism \(f_*:\mathsf M(X)\to\mathsf M(Y)\).

A **source-natural intervention** is a family of monoid endomorphisms

\[
\Phi_X:\mathsf M(X)\longrightarrow\mathsf M(X)
\]

such that

\[
f_*\Phi_X=\Phi_Yf_*
\tag{1}
\]

for every map \(f:X\to Y\).

## 2. Classification theorem

### Theorem 2.1 — natural interventions are uniform powers

There is a unique \(r\in\mathbb N\) such that, for every set \(X\) and every finite multiset
\(u\in\mathsf M(X)\),

\[
\boxed{\Phi_X(u)=r u.}
\tag{2}
\]

Conversely, every \(r\in\mathbb N\) defines such a natural intervention. Composition corresponds
to multiplication of the integers.

In multiplicative prime notation, \((2)\) is exactly

\[
\boxed{P_r(n)=n^r.}
\tag{3}
\]

#### Proof

Evaluate \(\Phi\) on the singleton set \(1=\{*\}\), and let

\[
r=\left|\Phi_1([*])\right|.
\]

The free commutative monoid on one generator is \(\mathbb N\), so
\(\Phi_1([*])=r[*]\). For \(x\in X\), apply naturality to the map
\(i_x:1\to X\), \(*\mapsto x\):

\[
\Phi_X([x])
=\Phi_X(i_{x*}[*])
=i_{x*}\Phi_1([*])
=r[x].
\]

Every multiset is a finite sum of singleton multisets, and \(\Phi_X\) is a monoid homomorphism.
Therefore \(\Phi_X(u)=ru\). Evaluation on one singleton proves uniqueness. Scalar multiplication
by \(r\) is natural, and \(r(su)=(rs)u\), proving the converse and composition law. QED.

The theorem uses naturality over all carrier maps. Equivariance under permutations of one fixed
finite set would allow additional globally mixed matrices and is insufficient.

## 3. Ramification comparison classification

Let \(\mathcal R\) be the divisibility category of positive integers: an arrow
\(r:m\to mr\) is multiplication of depth by \(r\). Consider two one-dimensional rational
representations:

\[
W(m)=\mathbb Q,
\qquad W(r)(x)=rx,
\tag{4}
\]

and

\[
N(m)=\mathbb Q,
\qquad N(r)(x)=x.
\tag{5}
\]

Here \(W\) is raw weight-one transport and \(N\) is the depth-normalized observer.

### Theorem 3.1 — inverse depth is the unique natural normalization

Every natural linear transformation \(\eta:W\Rightarrow N\) has a unique scalar
\(c\in\mathbb Q\) with

\[
\boxed{\eta_m(x)=\frac{c}{m}x.}
\tag{6}
\]

Conversely every \(c\) gives a natural transformation by \((6)\). Hence

\[
\operatorname{Nat}(W,N)\cong\mathbb Q.
\tag{7}
\]

#### Proof

Write \(\eta_m(x)=c_mx\). Naturality on \(r:m\to mr\) says

\[
c_{mr}r=c_m.
\tag{8}
\]

Taking the arrow \(m:1\to m\) gives \(c_mm=c_1\), hence
\(c_m=c_1/m\). This proves necessity and uniqueness. Substitution into \((8)\) proves the
converse. QED.

### Corollary 3.2 — fixed-frame rigidity and normalization loophole

1. If the components are required to be depth independent, \(c_m=c\), then naturality holds iff
   \(c=0\).
2. Without that extra fixed-frame requirement, the canonical comparison
   \(\eta_m(x)=x/m\) is nonzero.

The first statement follows from \(2c=c\). The second is Theorem 3.1 with \(c=1\).

## 4. Exact radial no-selection theorem

For \(a\in\mathbb Q\), define the raw radial defect at depth \(m\) by

\[
d_m(a)=ma.
\tag{9}
\]

It transports with weight one:

\[
d_{mr}(a)=r d_m(a).
\tag{10}
\]

Under the canonical inverse-depth comparison,

\[
\boxed{\eta_m(d_m(a))=a}
\tag{11}
\]

for every \(a\). Therefore power naturality and depth normalization retain the entire radial
deformation line. They do not select \(a=0\).

## 5. Literal arithmetic interpretation

On a pure prime-power shell, the raw clock is

\[
\ell_m(p^m)=m\log p.
\]

The power event \(P_r:p^m\mapsto p^{mr}\) multiplies it by \(r\), while the canonical normalized
clock is

\[
\frac1m\ell_m(p^m)=\log p.
\]

For radial parameter \(a\), the logarithmic inverse--dagger discrepancy has the same shape
\(2am\log p\); normalization returns \(2a\log p\), not zero. This is exactly the abstract law
\((11)\).

Consequently, a proposed source-normal Stokes/Bockstein dagger landing cannot be obtained from the
following ingredients alone:

1. the free commutative prime source;
2. natural monoid-homomorphic interventions;
3. ramification-power coherence;
4. depth-normalized comparison.

An additional source datum must destroy the \(c/m\) freedom: an absolute depth/frame, a
nonhomogeneous prime--infinity operation, a non-monoidal intervention, or a singular doctrine in
which inverse-depth normalization is inadmissible.

## 6. Conjecture--proof--failure loops

1. **Natural free-monoid interventions may mix prime labels.** False under full functorial
   naturality by Theorem 2.1. Survivor: unique uniform powers. True under only one finite
   permutation action, showing full naturality is load-bearing.
2. **Power naturality selects the unique fixed radial origin.** False because comparisons are
   allowed to vary with depth. Survivor: complete \(c/m\) classification.
3. **Every natural comparison is zero.** False: \(x\mapsto x/m\) is nonzero and natural.
4. **Depth-independent framing is harmless.** False: it removes every nonzero comparison and is
   exactly an additional constitutive mark.
5. **The free commutative source itself determines \(\log p\).** False: an additive character is
   determined by arbitrary prime weights. The archimedean size function is extra structure.
6. **The theorem proves the dagger landing.** False. It proves a no-selection theorem and
   classifies the precise normalization loophole.

## 7. Parent mathematics and scope

The free commutative monoid monad, Lawvere theories, analytic functors, and natural operations are
classical. The classification proof is elementary functorial algebra. Relevant parent frameworks
include Lawvere-theory/monad equivalence, commutants of algebraic theories, and analytic/shapely
monads. No priority claim is made.

The arithmetic leverage is the synthesis: it eliminates ramification naturality as a standalone
critical-line selector and identifies the exact additional datum a live source construction must
supply.

No analytic continuation, zero statement, source null-homology, or RH consequence is asserted.

## Lean certification

Formalized unconditionally in
`GaloisForLFunctions.HTGeometry.ConstitutiveNaturalPowerNormalization`:

1. natural multiset endomorphisms are unique scalar multiplications;
2. ramification-natural rational coefficient families are exactly \(c/m\);
3. constant natural families are exactly zero;
4. inverse-depth normalization preserves every raw radial parameter.

No theorem premises, project axioms, numerical computation, `sorry`, `admit`, `opaque`, or unsafe
declaration are used. The module and universal-law-field umbrella build successfully.

## Log

- 2026-08-09 — natural free-monoid intervention classification proved.
- 2026-08-09 — fixed-point selector conjecture failed; inverse-depth natural transformations
  classified and radial no-selection theorem extracted.
- 2026-08-09 — exact survivor certified in Lean and promoted to Stage 3.
