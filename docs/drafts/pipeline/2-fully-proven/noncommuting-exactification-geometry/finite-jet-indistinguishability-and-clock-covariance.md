# Finite-jet indistinguishability and clock covariance of hypertranscendence

- **ID:** `finite-jet-indistinguishability-and-clock-covariance`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper proof)
- **Program:** `noncommuting-exactification-geometry`
- **Scientific status:** `[UNCONDITIONAL] [GENERAL HYPERTRANSCENDENCE]`
- **Scope:** analytic germs and one-derivation differential fields; no RH claim
- **Novelty discipline:** the differential-field closure facts and Hölder's theorem are classical.
  New payload is their joint finite-observer theorem and its exact covariance boundary. No claim
  is made that density of differential-algebraic functions in every possible function-space
  topology is new.

## 1. Why this theorem is needed

Any proposed geometry of hypertranscendental objects must answer two questions before it can use
the word geometry.

1. Which changes of differential clock preserve hypertranscendence?
2. Can a finite jet observer distinguish a differentially algebraic germ from a
   hypertranscendental germ?

The answers are sharply different. Base-defined clock changes preserve the property exactly.
Finite jet observers cannot detect it at all. Arbitrary source-dependent analytic coordinate
changes are too large: they can turn two hypertranscendental germs into the identity by
composition.

This supplies a rigorous covariance principle and a rigorous uncertainty principle without
identifying either with RH.

## 2. Definitions

Let \((K,\delta)\) be a differential field of characteristic zero and let \(L\) be a
differential-field extension. An element \(f\in L\) is **differentially algebraic over \(K\)** if

\[
P(f,\delta f,\ldots,\delta^r f)=0
\]

for some \(r\geq 0\) and some nonzero polynomial
\(P\in K[Y_0,\ldots,Y_r]\). It is **hypertranscendental over \(K\)** when no such relation
exists.

Let \(\mathscr G=\mathbb C\{z\}\) be the set of germs at zero of holomorphic functions. Write

\[
j^r f=(f(0),f'(0),\ldots,f^{(r)}(0))\in\mathbb C^{r+1}.
\]

Equip \(\mathscr G\) with the **finite-jet topology**, the initial topology for all maps
\(j^r:\mathscr G\to\mathbb C^{r+1}\). A basic neighborhood constrains finitely many Taylor
coefficients and ignores the tail.

Write \(\mathrm{DA}\subset\mathscr G\) for germs differentially algebraic over \(\mathbb C(z)\),
and \(\mathrm{HT}=\mathscr G\setminus\mathrm{DA}\).

## 3. The triangular clock-change theorem

### Theorem 3.1 — base-clock covariance

Let \(u\in K^\times\), and put

\[
\delta_u=u\delta.
\]

For every \(f\in L\) and every \(n\geq 0\), there are coefficients
\(a_{n,j}\in K\), \(0\leq j<n\), such that

\[
\delta_u^n f
=u^n\delta^n f+\sum_{j<n}a_{n,j}\delta^j f.                 \tag{3.1}
\]

Consequently, for every \(n\),

\[
K[f,\delta_u f,\ldots,\delta_u^n f]
=K[f,\delta f,\ldots,\delta^n f],                              \tag{3.2}
\]

and \(f\) is hypertranscendental for \(\delta\) if and only if it is
hypertranscendental for \(\delta_u\).

#### Proof

For \(n=0\), (3.1) is immediate. Suppose it holds for \(n\). Applying \(u\delta\) gives

\[
\begin{aligned}
\delta_u^{n+1}f
&=u\delta\left(u^n\delta^n f+\sum_{j<n}a_{n,j}\delta^j f\right)\\
&=u^{n+1}\delta^{n+1}f
  +n u^n(\delta u)\delta^n f
  +\sum_{j<n}u(\delta a_{n,j})\delta^j f
  +\sum_{j<n}u a_{n,j}\delta^{j+1}f.
\end{aligned}
\]

All lower coefficients lie in \(K\), proving the induction.

For fixed \(n\), (3.1) is a triangular linear change between the two jet tuples, with
diagonal

\[
1,u,u^2,\ldots,u^n.
\]

Every diagonal entry is invertible. The triangular change therefore has a triangular inverse
over \(K\), proving (3.2). A finite tuple is algebraically dependent over \(K\) before the
change exactly when it is dependent after the change. Taking the union over \(n\) proves the
last assertion. ∎

### Corollary 3.2 — differential-birational generator covariance

If \(K\langle f\rangle=K\langle g\rangle\) inside a common differential extension, then
\(f\) is hypertranscendental over \(K\) if and only if \(g\) is.

#### Proof

In characteristic zero, elements differentially algebraic over \(K\) form a differential
field. If \(f\) is differentially algebraic, every element of \(K\langle f\rangle\), including
\(g\), is differentially algebraic. The reverse implication follows by symmetry. ∎

### Meaning

The intrinsic first-order object is not a chosen derivation \(\delta\), but its Cartan line

\[
[\delta]=\{u\delta:u\in K^\times\}.
\]

Hypertranscendence is invariant under this base-defined clock torsor and under
differential-birational changes of generator. Those are admissible observer changes.

## 4. Every finite jet has algebraic and hypertranscendental realizations

### Theorem 4.1 — exact finite-jet indistinguishability

Fix \(r\geq 0\) and arbitrary values \(c_0,\ldots,c_r\in\mathbb C\). There exist germs
\(p,h\in\mathscr G\) such that

\[
j^r p=j^r h=(c_0,\ldots,c_r),                                  \tag{4.1}
\]

while \(p\) is differentially algebraic and \(h\) is hypertranscendental over
\(\mathbb C(z)\).

#### Proof

Set

\[
p(z)=\sum_{k=0}^r\frac{c_k}{k!}z^k.
\]

Then \(p\) is a polynomial and hence differentially algebraic. Define

\[
h(z)=p(z)+z^{r+1}\Gamma(z+1).                                  \tag{4.2}
\]

The Gamma factor is holomorphic near zero, so \(h\) is a holomorphic germ. The second
term vanishes to order at least \(r+1\); hence (4.1) holds.

Hölder's theorem says that \(\Gamma(z)\) is hypertranscendental over \(\mathbb C(z)\).
Translation by one preserves differential algebraicity in both directions, so
\(\Gamma(z+1)\) is hypertranscendental. Suppose \(h\) were differentially algebraic.
Differentially algebraic elements form a field containing \(\mathbb C(z)\). Therefore

\[
\Gamma(z+1)=\frac{h(z)-p(z)}{z^{r+1}}
\]

would be differentially algebraic, a contradiction. Thus \(h\) is hypertranscendental. ∎

### Corollary 4.2 — mutual density

Both \(\mathrm{DA}\) and \(\mathrm{HT}\) are dense in \(\mathscr G\) for the finite-jet
topology. In particular, neither class has nonempty interior, and neither class is closed.

#### Proof

Every nonempty basic open set contains a finite jet cylinder. Theorem 4.1 supplies both a
differentially algebraic germ and a hypertranscendental germ in that cylinder. Thus both
classes meet every nonempty basic open set and are dense. Since they are disjoint complements
and both are dense, neither has interior and neither is closed. ∎

### Corollary 4.3 — no continuous finite-precision classifier

Let \(Y\) be Hausdorff. There is no continuous map \(F:\mathscr G\to Y\) and two distinct
points \(y_{\mathrm{DA}},y_{\mathrm{HT}}\in Y\) such that

\[
F(\mathrm{DA})=\{y_{\mathrm{DA}}\},\qquad
F(\mathrm{HT})=\{y_{\mathrm{HT}}\}.
\]

In particular, no observer depending on a fixed finite jet order can decide
hypertranscendence.

#### Proof

Continuity and density of \(\mathrm{DA}\) force \(F\) to equal
\(y_{\mathrm{DA}}\) on the closure of \(\mathrm{DA}\), which is all of \(\mathscr G\).
This contradicts its prescribed value on \(\mathrm{HT}\). ∎

## 5. Why arbitrary analytic covariance is forbidden

The base-clock covariance group in Theorem 3.1 cannot be enlarged to all local analytic
coordinate changes.

### Proposition 5.1 — source-dependent trivialization

There exist hypertranscendental analytic germs \(F\) and \(G\), with nonzero first derivatives,
whose composition is the identity germ:

\[
G\circ F=\operatorname{id}.
\]

#### Proof

Let \(E(z)=1/\Gamma(z)\). It is entire, nonconstant, and hypertranscendental: if \(E\)
were differentially algebraic, then its reciprocal \(\Gamma\) would be differentially
algebraic away from the zeros of \(E\), contradicting Hölder.

Because \(E\) is nonconstant, \(E'\) is not identically zero. Choose \(a\) with
\(E'(a)\neq0\). The inverse-function theorem gives a local inverse germ \(G\) of the germ
\(F(z)=E(z)\) at \(a\).

Differentially algebraic analytic germs with nonzero derivative are closed under local
functional inversion. This follows from repeated differentiation of
\(G(F(z))=z\): each derivative of \(G\) at \(F(z)\) is a rational differential expression
in \(F',\ldots,F^{(n)}\), with a power of \(F'\) in the denominator. Substitution into a
differential polynomial for \(G\), followed by clearing denominators, gives a differential
polynomial for \(F\). The chain-rule substitution is a birational isomorphism between the
localized jet fields generated by `F` and by its local inverse, so a nonzero differential
polynomial cannot become the zero polynomial under this substitution. Therefore, if \(G\) were
differentially algebraic, \(F\) would be, contradiction. Both are hypertranscendental, while
\(G\circ F\) is the identity. ∎

### Consequence

An observer is not admissible merely because it is an analytic local coordinate. If the
coordinate is allowed to depend on the source solution, it can use the solution as its own clock
and trivialize hypertranscendence. The covariance group must preserve the base Cartan line and
source provenance; Theorem 3.1 gives a sufficient exact group.

## 6. The finite-observer uncertainty law

Theorem 4.1 is stronger than the statement that no one has found a useful finite invariant. It
says that no finite-jet invariant can possibly distinguish the two classes, even with perfect
measurement of that finite jet. The obstruction is in the tail of the pro-jet object.

Thus a source geometry for hypertranscendence must satisfy all three requirements:

1. its base is the infinite jet pro-object, not any finite jet space;
2. its allowed clock changes preserve the base Cartan line independently of the source;
3. any source-specific coupling to arithmetic, spectral, geometric, or positive observers must
   live in a non-finite tail or in nonlocal transition data.

This theorem does **not** say that hypertranscendence implies RH, curvature, positivity,
noncommutativity, or any particular completion defect.

## 7. Hostile correctness audit

### Attack A — the Gamma perturbation might change the prescribed jet

It does not. The perturbation is divisible by \(z^{r+1}\), so its derivatives through order
\(r\) vanish at zero.

### Attack B — adding a polynomial might destroy hypertranscendence

It cannot. Differentially algebraic elements form a field. If the sum were differentially
algebraic, subtracting the polynomial and dividing by \(z^{r+1}\) would make the translated
Gamma function differentially algebraic.

### Attack C — a clock rescaling may change derivative order

It changes coefficients, not the generated finite jet algebra. Equation (3.1) is triangular with
invertible diagonal, so it is reversible at every order.

### Attack D — all analytic coordinate changes should count as covariance

False by Proposition 5.1. Such a group lets the solution itself become a coordinate and erases the
property. This is the exact analogue of declaring every field-dependent gauge choice physical.

### Attack E — this proves a quantitative Heisenberg inequality

It does not. It proves topological indistinguishability for every finite observer. Quantitative
tradeoffs between multiple exactification sectors require an additional Hilbert or Banach
realization and are treated separately.

## 8. Novelty and significance verdict

- **Classical inputs:** Hölder hypertranscendence of Gamma; closure of differentially algebraic
  elements under field operations, composition where defined, and local inverse; triangular
  changes of derivation.
- **Proved synthesis:** every exact finite jet fiber contains both classes; both classes are dense
  in finite-jet topology; no continuous separated classifier exists; admissible base-clock changes
  preserve HT while source-dependent analytic clocks can erase it.
- **Significance:** this closes an entire class of finite-dimensional geometric searches. Any
  theory claiming to see hypertranscendence at a fixed jet order is false. A viable theory must be
  pro-geometric and source-framed.
- **No overclaim:** the theorem does not identify the required pro-geometric coupling and earns no
  RH progress by itself.

## 9. Lean return notes

Do not write Lean in this phase. Later formalization can split into:

1. triangular iterates of \(u\delta\) in an abstract differential ring;
2. polynomial finite-jet interpolation;
3. an imported theorem or explicit hypothesis for Gamma hypertranscendence;
4. elementary topology proving density from the exact-fiber witness.

Before choosing files, search the existing formal corpus for differential-algebraic closure,
Gamma, jets, and initial topologies. No file path is asserted here.

## 10. Dependencies

- Hölder's theorem: \(\Gamma\) is differentially transcendental over \(\mathbb C(z)\).
- Standard differential algebra in characteristic zero: differentially algebraic elements over a
  differential field form a differential field.
- Complex inverse-function theorem.
