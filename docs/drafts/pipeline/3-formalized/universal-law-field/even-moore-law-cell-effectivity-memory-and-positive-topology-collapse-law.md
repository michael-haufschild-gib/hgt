# Even Moore law cell, effectivity, memory, and positive-topology collapse law

- **ID:** ULF-MOORE-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified)
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveMooreLawCell`
- **Status:** [LEAN-CERTIFIED] [UNIVERSAL-LAW FIELD]
  [TWO-DIMENSIONAL LAW TOPOLOGY] [EFFECTIVITY + FILLING MEMORY]
  [POSITIVITY CHANGES HOMOLOGY] [NON-PRODUCT SYNTHESIS] [NOT RH] [NO PROJECT AXIOMS]

## 1. Moore law cell

Fix an integer \(n\geq2\). Consider the two-dimensional cellular law complex with one cell in
degrees \(0,1,2\), whose only nontrivial boundary has degree \(n\).

For an abelian coefficient group \(A\), written multiplicatively, its reduced chain complex is

\[
 A\xrightarrow{[n]}A,
 \qquad [n](x)=x^n.
\tag{ML.1}
\]

Interpret:

- \(y\in A\) in degree one as a boundary law;
- \(x\in A\) in degree two as a filling;
- \(x\) fills \(y\) when

  \[
   x^n=y.
  \tag{ML.2}
  \]

The two relevant law-homology groups are

\[
 H_2(A)=\ker[n]=A[n],
 \qquad
 H_1(A)=\operatorname{coker}[n]=A/A^n.
\tag{ML.3}
\]

Thus \(H_1\) measures fillability obstruction and \(H_2\) measures ambiguity between fillings.

## 2. Real oriented law

Take

\[
 A=\mathbb R^\times.
\tag{ML.4}
\]

### Theorem 2.1 — parity dichotomy

If \(n\) is odd, the map \(x\mapsto x^n\) is an automorphism of \(\mathbb R^\times\), so

\[
 H_2(\mathbb R^\times)=1,
 \qquad
 H_1(\mathbb R^\times)=1.
\tag{ML.5}
\]

If \(n\) is even, then

\[
 \boxed{
 H_2(\mathbb R^\times)\cong\{\pm1\},
 \qquad
 H_1(\mathbb R^\times)\cong\{\pm1\}.}
\tag{ML.6}
\]

More explicitly:

1. a boundary law \(y\) is fillable if and only if \(y>0\);
2. every fillable \(y>0\) has exactly two fillings

   \[
    x=\pm y^{1/n};
   \tag{ML.7}
   \]

3. the two fillings differ by the nontrivial class in \(H_2\);
4. a negative boundary represents the nontrivial class in \(H_1\).

### Proof

For odd \(n\), real \(n\)-th power is bijective. For even \(n\), its kernel is
\(\{\pm1\}\) and its image is \(\mathbb R_{>0}\). Therefore

\[
 \mathbb R^\times/(\mathbb R^\times)^n
 =
 \mathbb R^\times/\mathbb R_{>0}
 \cong\{\pm1\}.
\tag{ML.8}
\]

The filling statements are the same classification pointwise.

## 3. Positive coefficient observer

Let

\[
 P=\mathbb R_{>0},
 \qquad
 p:\mathbb R^\times\longrightarrow\mathbb R_{>0},
 \qquad
 p(x)=|x|.
\tag{ML.9}
\]

The coefficient map commutes with the law boundary:

\[
 p(x^n)=p(x)^n.
\tag{ML.10}
\]

### Theorem 3.1 — positivity simultaneously repairs and erases

For every \(n\geq2\), the \(n\)-th power map on \(\mathbb R_{>0}\) is an automorphism. Hence

\[
 \boxed{
 H_2(\mathbb R_{>0})=1,
 \qquad
 H_1(\mathbb R_{>0})=1.}
\tag{ML.11}
\]

For even \(n\), coefficient passage (ML.9) therefore does two things at once:

1. **effectivity repair:** a negative, nonfillable oriented boundary \(y<0\) becomes the positive
   fillable boundary \(|y|>0\);
2. **memory erasure:** the two oriented fillings \(\pm y^{1/n}\) become the same positive filling
   \(y^{1/n}\).

Equivalently, positivity kills both nontrivial groups in (ML.6).

### Proof

The logarithm identifies \(\mathbb R_{>0}\) with \((\mathbb R,+)\), under which
\(x\mapsto x^n\) becomes multiplication by \(n\), an automorphism. Equation (ML.11) follows.
The two concrete statements follow from absolute value.

## 4. Exact fibre classification

For even \(n\), define the oriented realization fibre

\[
 \mathcal R_y
 =
 \{x\in\mathbb R^\times:x^n=y\}.
\tag{ML.12}
\]

Then

\[
 \mathcal R_y
 =
 \begin{cases}
 \varnothing,&y<0,\\
 \{+y^{1/n},-y^{1/n}\},&y>0.
 \end{cases}
\tag{ML.13}
\]

The positive realization fibre is always a singleton:

\[
 \mathcal R^+_{|y|}
 =
 \{|y|^{1/n}\}.
\tag{ML.14}
\]

Thus one coefficient change moves the individual realization profile:

- from an empty fibre to a singleton when \(y<0\);
- from a two-point fibre to a singleton when \(y>0\).

The associated matching map over \(\mathbb R^\times\) is in the mixed PLG phase, while its positive
base change is reconstructible. The four-phase PLG classification is therefore not invariant under
coefficient doctrine. Dynamic equivalence and positivity act on the realization topology itself.

## 5. Field significance

One elementary two-cell couples four previously separate faces:

1. **global effectivity:** \(H_1\);
2. **hidden filling memory:** \(H_2\);
3. **observer matching fibre:** empty versus two-point;
4. **positivity:** coefficient change killing both obstruction and memory.

This is not product packaging. All four are determined by the one boundary operator
\([n]:x\mapsto x^n\).

The result suggests that the universal primitive is not a fixed geometry plus positive observer.
It may be a **coefficient-relative law topology**: changing the observer coefficient doctrine can
alter both existence and higher memory.

## 6. Hostile boundaries

1. This is the classical Moore-space cellular calculation interpreted as law topology.
2. Absolute value is a special coefficient quotient; general positive observers need not be
   coefficient changes.
3. Effectivity repair is information loss, not a proof that the oriented law became realizable.
4. The model is finite and abelian. It supplies no dynamics, cost, hypertranscendence, arithmetic
   source, or RH theorem.
5. A universal field must specify which coefficient changes are physical/admissible and which are
   merely lossy observers.

## 7. New conjecture — coefficient-relative law spectrum

A source law should determine a spectrum-valued cellular object \(\mathbb L_{\mathrm{src}}\).
Observer doctrines act by coefficient/change-of-scalars functors

\[
 \mathbb L_{\mathrm{src}}
 \longmapsto
 \mathbb L_{\mathrm{src}}\otimes^{\mathbb L}E.
\tag{ML.15}
\]

The resulting homology sheaves jointly encode:

- negative-degree effectivity obstruction;
- degree-zero realizations;
- positive-degree proof memory.

Positivity, completion, and classical observation become distinct coefficient doctrines. Their
nonconservative base changes can move information between obstruction, realization, and memory
layers.

The next nontrivial test is arithmetic: find a source-native coefficient change whose derived
base-change spectral sequence produces a new transgression rather than merely erasing a known
class.
