# Cyclic A-infinity law moduli and dual-number event realization

- **ID:** `nhg-cyclic-ainfinity-law-moduli-realization`
- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [NATIVE NHG REALIZATION] [SOURCE-ANCHORED LAW MODULI]`
  `[CYCLIC A_INFINITY] [NONTRIVIAL LAW EVENT] [NO ROUTE INPUT] [NOT RH]`
  `[NO LEAN WRITTEN OR BUILT]`

## 1. Law space before any observer

Let `V` be a finite-dimensional graded vector space over a characteristic-zero field `k`, equipped
with a fixed nondegenerate graded pairing. Let

\[
 C=T^c(sV)=\bigoplus_{n\geq1}(sV)^{\otimes n}
\tag{CA.1}
\]

be the reduced tensor coalgebra. Continuous coderivations of its tensor-length completion form a
graded Lie algebra under graded commutator:

\[
 \mathfrak g=\operatorname{Coder}(\widehat C),
 \qquad
 [D,E]=DE-(-1)^{|D||E|}ED.
\tag{CA.2}
\]

Let `g_cyc` be the subalgebra of coderivations cyclic with respect to the fixed pairing. Filter by
arity. On the positive-arity deformation ideal this is a complete pronilpotent filtration, and

\[
 [F^p\mathfrak g_{\mathrm{cyc}},F^q\mathfrak g_{\mathrm{cyc}}]
 \subseteq F^{p+q-1}\mathfrak g_{\mathrm{cyc}}.
\tag{CA.3}
\]

No target theorem or observer is used in this construction.

## 2. Coderivation field equation

### Theorem 2.1 — cyclic law moduli is a native Q-geometry

A degree-one cyclic coderivation

\[
 Q=\sum_{n\geq1}\widehat m_n
\tag{CA.4}
\]

defines a cyclic `A_infinity` law on `V` exactly when

\[
 \boxed{Q^2=0}
 \qquad\text{equivalently}\qquad
 \frac12[Q,Q]=0.
\tag{CA.5}
\]

At such a source law `Q`, the deformation complex is

\[
 (\mathfrak g_{\mathrm{cyc}},d_Q),
 \qquad
 d_Q\xi=[Q,\xi],
 \qquad
 d_Q^2=0.
\tag{CA.6}
\]

Degree-zero cyclic coordinate changes have infinitesimal anchor

\[
 \boxed{
 \rho_Q:\mathfrak g_{\mathrm{cyc}}^0
 \longrightarrow T_Q\operatorname{MC}(\mathfrak g_{\mathrm{cyc}}),
 \qquad
 \rho_Q(\xi)=[Q,\xi].}
\tag{CA.7}
\]

The pointed formal quotient

\[
 [\operatorname{MC}(\mathfrak g_{\mathrm{cyc}})/
   \exp(F^1\mathfrak g_{\mathrm{cyc}}^0)]_Q
\tag{CA.8}
\]

is therefore a source-anchored filtered cyclic formal law geometry. Its tangent, infinitesimal
automorphism, and primary obstruction spaces are

\[
 H^1(\mathfrak g_{\mathrm{cyc}}^Q),
 \qquad
 H^0(\mathfrak g_{\mathrm{cyc}}^Q),
 \qquad
 H^2(\mathfrak g_{\mathrm{cyc}}^Q).
\tag{CA.9}
\]

### Proof

A coderivation is determined by its corestrictions `m_n:(sV)^(tensor n)->sV`. Expanding `Q^2=0`
in tensor length gives exactly the Stasheff identities. Cyclic coderivations are closed under
commutator, so `(CA.5)` remains inside the cyclic sector. The graded Jacobi identity gives

\[
 d_Q^2\xi=[Q,[Q,\xi]]=\frac12[[Q,Q],\xi]=0.
\tag{CA.10}
\]

Differentiating the Maurer--Cartan equation in the direction `[Q,xi]` gives zero by the same
identity, so `(CA.7)` is tangent to law space. Standard deformation theory identifies `(CA.9)`.
QED.

This is an NHG chart whose points are algebra laws themselves. Gauge is change of cyclic formal
coordinates; deformation and obstruction are intrinsic cohomology of the sourced law.

## 3. Explicit sourced law: dual numbers

Take

\[
 V=\mathbb R\,1\oplus\mathbb R\,\varepsilon,
 \qquad
 \varepsilon^2=0,
\tag{CA.11}
\]

with trace

\[
 \tau(1)=0,
 \qquad
 \tau(\varepsilon)=1.
\tag{CA.12}
\]

The Frobenius pairing is

\[
 \langle a,b\rangle=\tau(ab),
 \qquad
 [\langle-,-\rangle]_{(1,\varepsilon)}
 =\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\tag{CA.13}
\]

It is nondegenerate. Associativity and trace cyclicity make the multiplication coderivation `Q_0`
a sourced cyclic `A_infinity` point satisfying `(CA.5)`.

### Theorem 3.1 — nontrivial law-event tangent

Define a one-parameter family of products by

\[
 \varepsilon\cdot_t\varepsilon=t\,1,
\tag{CA.14}
\]

with the unit rules unchanged. Then:

1. every product `m_t` is associative, unital, and cyclic for the fixed pairing `(CA.13)`;
2. its derivative at zero is the normalized cyclic Hochschild cocycle

   \[
   \phi(\varepsilon,\varepsilon)=1,
   \qquad
   \phi=0\text{ on the other basis pairs};
   \tag{CA.15}
   \]

3. `[phi]` is nonzero in the normalized deformation cohomology. Hence the event is not an
   infinitesimal change of cyclic coordinates.

### Proof

Associativity is checked on the generator: both bracketings of `epsilon^3` equal `t epsilon`.
Cyclicity follows from commutativity and associativity of `tau(abc)`. Differentiating the
associativity equation gives the Hochschild cocycle identity for `phi`.

For a normalized infinitesimal coordinate change `xi` with `xi(1)=0`, write

\[
 \xi(\varepsilon)=a\,1+b\,\varepsilon.
\tag{CA.16}
\]

Its Hochschild coboundary on `(epsilon,epsilon)` is

\[
 (\delta\xi)(\varepsilon,\varepsilon)
 =\varepsilon\xi(\varepsilon)+\xi(\varepsilon)\varepsilon
 =2a\,\varepsilon,
\tag{CA.17}
\]

which cannot equal `1`. Thus `phi` is not a coboundary. QED.

The family crosses a genuine change of algebra law at `t=0`: its tangent survives the gauge anchor.
This supplies a concrete, independently defined source-history direction in NHG.

## 4. Native structures realized

This one chart realizes, before observation:

1. **law points:** cyclic `A_infinity` codifferentials `Q`;
2. **field equation:** `Q^2=0`;
3. **source:** the chosen Frobenius algebra `Q_0`;
4. **anchor:** infinitesimal cyclic coordinate action `[Q,-]`;
5. **filtration:** tensor arity;
6. **polarization:** fixed Frobenius/cyclic pairing;
7. **prolongation:** higher arities `m_n`;
8. **gauge-invariant event tangent:** the nonzero class `[phi]`.

Consequently NHG is not empty and not dependent on an RH endpoint. The remaining analytic
structures—connection choice on a family, relative Atiyah curvature, completion, proper action, and
integrated global history—are additional field layers rather than fitted parts of this example.

## 5. Scope and parent boundary

- This is the formal/local moduli geometry of cyclic `A_infinity` laws. It does not establish the
  global quotient as a Hausdorff analytic stack.
- The exponential gauge group uses the complete positive-arity filtration. Linear changes may be
  included as a separate finite-dimensional structure group.
- A cyclic pairing on `V` supplies noncommutative symplectic law geometry; it does not automatically
  make every cochain-space pairing positive or coercive.
- The dual-number family is a native example, not a universal normal form.
- No connection holonomy, recurrence, physical interpretation, source normalization, or RH claim
  follows.

Coderivation descriptions of `A_infinity` laws and cyclic noncommutative symplectic geometry are
standard parents; see Cho--Lee, <https://arxiv.org/abs/1002.3653>, and
Kontsevich--Soibelman, <https://arxiv.org/abs/math/0606241>. The theorem's role is foundational:
it constructs a nontrivial native law-moduli chart satisfying NHG's source, anchor, filtration,
cyclicity, gauge, deformation, and obstruction requirements before any proof-route calibration.
