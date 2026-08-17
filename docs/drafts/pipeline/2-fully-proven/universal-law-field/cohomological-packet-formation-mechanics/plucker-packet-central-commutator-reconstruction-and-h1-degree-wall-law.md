# Plücker packet central commutator, reconstruction, and H1-degree wall law

- **ID:** ULF-CPFM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CROSS-ORGAN FUSION / HIGHER-RIGIDITY CORRECTION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [FIELD CORRECTION]`
  `[LEAN FORMALIZED] [NOT RH]`
- **Date:** 2026-08-17

## 1. Two-step packet-formation group

Let \(I\) be a finite nonempty set, put

\[
 V=\mathbb R^I,
 \qquad Z=\mathbb R^{I\times I},
 \qquad (x\boxtimes y)_{ij}=x_i y_j.
\]

On \(\mathsf H_I=V\times Z\), define

\[
 (x,A)\star(y,B)=
 \bigl(x+y,\ A+B+x\boxtimes y\bigr).
 \tag{CP.1}
\]

### Theorem 1.1 — exact two-step formation

Equation `(CP.1)` makes \(\mathsf H_I\) a group, with

\[
 e=(0,0),
 \qquad
 (x,A)^{-1}=\bigl(-x,-A+x\boxtimes x\bigr).
 \tag{CP.2}
\]

Its commutator is central and equals

\[
 [(x,A),(y,B)]
 =\bigl(0,x\boxtimes y-y\boxtimes x\bigr).
 \tag{CP.3}
\]

#### Proof

Bilinearity gives

\[
 x\boxtimes y+(x+y)\boxtimes z
 =y\boxtimes z+x\boxtimes(y+z),
\]

which is exactly associativity of the second coordinate in `(CP.1)`.  Equations `(CP.2)` follow by
direct substitution.  Substituting the two inverses into
\((x,A)(y,B)(x,A)^{-1}(y,B)^{-1}\) cancels every symmetric and marked central term, leaving
`(CP.3)`.  An element with first coordinate zero commutes with every element, so the commutator is
central. QED.

## 2. One commutator is the complete pair packet

For \(a\in V\), let \(\mathbf 1\in V\) be the constant-one vector and define

\[
 g_a=(a,0),\qquad h=(\mathbf1,0),\qquad
 C_a(i,j)=a_i-a_j.
\]

### Theorem 2.1 — central packetization

\[
 \boxed{[g_a,h]=(0,C_a).}
 \tag{CP.4}
\]

For all integers \(m,n\),

\[
 \boxed{[g_a^m,h^n]=(0,mn\,C_a).}
 \tag{CP.5}
\]

#### Proof

Since
\((a\boxtimes\mathbf1-\mathbf1\boxtimes a)_{ij}=a_i-a_j\), `(CP.4)` is `(CP.3)`.
The first coordinates of \(g_a^m\) and \(h^n\) are \(ma\) and \(n\mathbf1\); applying `(CP.3)`
again proves `(CP.5)`. QED.

Thus a finite pair obstruction is not a list of unrelated arrows.  It is one central history value
of a two-step formation law.

## 3. Positive work is exactly the Plücker/Gram determinant

Let \(\mu_i\ge0\), and put

\[
 M=\sum_i\mu_i,
 \qquad A=\sum_i\mu_i a_i,
 \qquad S=\sum_i\mu_i a_i^2.
\]

Define the weighted central work

\[
 \mathcal E_\mu(a)
 =\sum_{i,j}\mu_i\mu_j C_a(i,j)^2.
 \tag{CP.6}
\]

### Theorem 3.1 — central-work/Plücker conservation

\[
 \boxed{
 \mathcal E_\mu(a)=2(MS-A^2)
 =2\det\begin{pmatrix}M&A\\A&S\end{pmatrix}.}
 \tag{CP.7}
\]

Consequently \(\mathcal E_\mu(a)\ge0\).  If every \(\mu_i>0\), then

\[
 \boxed{\mathcal E_\mu(a)=0\iff a\text{ is constant on }I.}
 \tag{CP.8}
\]

#### Proof

Expand \((a_i-a_j)^2=a_i^2+a_j^2-2a_i a_j\) in `(CP.6)` and separate the two finite sums.  This
gives \(MS+MS-2A^2\), proving `(CP.7)`.  The original sum in `(CP.6)` is nonnegative.  Under strict
positive weights it vanishes exactly when every pair difference vanishes, which is `(CP.8)`. QED.

Equation `(CP.7)` fuses pair incidence, central noncommutative history, and positive Gram/Plücker
work without a fitted comparison map.

## 4. Joint reconstruction and reflection neutrality

Assume \(M>0\), and write \(\bar a=A/M\).

### Theorem 4.1 — mean plus central packet reconstructs the source

For every \(i\in I\),

\[
 \boxed{
 a_i=\bar a+{1\over M}\sum_j\mu_j C_a(i,j).}
 \tag{CP.9}
\]

Hence \((\bar a,C_a)\) reconstructs \(a\) exactly, while \(C_a\) alone reconstructs \(a\) modulo
the constant line.

For \(c\in\mathbb R\), define the reflected source

\[
 \rho_c(a)=c\mathbf1-a.
\]

Then

\[
 \boxed{C_{\rho_c(a)}=-C_a,qquad
 \mathcal E_\mu(\rho_c(a))=\mathcal E_\mu(a).}
 \tag{CP.10}
\]

#### Proof

Summing \(C_a(i,j)=a_i-a_j\) against \(\mu_j\) gives \(Ma_i-A\), proving `(CP.9)`.
Equation `(CP.10)` follows by subtracting two reflected coordinates and then squaring. QED.

This is an exact orientation/positivity quotient: reflection reverses the unsquared central history
and leaves its positive work unchanged.

### Corollary 4.2 — oriented fixedness selects the constant sector

If a comparison preserves the oriented packet while implementing reflection,

\[
 C_{\rho_c(a)}=C_a,
\]

then \(C_a=0\), so \(a\) is constant.  If additionally \(\bar a=0\), then \(a=0\).

This is a typed finite selector.  The theorem does not assert that an arithmetic source supplies
the orientation-preserving comparison.

## 5. Exact H1/H2 degree wall

Let \(p:\mathsf H_I\to V\) be first-coordinate projection and let
\(z:\mathsf H_I\to Z\) be central-coordinate projection.  Then

\[
 p(uv)=p(u)+p(v),
 \qquad
 z(uv)-z(u)-z(v)=p(u)\boxtimes p(v).
 \tag{CP.11}
\]

### Theorem 5.1 — additive reporters erase the packet

Every group homomorphism from \(\mathsf H_I\) to an abelian group sends every packet commutator
`(CP.4)` to zero.  Meanwhile `z` is not an additive reporter: its failure of additivity is the
bilinear \(2\)-cocycle in `(CP.11)`, whose antisymmetrization is `C_a`.

#### Proof

Every homomorphism to an abelian group kills every commutator.  The second assertion is exactly the
second coordinate of `(CP.1)`. QED.

Thus central packetization does **not** construct the Hilbert \(1\)-cocycle required by a
Delorme--Guichardet/property-(T) argument.  It constructs degree-two extension data.  Any
degree-lowering map must supply a nontrivial coefficient representation or a separate
transgression theorem.

### Corollary 5.2 — what property-(T) packetization would already prove

Suppose a property-(T) group \(G\), a unitary representation \(\pi\), a Hilbert \(1\)-cocycle
\(b\), and elements \(q_F\in G\) are independently constructed with

\[
 \|b(q_F)\|^2=\mathcal E_F.
\]

Then Delorme--Guichardet makes \(b\) a coboundary,
\(b(g)=\pi(g)\xi-\xi\), and therefore

\[
 \boxed{\mathcal E_F\le4\|\xi\|^2\quad\text{for every }F.}
 \tag{CP.12}
\]

The central commutator theorem alone supplies none of \(G,\pi,b,\xi\).  In particular, a central
extension or an \(A_2\) Lie-algebra rank jump cannot be cited as `(CP.12)` without the missing
degree-lowering representation.

## 6. Four-organ prediction

Equation `(CP.5)` predicts the response of repeated formation histories:

\[
 \boxed{
 \mathcal E_\mu([g_a^m,h^n])=(mn)^2\mathcal E_\mu([g_a,h]).}
 \tag{CP.13}
\]

Thus central history grows bilinearly in winding counts while positive work grows quartically in
the two winding amplitudes.  This prediction is forced by the same law that generated the pair
packet; no clock, recurrence metric, or extra energy was appended.

## 7. Hostile scope

1. The group is a finite two-step calibration, not the completed arithmetic source group.
2. Positive work forgets central orientation exactly as `(CP.10)` states.
3. Central packetization is not Hilbert packetization and gives no property-(T) contradiction.
4. The fixedness selector in Corollary 4.2 needs an orientation-preserving source comparison;
   norm neutrality is insufficient.
5. Cofinal properness needs a specified topology and weight system.  Finite strict positivity does
   not supply it.
6. No hypertranscendence, Xi landing, zero exclusion, or RH statement is claimed.

## 8. Parent boundary

- Free two-step nilpotent Lie algebras and generalized Heisenberg formation are classical:
  <https://arxiv.org/abs/1703.06214>.
- Property-(T) controls affine Hilbert \(1\)-cocycles through Delorme--Guichardet:
  <https://ncatlab.org/nlab/files/BekkaHarpeValetteOnKashdanPropertyT.pdf>.
- Central extensions are classified in cohomological degree two:
  <https://arxiv.org/abs/math/0511357>.
- Current-algebra central extensions are established parent machinery:
  <https://arxiv.org/abs/0812.2625>.

The theorem is retained as a route-independent bridge and a correction to the field's
higher-rank packetization gate.

## 9. Lean formalization

The unconditional finite core is formalized in
`formal/GaloisForLFunctions/HTGeometry/ConstitutiveCohomologicalPacketFormation.lean`:

1. associative packet product, identity, inverse, and commutator;
2. packet-coordinate identity `(CP.4)`;
3. weighted energy/Gram identity `(CP.7)`;
4. reconstruction `(CP.9)` and reflection law `(CP.10)`;
5. repeated-commutator scaling `(CP.5)`.

The module additionally proves centrality, strict-positive-weight zero-work rigidity, additive
reporter erasure, and the central-coordinate two-cocycle defect.  Its declarations use no project
axioms, `sorry`, `admit`, `opaque`, or `unsafe` definitions.

Property-(T) is cited parent mathematics and is not to be axiomatized in Lean.
