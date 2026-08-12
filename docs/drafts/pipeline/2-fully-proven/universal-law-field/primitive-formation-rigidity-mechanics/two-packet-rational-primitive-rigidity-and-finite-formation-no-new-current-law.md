# Two-packet rational primitive rigidity and finite-formation no-new-current law

- **ID:** ULF-PFRM-1
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT FORMATION-RIGIDITY THEOREM + ARITHMETIC COROLLARY
- **Source:** `../../../1-in-progress/prime-additive-differential-field-primitive-rigidity.md`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [CHARACTERISTIC ZERO]`
  `[TWO-PACKET FREENESS] [RATIONAL DENOMINATORS CLOSED] [FINITE FORMATION RIGIDITY]`
  `[GENERAL MECHANISM] [ARITHMETIC COROLLARY] [NOVELTY UNVERIFIED] [NOT RH] [NO LEAN YET]`
- **Statement:** In a differential realization admitting two disjoint algebraically free packet
  copies, every packet-additive element of a finitely generated rational differential field is a
  finite constant-coefficient linear combination of source jets.  For prime-radial arithmetic
  sources, the intersection of their differential field with the positive-prime-power additive
  sector is exactly their finite jet span.

## 1. Why this is a field-mechanism theorem

The recurring unsuccessful move in many proof routes is:

1. begin with finitely many collective source currents;
2. apply rational algebraic operations and finitely many derivatives;
3. hope that cancellation creates a new additive local current.

The theorem below proves that this mechanism cannot work whenever the source can be separated into
two free packets.  Rational nonlinearity necessarily creates mixed-packet support.  If the mixed
support disappears exactly, then the rational expression was linear in the source jets already.

The primitive is a law, not an object:

\[
 \boxed{
 \text{two-copy freeness}
 +\text{packet additivity}
 +\text{finite rational formation}
 \Longrightarrow
 \text{linear primitive current}.}
 \tag{PFR.1}
\]

This is the rational-field counterpart of polynomial Hopf-primitive extraction.  The denominator
problem is load-bearing and is solved before any arithmetic specialization.

## 2. Rational Cauchy rigidity

Let (k) be a field of characteristic zero and let

\[
 k(X)=k(X_1,\ldots,X_N)
\]

be a finite rational function field.  In the independent two-copy field (k(X,Y)), put

\[
 X+Y=(X_1+Y_1,\ldots,X_N+Y_N).
\]

### Theorem 2.1 -- rational additive functions are linear

If (F\in k(X)) satisfies

\[
 \boxed{F(X+Y)=F(X)+F(Y)}
 \tag{PFR.2}
\]

in (k(X,Y)), then unique constants (c_1,\ldots,c_N\in k) satisfy

\[
 \boxed{F(X)=\sum_{j=1}^N c_jX_j.}
 \tag{PFR.3}
\]

### Proof

For each (j), differentiate `(PFR.2)` with respect to (Y_j).  Writing

\[
 G_j=\frac{\partial F}{\partial X_j},
\]

gives

\[
 G_j(X+Y)=G_j(Y).
 \tag{PFR.4}
\]

The change of algebraically independent coordinates

\[
 (X,Y)\longleftrightarrow(Z=X+Y,Y)
\]

turns `(PFR.4)` into (G_j(Z)=G_j(Y)) in (k(Z,Y)).  The intersection of the two pure
rational subfields is

\[
 k(Z)\cap k(Y)=k,
\]

so (G_j=c_j\in k).

Hence

\[
 H(X)=F(X)-\sum_jc_jX_j
\]

has every partial derivative zero.  In characteristic zero the common constant field of the
standard derivations on (k(X)) is (k), so (H=c\in k).  Substitution into `(PFR.2)` gives
(c=2c), hence (c=0).  This proves `(PFR.3)`.  Uniqueness follows from algebraic independence.
QED.

### Hostile characteristic check

Characteristic zero is necessary.  In characteristic (p), (F(X)=X_1^p) satisfies

\[
 F(X+Y)=F(X)+F(Y)
\]

and is nonlinear.  Thus Frobenius primitives are a real extra sector, not a proof artifact.

## 3. Abstract two-packet primitive theorem

Let (A) be a commutative integral (k)-algebra with derivation (D), and write
(L=\operatorname{Frac}(A)).  Let (V) be a (k)-vector space and let
(x:V\to A) be a (k)-linear source realization.  Put

\[
 K=k\langle x(v):v\in V\rangle_D\subseteq L.
 \tag{PFR.5}
\]

Every element of (K) uses only finitely many labels and finitely many jets.

Assume there exist three (k)-algebra maps on (A), called packet restrictions,

\[
 r_0,r_1,r_{01}:A\longrightarrow A,
 \tag{PFR.6}
\]

commuting with (D), such that for every source jet

\[
 r_{01}(D^nx(v))=r_0(D^nx(v))+r_1(D^nx(v)).
 \tag{PFR.7}
\]

The maps need not be injective on all of (A).  Instead require the exact condition which makes
rational evaluation legal:

> **Two-packet freeness.** For every finite linearly independent source list
> (v_1,\ldots,v_d\in V), and every jet cutoff (M), the family
> \[
> \{r_0(D^nx(v_a)),r_1(D^nx(v_a)):1\le a\le d,0\le n\le M\}
> \]
> is algebraically independent over (k).

Call (z\in A) **packet-additive** when

\[
 r_{01}(z)=r_0(z)+r_1(z).
 \tag{PFR.8}
\]

### Theorem 3.1 -- finite rational formation creates no new packet-additive current

Under two-packet freeness,

\[
 \boxed{
 K\cap\{z\in A:r_{01}z=r_0z+r_1z\}
 =\operatorname{span}_k\{D^nx(v):v\in V,n\ge0\}.}
 \tag{PFR.9}
\]

Here `span` means finite linear span.

### Proof

The right-to-left inclusion follows from `(PFR.7)` and linearity.

Let (z\in K\cap A) satisfy `(PFR.8)`.  Choose finitely many source vectors used by one rational
differential expression for (z), replace them by a basis (v_1,\ldots,v_d) of their finite
linear span, and choose (M) larger than every jet order in the expression.  Write

\[
 z=F(G),\qquad
 G=(D^nx(v_a))_{1\le a\le d,0\le n\le M},
 \tag{PFR.10}
\]

for (F=P/Q\in k(X)), (Q\ne0).

Put (G_0=r_0G) and (G_1=r_1G).  Two-packet freeness says that ((G_0,G_1)) is algebraically
independent.  Therefore

\[
 Q(G_0)\ne0,\qquad Q(G_1)\ne0,\qquad Q(G_0+G_1)\ne0.
 \tag{PFR.11}
\]

This is the denominator step.  Although (r_0,r_1,r_{01}) may kill unrelated elements of (A),
they extend uniquely to the particular finitely generated rational field used in `(PFR.10)`.
Applying the algebra maps to (Q(G)z=P(G)) gives

\[
 r_0z=F(G_0),\qquad
 r_1z=F(G_1),\qquad
 r_{01}z=F(G_0+G_1).
 \tag{PFR.12}
\]

Equation `(PFR.8)` now gives

\[
 F(G_0+G_1)=F(G_0)+F(G_1).
 \tag{PFR.13}
\]

Because evaluation at the algebraically independent family ((G_0,G_1)) is injective,
`(PFR.13)` is the formal identity `(PFR.2)`.  Theorem 2.1 makes (F) a constant-coefficient
linear form.  Substituting into `(PFR.10)` proves that (z) lies in the finite jet span.  QED.

## 4. Prime-radial arithmetic realization

Let (mathcal A) be the complex Dirichlet-convolution algebra of arithmetic functions and let
(mathcal L=\operatorname{Frac}(\mathcal A)).  Let (D) be the rotated logarithmic derivation.
For a profile

\[
 u(t)=\sum_{n\ge1}u_nt^n\in t\mathbb C[[t]],
\]

write (a_u\in\mathcal A) for the prime-radial source

\[
 a_u(p^n)=u_n,qquad
 a_u(m)=0\quad\text{away from positive prime powers}.
 \tag{PFR.14}
\]

For a profile subspace (W\le t\mathbb C[[t]]), define the differential field over constants

\[
 K(W)=\mathbb C\langle a_u:u\in W\rangle_D\subseteq\mathcal L.
 \tag{PFR.15}
\]

Let (mathcal P_0\subseteq\mathcal A) be the vector space of arithmetic functions which vanish at
(1) and away from positive prime powers.  These are precisely the coefficientwise additive
prime-local currents relevant here.

For a set (S) of primes, let (r_Sf) retain the coefficients on the free submonoid generated by
(S) and kill every other coefficient.  Then (r_S) is a unital convolution-algebra map and

\[
 r_SD=Dr_S.
 \tag{PFR.16}
\]

Choose disjoint infinite prime sets (S_0,S_1).  Put (r_0=r_{S_0}), (r_1=r_{S_1}), and
(r_{01}=r_{S_0\cup S_1}).

### Lemma 4.1 -- two disjoint infinite prime packets are jet-free

If (u_1,\ldots,u_d) are linearly independent profiles, then for every (M\ge0),

\[
 \{r_{S_b}(D^na_{u_j}):b\in\{0,1\},1\le j\le d,0\le n\le M\}
 \tag{PFR.17}
\]

is algebraically independent over (mathbb C).

### Proof

Linear independence of the profiles supplies distinct valuation rows
(e_1,\ldots,e_d) with nonsingular evaluation minor

\[
 (u_j(e_i))_{i,j}.
\]

Each infinite packet contains enough pairwise distinct primes to build the finite jet rectangle.
Apply the prime-coordinate derivations on those chosen rays.  The coefficient of the product of
the selected prime powers in the arithmetic-function Jacobian is the product of:

1. the nonzero profile minor;
2. logarithmic-clock Vandermonde determinants for jet orders (0,\ldots,M);
3. the corresponding block from the second disjoint packet.

The two packet blocks are disjoint, so the joint determinant is block diagonal and nonzero.
The arithmetic-function Jacobian criterion gives algebraic independence. This uses the **proof
mechanism** of the prime-valuation leading-echelon theorem, not a formally stronger reading of its
statement: that theorem is phrased for complete prime rays, whereas its determinant depends on only
the finitely many selected coordinate rays. Choosing all those rays inside `S_0` or `S_1` gives the
displayed block-diagonal minor; coefficients on unchosen rays are absent from the determinant and
cannot cancel it. Infinitude of each packet supplies the required number of selected rays. QED.

### Theorem 4.2 -- prime-additive differential-field primitive rigidity

For every complex profile subspace (W\le t\mathbb C[[t]]),

\[
 \boxed{
 K(W)\cap\mathcal P_0
 =\mathbb C[D]a_W
 :=\operatorname{span}_{\mathbb C}
   \{D^na_u:u\in W,n\ge0\}.}
 \tag{PFR.18}
\]

Every representation on the right is finite.  If a profile basis is fixed, the jet coefficients
are unique.

### Proof

The reverse inclusion is immediate because (D) preserves positive-prime-power support and the
zero coefficient at (1).

For (z\in\mathcal P_0), disjoint prime support gives

\[
 r_{S_0\cup S_1}z=r_{S_0}z+r_{S_1}z.
 \tag{PFR.19}
\]

For every source jet, the same identity holds.  Lemma 4.1 supplies two-packet freeness.  Theorem
3.1 therefore gives `(PFR.18)`.  QED.

## 5. Exact leverage

The theorem closes a broad family of proposed source mechanisms.

### Corollary 5.1 -- rational nonlinear formation cannot return a new additive Euler current

Let (z\in\mathcal P_0) be obtained from finitely many prime-radial sources by finitely many field
operations and logarithmic derivatives.  Then (z) is already a constant-coefficient finite jet
combination of those sources.

In particular, multiplication, division, rational feedback, finite elimination, and finite
differential closure cannot manufacture a new prime-additive direction.  Every genuinely new
additive output must use at least one of:

1. a new profile direction;
2. non-radial source coefficients supplied before the rational expression;
3. a mixed-prime formation followed by a nonrational primitive such as logarithm;
4. an infinite or singular completion not represented by one finite rational expression;
5. a coefficient base already containing local prime data.

This is stronger than differential-rank classification.  It classifies **all additive outputs** of
the finite rational differential field, not merely outputs assumed prime-radial in advance.

### Corollary 5.2 -- fourth-organ prediction

Suppose a future comparison claims to generate a new additive prime current (J) from a finite
prime-radial differential packet.  If one coefficient test proves

\[
 J\notin\mathbb C[D]a_W,
\]

then the comparison cannot be a finite rational differential operation on that packet.  It must
expose a new source direction or a genuine admission/completion event.  Thus the theorem predicts
where a new topology is compulsory before constructing it.

## 6. Four-organ fusion

| organ | exact role |
|---|---|
| source formation | disjoint prime packets add source jets |
| hypertranscendence | packet jet families are algebraically free |
| primitive/current sector | positive-prime-power support imposes packet additivity |
| admission/topology | finite rational operations are classified; infinite completion is the only remaining escape |

The conservation identity is the rational Cauchy equation `(PFR.2)`.  Joint reconstruction is
provided by injective two-packet evaluation: the two packet copies recover the formal rational
expression before the primitive equation is solved.

The theorem therefore implements four steps of the intervention grammar in one mechanism:

\[
 \textsf{form}\to\textsf{ghost/primitive}\to\textsf{saturate}\to\textsf{admit}.
\]

It does not claim that the necessary infinite completion exists.  It proves that finite rational
formation cannot substitute for it.

## 7. Hostile boundaries

1. **Characteristic (p).** Frobenius gives nonlinear additive rational functions.  The theorem is
   false without characteristic zero.
2. **Finite packets.** A fixed finite prime set cannot realize arbitrarily large jet rectangles.
   Two infinite packets are load-bearing.
3. **Finite-prime coefficient base.** If the base field already contains individual prime
   indicators, `(PFR.18)` is false as written.  The theorem is over the constant field
   (mathbb C).
4. **Completed expressions.** Infinite series, limits, logarithms, and non-Hausdorff quotients are
   outside the finite rational differential field.  They are not ruled out; they are the exact
   survivor.
5. **Mixed support.** A nonlinear rational expression is allowed to exist; it simply carries
   composite/cross-packet support and is not a new additive current.
6. **Constants.** The condition (z(1)=0) removes the augmentation constant.  Without it, the
   affine version contains one constant term and packet additivity must be centered.
7. **RH.** The theorem constrains source generation.  It supplies no zero-free region and does not
   select a divisor point.

## 8. Literature and priority boundary

Parent mathematics:

- rational homomorphisms (mathbb G_a^N\to\mathbb G_a) are linear in characteristic zero;
- Hopf primitives in symmetric algebras;
- Shapiro--Sparer arithmetic-function Jacobians;
- Pong, *Applications of differential algebra to algebraic independence of arithmetic
  functions*, [arXiv:1504.03263](https://arxiv.org/abs/1504.03263);
- the corpus's prime-valuation profile differential-field and complete-tail independence theorems.

Broad searches through August 2026 found these ingredients separately, but did not locate the
two-packet rational primitive-intersection theorem `(PFR.18)` for Dirichlet-convolution fields.
This is not a priority claim.  Label the exact arithmetic coupling `[NOVELTY UNVERIFIED]` until
specialist review; the abstract rational Cauchy theorem is classical.

## 9. Conjecture loops closed

1. **Packet restriction of a fraction is automatically defined. -- False.** A restriction may
   kill its denominator.  Survivor: two-packet algebraic freeness proves every nonzero formal
   denominator remains nonzero on the exact finite palette used by the element.
2. **Polynomial Hopf-primitive extraction already proves the field theorem. -- False.** Inverses
   are not polynomial.  Survivor: Theorem 2.1 works in the rational field itself.
3. **Nonlinear cancellation may create a hidden additive current. -- False in the classified
   mechanism.** It would solve the rational Cauchy equation and is therefore linear.
4. **Prime-radial field classification is enough. -- False.** It assumes the output is radial.
   Theorem 4.2 assumes only additive prime-power support and derives the finite jet form.
5. **The theorem forces the missing completion. -- False.** It proves precisely that completion or
   a new source direction is necessary; existence remains a separate theorem.

## 10. Gates

- [x] rational primitive theorem proved without evaluation at a possible pole
- [x] denominator restriction obstruction closed by packet freeness
- [x] two-packet joint algebraic independence reduced to the proved separated-prime determinant
- [x] arbitrary profile subspace reduced to each element's finite source basis
- [x] exact intersection law `(PFR.18)` proved on paper
- [x] characteristic, coefficient-base, packet-size, and completion countermodels recorded
- [x] broad internal and external collision audit
- [ ] Lean formalization of Theorems 2.1, 3.1, and the arithmetic packet corollary
- [ ] publication-level specialist priority review
- [x] construct a source-generated infinite primitive completion escaping Corollary 5.1

The completion gate is resolved, and its naive strict-fracture form falsified, by
`product-primitive-saturation-resolvent-and-formation-depth-properness-law.md`: product completion
admits the source resolvent but saturates the entire active primitive sector. The surviving
invariant is exact cofinal formation depth.

## Log

- 2026-08-12 -- solved the denominator obstruction by evaluating only after two-packet freeness;
  proved the formal rational Cauchy theorem by differentiating in independent packet coordinates;
  promoted the exact arithmetic intersection law to Stage 2.
