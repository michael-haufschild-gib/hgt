# Integral cylinder comparison for the shifted Legendre extension

- **ID:** RH-LICC-20261006
- **Stage:** 1-in-progress
- **Parent:** `xi-marked-legendre-affine-gluing.md`
- **Status:** integral cocycle quotient, relative pairing, and finite branch-gluing presentation verified in Lean; five-line Prym comparison proved on paper using its classical parent; original cylinder map and arithmetic comparison open; no RH conclusion.

## Target

Construct the cylinder correspondence from the discriminant curve

```
Q_delta: y^2=x*(x-1)*(x+delta)*(x+delta-1)
```

to the tensor part of the fibre product of `E_w` and `E_(w+delta)`, for `delta` outside `{0,1,-1}`. Determine its **integral** image in parabolic cohomology and its specialization at `delta=0`, before substituting `delta=p^(-s)*xi(s)`.

Two incompatible hypotheses must be distinguished: the cylinder image is primitive after removing torsion; or a genuine finite-index defect survives and requires additional relative boundary classes. An isomorphism after tensoring with `C` would not decide this. No exact index is asserted in advance.

`[OPEN CORE]`: an explicit cylinder correspondence, including every compactification component, together with the induced integral map into the cocycle lattice below and its degeneration law. A nonzero arithmetic class must be constructed separately; a nonzero cohomology space is insufficient.

## Exact chamber and monodromy model

Start with real `delta>1` and ordered punctures `-delta,1-delta,0,1`. Choose standard paths and independent bases for the two Legendre systems. Write

```
T0 = [[1,2],[0,1]],   T1 = [[1,0],[-2,1]],
C=T0*T1=[[-3,2],[-2,1]].
```

On `M=Mat_(2x2)(Z)`, the four finite monodromies act as

```
r1(M)=T0*M,   r2(M)=T1*M,
r3(M)=M*T0^(-1),   r4(M)=M*T1^(-1).
```

Operators compose in their usual order. Their product is `R(M)=C*M*C^(-1)`. The infinity monodromy is `R^(-1)`. These equations specify the integral coefficient model. The chosen-loop identification with the geometric family must be retained when constructing its cylinder map.

Use left crossed cocycles: `v(gh)=v(g)+rho(g)*v(h)`. Integral parabolicity requires the local value to lie in the **actual integral image** of local monodromy minus identity, not merely its rational span. Thus the finite local values have the form

```
v1=2*[[u,v],[0,0]],     v2=2*[[0,0],[w,x]],
v3=2*[[0,y],[0,z]],     v4=2*[[r,0],[s,0]],
```

with all eight letters in `Z`. Infinity parabolicity says

```
S=v1+r1(v2)+r1*r2(v3)+r1*r2*r3(v4) in im(R-1).
```

## Paper calculation of the exact integral lattice

Direct matrix multiplication gives `S=2*P`, where

```
P11=u+2w-3r+2s,
P12=v+2x-3y+2z+6r-4s,
P21=w-2r+s,
P22=x-2y+z+4r-2s.
```

Put `D=[[-1,1],[-1,1]]`, so `C=-1+2D`, `D^2=0`, and `C^(-1)=-1-2D`. For an arbitrary matrix `B=[[a,b],[c,d]]`, put `k=b+c` and `q=a+b-c-d`. Then

```
(R-1)(B)=2*[[-k-2q, k+3q],[-k-q,k+2q]].
```

Every integer pair `(k,q)` occurs: choose `b=k,c=0,a=q-k,d=0`. Hence a matrix `2P` lies in `im(R-1)` exactly when

```
P11+P22=0,     2P11+P12-P21=0.
```

Substituting the displayed entries is equivalent to

```
u=-2w-x+2y-z-r,       v=w-y+s.
```

Therefore integral parabolic cocycles are parametrized without denominators by the six free integers `(w,x,y,z,r,s)`.

The coboundary associated with `B=[[a,b],[c,d]]` has free coordinates

```
(-a,-b,-a,-c,b,d).
```

Its quotient is read exactly by

```
(w,x,y,z,r,s) |-> (y-w, x+r).
```

This map is onto: `(0,0,h,0,k,0)` maps to `(h,k)`. Its kernel consists precisely of the displayed coboundaries: if `y=w` and `r=-x`, choose `a=-w,b=-x,c=-z,d=s`. Thus the integral parabolic cohomology of this coefficient model is free of rank two, with these explicit coordinates. There is no torsion in this particular quotient. This does not settle the index of the cylinder image inside it.

No finite-field point counting, numerical experiment, estimate, positive form, or eigenvalue argument is used. These are exact symbolic identities and an exact kernel/image decomposition. They are now Lean-verified in `HTGeometry/LegendreParabolicLattice.lean`.

## Geometric checks already obtained

The change of variables

```
t=(1+delta)*x/(x+delta),
v=delta*(1+delta)*y/(x+delta)^2
```

identifies the smooth projective `Q_delta` with `v^2=t*(t-1)*(t-(1-delta^2))`.

The two points at infinity on the quartic map to

```
P=(1+delta,delta*(1+delta)),   -P.
```

The tangent slope at `P` is `1+delta`, so the chord-and-tangent law gives `2P=(1,0)`. Thus `P` has order four. The four branch points map to the full two-torsion. Consequently degree-zero divisor classes supported on these six evident marks generate a group isomorphic to `Z/4 x Z/2`; any additive map from that group to a complex vector space is zero. A nonzero complex regulator cannot be obtained by merely linearly reading these marked divisor classes. This does not rule out higher cycle classes, relative chains, or a source-specific analytic section after pullback.

The stronger universal Mordell–Weil classification is classical: the quadratic Legendre surface has fibre configuration `I4,I4,I2,I2`, with group `Z/4 x Z/2`. This is a parent-theory check, not a new theorem claimed here. It must not be confused with a classification of analytic sections after the transcendental substitution involving Xi.

## Sources, scope and next steps

- Legendre monodromy: the author notes cited in the parent card.
- Parabolic cocycles: Collas–Dettweiler–Reiter–Sawin, *Monodromy of Elliptic Curve Convolution*, and its Dettweiler–Wewers references. Their elliptic-base formulation must be adapted explicitly to this sphere.
- Schütt–Shioda, [*Elliptic Surfaces*](https://arxiv.org/abs/0907.0298), Section 9, supplies the classical extremal-surface parent classification; Top–Yui, [*Some elliptic modular surfaces*](https://www.math.rug.nl/~top/top-yu.pdf), lists the associated cusp widths.
- Standard conic-bundle/Prym comparisons are relevant, but the current affine conic has extra boundary components. A theorem requiring a smooth irreducible discriminant cannot be applied without resolving them.

- [x] Compute the integral cocycle lattice on paper, retaining the factors of two.
- [x] Audit the specified matrix convention and integral infinity condition; verify their symbolic identities in Lean. The chosen-loop identification with the actual cylinder correspondence is still separate.
- [ ] Construct all discriminant and compactification components and the cylinder correspondence.
- [ ] Determine the exact integral image and specialization; audit novelty against the closest parent theories.
- [ ] Construct the actual arithmetic source class. Do not replace its required law by an assumed equivariance square.

The main RH goal remains active. No new significant theorem beyond literature has yet been certified for this card.

### Current comparison audit

The deep corpus query `parabolic cocycle integral quotient pairing monodromy` completed with `partial=false`, complete source inventory (68,018 files), and no directly applicable comparison theorem. Compiler coverage is mostly pending; retrieved names are not compiler certificates. A lexical `Humbert Prym gluing --any` query mainly returned the unrelated positive-definite Humbert reduction modules. Those are not used.

- [x] Audit the infinity residues and the complete five-line discriminant after changing the base from `P1 x P1` to `P2`.
- [x] Identify the discriminant cover with the ruling cover of an explicit net of diagonal quadrics, including branch-point labels, on paper.
- [x] Apply the precise classical Prym theorem after checking its hypotheses; distinguish this comparison from the original integral parabolic cylinder map.
- [x] Verify the exact cocycle quotient, full relative cup expression, and finite gluing presentation in Lean.
- [ ] Formalize the actual algebraic curves, net correspondence, and geometric normalization sequence. The finite gluing module does not stand in for these.
- [ ] Return to the arithmetic source class; the universal geometric comparison alone cannot locate Xi zeros.

Working conjecture: after the necessary boundary modifications, the admissible discriminant cover is the ruling cover of the net

```
diag(X, X-W, Z, Z-W, Z-X-delta*W).
```

Its base curve has equations

```
U1^2+U2^2-U5^2=0,
U3^2+U4^2+U5^2=0,
U2^2+U4^2+delta*U5^2=0.
```

The linear coordinate change `(u0,u1,u2,u3,u4)=(U5,U2,i*U1,i*U4,U3)` identifies it with `H_delta`. The conjecture is falsifiable by any mismatch in the five residue square classes or their nodal gluing. Its classical parent is Beauville's discriminant-cover description of the Jacobian of an intersection of three quadrics. Therefore even a successful identification is classified **BRIDGE**, not a new field or a new RH theorem.

### Five-line Prym comparison: dependency-closed paper result

Work over `C`, with `delta != 0,1,-1`. In `P2_[X:Z:W]`, let `D` be the union of the five lines

```
X=0, X=W, Z=0, Z=W, Z-X-delta*W=0.
```

There are ten distinct pairwise intersections and no triple intersections: the four grid points miss the fifth line precisely under the three exclusions on `delta`; the two parallel pairs meet at distinct points at infinity which miss the fifth line. On each line take the connected double cover branched at its four intersection points, and glue the unique ramification points over each node. This defines an admissible double cover `Dtilde -> D` without an extra gluing choice. Its normalized components are exactly the five elliptic curves in the residue table.

The diagonal net displayed above has determinant equal to the product of these five line forms. Over a smooth point of a discriminant line its rank is four; the two rulings are distinguished by the square root of the product of the other four diagonal coefficients. Restricting these products to the five lines gives, up to constant squares,

```
z(z-1)(z-delta), z(z-1)(z-1-delta),
x(x-1)(x+delta), x(x-1)(x+delta-1),
x(x-1)(x+delta)(x+delta-1).
```

These agree with all five conic residues. At every crossing the remaining three coefficients are nonzero, so the quadric has rank three and the two ruling sheets meet in the admissible local model. The base curve is `H_delta` under the explicit coordinate change, and is smooth by the gradient argument above. Beauville, [*Variétés de Prym et jacobiennes intermédiaires*](https://math.univ-cotedazur.fr/u/beauvill/pubs/prym.pdf), Theorem 6.3(i), now identifies `Prym(Dtilde/D)` with `J(H_delta)` through algebraic cycle correspondences. The algebraic statement is sufficient here; no positive form or estimate is used.

Here is the exact finite gluing group, beyond a rank comparison. Put `A=product_i J(E_i)`. At vertex `i` of `K5`, identify `E_i[2]` with even subsets of its four incident edges, modulo the full four-edge subset. (A pair records the difference of two branch points; complementary pairs give the same two-torsion point.) For an even-degree edge subset `c` of `K5`, send `c` to these five local classes. Its kernel consists exactly of the empty and full edge subsets: a zero local class makes each row empty or full, and the common edge of every pair of vertices forces all rows to have the same value. The cycle space has dimension `10-5+1=6`, so the image `G` has dimension five over `F2`.

Beauville's Proposition 0.3.3 identifies the Prym as `A/G`; its normalization gluing generators are precisely these cycle classes. Thus the five normalized elliptic cylinder channels together have **index 32** in the integral lattice of this Prym. Each single channel is primitive: if a gluing class is supported only at vertex `i`, all four other rows are constant; edges among those vertices force one common value, and their edges to `i` then force the remaining row to be constant too. Hence `G` intersects each elliptic factor trivially. The induced map from each factor to `A/G` is an embedding of tori, so its lattice is primitive.

This is a classical-parent **BRIDGE**, with the exact branch labels and graph kernel made explicit. The index statement concerns the five-factor map into the discriminant Prym. It does **not** yet identify the original parabolic rank-two cocycle lattice with its diagonal channel, nor prove a comparison for an unspecified resolution of the original fibre product. Those claims still require an actual integral cylinder map. In particular, a birational map alone does not identify third cohomology: blowing up a curve can add its first cohomology.

The infinity audit in `P1 x P1` explains the missing graph edges. Along `x=infinity` the residue is `z(z-1)`; along `z=infinity` it is `x(x-1)`. These two double covers are rational and each connects two elliptic components. Near `(infinity,infinity)`, with `u=1/x,v=1/z`, the quaternion is equivalent to

```
((1-u)/(1-v), (1-u)*u*v*(v-u+delta*u*v)).
```

The first entry is a square in the complex analytic local ring, so no local Brauer ramification remains there. Blowing up this point resolves the rational map `(x,z) -> [x:z:1]`; contracting the strict infinity rulings produces the two missing nodes of the five-line arrangement. This establishes the discriminant-cover comparison, without asserting that every modification of a total space preserves its integral third cohomology.

## Pairing and boundary audit: additional paper calculations

The left-cocycle version of the relative cup pairing can be written, up to the overall orientation sign, as

```
cup(a,b) = sum_i B(S_(i-1)^a, P_(i-1)*b_i) - sum_i B(e_i^a,b_i),
S_(i-1)^a=sum_(j<i) P_(j-1)*a_j,
P_i=r1*...*ri,   a_i=(ri-1)*e_i^a,
B(M,N)=M11*N22+M22*N11-M12*N21-M21*N12.
```

The relation gives `S_5=0`. The bar-chain boundary is the sum of the puncture loops; subtracting the local primitives gives the second term. Both coboundary arguments telescope to zero. Invariance of `B` gives alternation. The formula agrees, after changing right/left conventions, with the topological formula in Dettweiler–Wewers, [*Variation of parabolic cohomology and Poincare duality*](https://arxiv.org/abs/math/0411119), Theorem 2.5. Its positive Hermitian-form results are not used.

More explicitly, the relative bar chain is `sum_i [P_(i-1)|g_i]`, with boundary `sum_i [g_i]`. Evaluating the left cup cochain gives the first sum above; evaluating the primitive correction on that boundary gives the second. Replacing a primitive by an invariant vector changes nothing, since each other local value is an image of `ri-1`. For a global first coboundary `(rho(g)-1)e`, the cross terms telescope to `sum_i B(e,b_i)`, cancelled by the local sum. For a second coboundary `(rho(g)-1)f`, summation by parts gives `-sum_i B(a_i,ri*f)`; substituting `a_i=(ri-1)e_i` cancels the primitive sum. This fixes the left/right convention directly, independently of reading a right-cocycle formula by analogy.

For the basis `(y-w,x+r)=(1,0),(0,1)`, choose free coordinates `(0,0,1,0,0,0)` and `(0,0,0,0,1,0)`. The corresponding finite cocycles are

```
a1=[[4,-2],[0,0]], a2=0, a3=[[0,2],[0,0]], a4=0,
b1=[[-2,0],[0,0]], b2=0, b3=0, b4=[[2,0],[0,0]].
```

Their partial sums before infinity are `Sa=[[4,-8],[0,-4]]` and `Sb=[[-8,12],[-4,8]]`. Choose the first cocycle's local primitives `e1=[[0,0],[2,-1]]`, `e3=[[-1,0],[0,0]]`, and `e5=[[-4,2],[0,0]]`; the other two are zero. The second cocycle's infinity value is `[[-8,4],[-12,8]]`. The cross terms sum to `-8`, and the local terms sum to `-6`, giving `cup(a,b)=-2`. Thus the integral pairing is `[[0,-2],[2,0]]`. Lean now verifies the stronger identity for arbitrary pairs of six-coordinate cocycles: `relativeCup(v,w)=-2*(h(v)*k(w)-k(v)*h(w))`, as well as all five primitive/relation formulas used by that expression. A factor of two in a pairing does not by itself determine a cylinder-map index.

### Four boundary elliptic curves cannot be discarded

Put `A=x(x-1)`, `B=z(z-1)`, `C=x-z+delta`. The conic is

```
B*y1^2 - A*y2^2 = A*B*C*y0^2.
```

Its generic quaternion description is `(A/B,A*C)`. The square classes of its residues along the five finite discriminant components give the following double covers:

| Component | Residue square class | Cover |
|---|---|---|
| `C=0` | `A/B`, equivalently `A*B` | `Q_delta` |
| `x=0` | `-B*C` | `E_delta` |
| `x=1` | `-B*C` | `E_(1+delta)` |
| `z=0` | `A*C` | `E_(-delta)` |
| `z=1` | `A*C` | `E_(1-delta)` |

The residue formula is `(-1)^(v(a)v(b))*a^v(b)/b^v(a)` modulo squares. These are exact square-class identities, not a completed resolution at infinity. In particular, the extra components are elliptic rather than rational. The earlier temptation to keep only the diagonal discriminant would lose four nontrivial channels.

### Explicit genus-five carrier and its nodal limit

All five covers are the four-point subcovers of the five-point configuration

```
{0,1,-delta,1-delta,infinity}.
```

Its maximal elementary-abelian double cover is the projective curve

```
H_delta in P4:
u1^2-u2^2=u0^2,
u3^2-u1^2=delta*u0^2,
u4^2-u2^2=delta*u0^2.
```

For `delta` outside `{0,1,-1}`, its affine function field adjoins square roots of `x,x-1,x+delta,x+delta-1`. Their square classes are independent by valuations at their four distinct finite roots. The cover has degree 16 and five branch points of inertia order two. Riemann–Hurwitz gives `2g-2=-32+40=8`, so `g=5`. Smoothness also follows directly from the diagonal quadrics: no two coordinates can vanish at a point, and the remaining gradient columns have rank three. This is a classical Humbert curve; a novel general construction is not claimed.

At `delta=0`, the special fibre consists of the four smooth conics

```
u3=epsilon*u1,   u4=eta*u2,   u1^2-u2^2=u0^2,
(epsilon,eta) in {1,-1}^2.
```

Changing only `epsilon` gives two intersection points (`u1=0`, `u2=+/-i*u0`); changing only `eta` gives two (`u2=0`, `u1=+/-u0`). Changing both gives no projective intersection. Thus there are eight nodes, and the dual graph is a square with each edge doubled. Its first Betti number is `8-4+1=5`, matching the arithmetic genus.

Near the first type of node, in the chart `u0=1`, the exact smoothing equation is `(u3-u1)*(u3+u1)=delta`; near the second it is `(u4-u2)*(u4+u2)=delta`. The other coordinates are solved by the implicit-function theorem because their relevant values are nonzero. This proves a proper nodal degeneration with all eight smoothing parameters equal to `delta`. After `delta=p^(-s)*xi(s)`, a zero of order `m` has each node equation `a*b=p^(-s)*xi(s)` and leading normal coefficient `p^(-rho)*j`. For `m>1`, regularity of the total space requires separate resolution; no simple-zero assumption is made.

The five coordinate-sign involutions give degree-two genus-one quotients. Their Jacobians yield the classical isogeny from `J(H_delta)` to the product of five elliptic curves, with kernel `(Z/2)^5`; see Stoll, [*Diagonal genus 5 curves*](https://www.mathe2.uni-bayreuth.de/stoll/papers/dioph5.pdf), Section 2, and Auffarth–Lucchini Arteche–Rojas, [*A decomposition of the Jacobian of a Humbert–Edge curve*](https://arxiv.org/abs/1905.12690). This supports a carrier including all five channels, but **does not prove** that its integral lattice is the required cylinder lattice of the fibre product. That identification remains open.

## Source-rich extension of the construction to test next

For several primes, do not discard the relative normal directions during degeneration. In the auxiliary source plane `(s,w)`, the graphs

```
w=-p^(-s)*xi(s)
```

all meet along `w=xi(s)=0`. In the chart of the blowup of `(w,xi(s))` with `w=t*xi(s)`, their strict transforms meet the exceptional line at `t=-p^(-rho)`. Adding the source graph `w=-xi(s)` anchors `t=-1`; the graph `w=0` anchors zero. Thus a simultaneous marked degeneration retains relative prime coefficients even though one reduced node loses them. Distinct primes give distinct marks in the open strip: equality would force `(p/q)^(-rho)=1`, contradicting the real part of its exponential exponent.

This is a concrete candidate for retaining arithmetic input in higher simultaneous covers. It is not a zero-location proof: functional-equation symmetry may still exchange exceptional components over different zeros. The missing step is a source-derived comparison fixing the appropriate component, not the mere existence of the blowup or of its marked points. The immediate task remains the integral five-channel cylinder comparison above.

## Verification and next source construction

Two new leaves are wired into the HTGeometry umbrella:

- `LegendreParabolicLattice.lean`: exact integral infinity image, actual local primitives, coboundary kernel/range equality, quotient equivalence with `Z x Z`, and the full relative cup identity.
- `HumbertBranchGluing.lean`: explicit six-edge presentation, its constant-vector kernel, an equivalence of the gluing group with `(Z/2)^5`, cardinality 32, and trivial intersection with a single local channel.

Both direct `lake env lean` checks passed without warnings. A targeted `lake build --old` of both leaves passed. The five principal declarations' axiom audit returned only `propext`, `Classical.choice`, and `Quot.sound`. Index generation passed. Global lint exited 1 with eight umbrella-reachability errors outside these leaves: `WeilZetaSquareAveraging`, `WeilZetaSquareBoundaryInequality`, `WeilZetaSquareMoments`, `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, and `BoundaryCoronaCStarAlgebra`. This is not a globally clean lint claim.

The next source construction is recorded in `xi-legendre-formal-source-section.md`: an explicit non-torsion section in the `E_(1+delta)` channel, with formal parameter `q` on `q^2=delta/(1-delta)`. Its paper proof is complete, but its formal-group interpretation and global division-cover comparison remain unformalized. It supplies a geometric section, not automatically the required nearby-cycle class. None of these universal pullback constructions has yet used enough Xi-specific arithmetic to force a zero location.

### Research audit

Novelty gate: **not passed**. The Prym/Jacobian comparison and section argument have classical parents. The concrete frontier advanced from an unspecified five-channel carrier to an exact discriminant cover, a verified finite gluing presentation, and a proposed actual source section. This is useful bridge work, not an unconditional RH advance. No effort estimate was used to abandon the open cylinder or arithmetic problem. Next work must attack the actual integral comparison and global source-class transport, rather than accumulate further arbitrary coefficient lemmas.
