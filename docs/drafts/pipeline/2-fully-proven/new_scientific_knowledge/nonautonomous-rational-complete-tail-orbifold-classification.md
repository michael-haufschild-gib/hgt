# Every scalar rational HT tail is an eventual orbifold-current field

- **ID:** nonautonomous-rational-complete-tail-orbifold-classification
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Source:** differential deck descent + Lie--Cartan finite-rank classification + projective defect budgets
- **Statement:** Every nonconstant tail of a degree-expanding nonautonomous rational protocol on scalar free differential fields contains a nonconstant first-order tensor observable.  After a finite transient prefix the protocol is a tower of coverings of parabolic orbifolds, and its complete tail is the finite-holonomy Maurer--Cartan current field.  Moreover a tensor witness can always be chosen with universal weight `12`.

## The theorem

Let `C` be algebraically closed of characteristic zero with trivial derivation.  At phase `i` let

```text
F_i=C<y_i>,
R_i:P1_i->P1_(i+1),  degree(R_i)>=2,
P_(i,n)=R_(i+n-1) composed ... composed R_i,
T_i=intersection_(n>=0) P_(i,n)^*F_(i+n).
```

Then the following are equivalent.

1. `T_i` is nonconstant for one, hence every, phase `i`.
2. `T_i` contains a nonconstant differential rational function of order one.
3. There are a phase `N`, a nonzero integer `k`, and nonzero rational `k`-differentials

   ```text
   omega_i=q_i(z)(dz)^k,  i>=N,
   R_i^*omega_(i+1)=omega_i.                              (1)
   ```

4. After a finite transient prefix, the maps are coverings of parabolic orbifolds and the full
   tail is their finite-holonomy Maurer--Cartan current field.

In `3`, one may always take `k=12` for a nonconstant witness, although the primitive current
generating the full tail can have smaller weight.

The implications `4 => 3 => 2 => 1` are already contained in the first-order tail theorem.  The
new assertion is the converse `1 => 3`: no genuinely higher-jet persistent phase exists.

There is no separate finite-order hypothesis.  Every element of the differential rational field
`C<y_i>` belongs to a finite jet field `C(y_i,...,delta^m y_i)` for some `m`; therefore any
nonconstant tail automatically supplies a finite-order element to which the proof applies.  Formal
jet completions and differential power-series closures are different ambient categories and are
not claimed here.

## 1. The tail is the fixed field of nested finite deck relations

Put `L_i=C<y_i>` and `K_(i,n)=C<P_(i,n)(y_i)>`.  The extension

```text
L_i/K_(i,n)
```

is finite separable of degree `degree(P_(i,n))`.  For a finite faithfully flat extension, the
base is the equalizer of its two maps to the tensor square.  Therefore

```text
h in K_(i,n)
iff
the two pullbacks of h agree on
P_(i,n)(x)=P_(i,n)(y).                                    (2)
```

This is descent along the algebraic equivalence relation, not invariance under a fictitious global
deck group.  The derivation extends uniquely through a separable algebraic extension, so (2)
holds for the differential fields as stated.

The relations are nested because `P_(i,n+1)` factors through `P_(i,n)`.  If `Gamma_i` is their
union with all jet prolongations, then

```text
T_i=L_i^(Gamma_i).                                        (3)
```

There is no nonconstant order-zero element in `T_i`: a compatible rational coordinate would have
degree divisible by every prefix degree.  Hence a nonconstant tail makes the differential-Zariski
closure `G_i` of `Gamma_i` a proper **transitive** rational differential groupoid on `P1_i`.

## 2. Finite-order persistence has rank at most three

The Lie--Cartan/Casale classification of proper transitive differential groupoids on a curve gives
one of the following rational structures:

```text
G1: eta(y)(y')^k=eta(x),                                  (4)
G2: mu(y)y' + y''/y' = mu(x),                             (5)
G3: nu(y)(y')^2 + 2y'''/y' - 3(y''/y')^2 = nu(x).         (6)
```

The first case is already a transported rational tensor and proves `3`.  In the second case the
affine connection has a canonical projectivization

```text
nu=2 mu' - mu^2,                                          (7)
```

whose pullback law is (6).  It is therefore enough to prove that every compatible rational
projective-connection tower has a transported tensor.

Because every prefix deck relation lies in `G_i`, descent (2) applies to the geometric structure
itself.  Thus there are rational projective connections `Q_j` at every later phase such that

```text
Q_i=P_(i,n)^*Q_(i+n).                                     (8)
```

In coordinates, if `Q_j=q_j(z)(dz)^2`, this is

```text
q_i=(q_(i+n) composed P)(P')^2+S_2(P),
S_2(P)=2P'''/P'-3(P''/P')^2.                              (9)
```

## 3. Irregular projective curvature is transient

At a pole of order `r>2`, define the irregularity `I=r-2`.  If a point above it has ramification
index `e`, equation (9) gives source irregularity `eI`; the Schwarzian has order at most two and
cannot cancel this term.  Summing over a degree-`D` fibre gives

```text
I_i >= D I_(i+n).                                         (10)
```

The left side is the fixed finite irregularity budget of `Q_i`, while prefix degrees tend to
infinity.  Hence every sufficiently late `Q_j` is Fuchsian.

At a double pole write `c` for the coefficient of `dt^2/t^2` and set

```text
theta^2=1-c.                                              (11)
```

For a local map `t=s^e`, equation (9) gives

```text
c_source=e^2 c_target+(1-e^2),
theta_source^2=e^2 theta_target^2.                        (12)
```

An affine residue has the identical unsquared law: if `a=1+res(mu)`, then

```text
a_source=e a_target.                                     (13)
```

These exact identities are formalized in Lean.

## 4. The non-orbifold skeleton has at most two worldlines

For a Fuchsian projective connection, call a singular point a **cone point of weight `m`** when the
local projective structure becomes regular after the cyclic cover `s |-> s^m`.  Equivalently it
has exponent difference `1/m` and no logarithmic local monodromy.  Put every other singular point
in the finite set `B_i`.

If `y in B_j` and `x` lies above it, then `x in B_i`.  Indeed, a regular or cone source germ would
make a finite power of the target monodromy finite and would force `theta_target=1/(em)` by (12);
the target germ would itself be a cone.  Therefore

```text
P_(i,n)^(-1)(B_(i+n)) subset B_i.                         (14)
```

Three distinct target fibres trapped in one fixed finite source set are impossible at large
degree.  If their distinct fibre cardinalities are `r_1,r_2,r_3`, Riemann--Hurwitz gives

```text
3D-(r_1+r_2+r_3) <= 2D-2.
```

Since the three fibres are disjoint subsets of `B_i`,

```text
D+2 <= |B_i|.                                             (15)
```

Thus `|B_j|<=2` at every sufficiently late phase.  Relation (14) also makes `|B_j|` antitone, so
it eventually stabilizes at one value

```text
b in {0,1,2}.                                             (16)
```

After stabilization, every fibre above `B_(j+1)` is nonempty, the fibres are disjoint, and their
union is contained in the equally sized set `B_j`.  Hence every such fibre is a singleton, its
point is totally ramified, and

```text
R_j^(-1)(B_(j+1))=B_j.                                   (17)
```

The antitone stabilization, singleton-fibre conclusion, and total-ramification conclusion are
formalized in Lean.

## 5. Negative orbifold Euler characteristic is impossible

At a late phase, give every cone point its finite weight and treat every point of `B_j` as a cusp
of weight infinity.  Define

```text
A_j=sum_y (1-1/m_y),
chi_j=2-A_j.                                              (18)
```

For a cone value of weight `m`, every preimage outside the fixed earlier singular set has
ramification index `m`.  If `s_y` exceptional source points lie over it and `Ram_y` is the
ramification spent over that fibre, direct fibre counting gives

```text
D(1-1/m) <= Ram_y+s_y.                                   (19)
```

For a wholly exceptional fibre the same inequality holds with `m=infinity`.  Summing (19), using
disjointness of the exceptional points and Riemann--Hurwitz, gives the exact defect law

```text
D A_j <= 2D-2+s,
D(A_j-2)+2 <= s,                                         (20)
```

where `s` is the fixed earlier singularity budget.

Every hyperbolic orbifold on the sphere satisfies the Hurwitz gap

```text
A_j-2 >= 1/42.                                           (21)
```

The extremal signature is `(2,3,7)`.  The proof is elementary: with at least four marked points
compare against order two; for three ordered weights split into `a>=3`, `a=2,b>=4`, and
`a=2,b=3`, whose nearest hyperbolic signatures are `(3,3,4)`, `(2,4,5)`, and `(2,3,7)`.
Combining (20) and (21) yields

```text
D <= 42(s-2).                                             (22)
```

Since prefix degrees are unbounded, every sufficiently late signature satisfies

```text
chi_j>=0.                                                 (23)
```

## 6. The stable skeleton forces a tensor

Equation (12), the definition of cone points, and (17) now show that every late `R_j` is an exact
covering between the marked orbifolds of (18): cone weights obey

```text
m_target=e_x m_source,                                   (24)
```

and cusp fibres are precisely the stable exceptional skeleton.

The cases in (16) are rigid.

### Two exceptional worldlines

If `b=2`, inequality (23) permits no cone points.  The signature is `(infinity,infinity)` and (17)
makes `R_j`, after phasewise projective coordinates, a monomial.  The logarithmic differential
`dz/z` is transported up to a nonzero scalar.

### One exceptional worldline

If `b=1`, the cusp consumes one unit of (18), so the cone deficits sum to at most one.  A
Fuchsian projective connection on the sphere cannot have only one singular point.  With one other
marked point, Riemann--Hurwitz forces a two-point monomial cover.  With two cone points, both must
have weight two and the signature is `(2,2,infinity)`; the maps are dihedral/Chebyshev orbifold
covers.  The rational quadratic differential with simple poles at the two order-two points and a
double pole at the cusp is transported up to scalar.

### No exceptional worldline

If `b=0`, there are only cone points.  Equation (23) leaves the spherical and Euclidean signatures.
Exact covering gives

```text
chi_j=degree(R_j) chi_(j+1).                              (25)
```

The sporadic spherical signatures have Euler characteristic bounded away from zero, so they can
occur only in a finite prefix.  The only spherical families that can persist while (25) tends to
zero are the cyclic `(m,m)` and dihedral `(2,2,m)` families.  By the classification of finite
subgroups of `PGL_2`, their coverings lift to inclusions of cyclic or dihedral groups and preserve
`(dz/z)^2` up to scalar.  If `chi=0`, the signature is one of

```text
(infinity,infinity), (2,2,infinity), (2,2,2,2),
(2,3,6), (2,4,4), (3,3,3),                               (26)
```

and the covering lifts to an affine map of the Euclidean universal orbifold cover.  Its
translation-invariant differential descends after taking a finite holonomy power.

These cases exhaust (23).  They prove that a nonzero rational tensor chain exists at all late
phases.

## 7. Universal twelve-charge witness

The finite rotational orders in (26) divide one of `2,3,4,6`; cyclic and dihedral shadows require
at most a square.  Their least universal common multiple is `12`.  Raising the primitive late
current to a suitable power therefore supplies rational `12`-differentials

```text
Omega_j,
R_j^*Omega_(j+1)=c_j Omega_j,  c_j in C^*.                (27)
```

Rescale phasewise by nonzero constants to remove `c_j`.  No infinite product is needed: choose one
phase scalar and define the next recursively.  Pulling the chain through the arbitrary finite
prefix gives a weight-`12` first-order tail observable

```text
W_i=Omega_i(y_i)(delta y_i)^12.                           (28)
```

It is nonconstant and hypertranscendental.  This contradicts minimal rank two or three for the
deck closure and proves `1 => 3`.

## 8. Completeness of the tail

The proved first-order nonautonomous tail classification applies to (28).  It identifies the late
protocol with a parabolic-orbifold covering tower and gives

```text
T_i=C<Q_i>,                                               (29)
```

where `Q_i` is its primitive finite-holonomy Maurer--Cartan current.  Exact phase-tail transport
pulls (29) backward through the finite transient prefix.  Thus higher derivatives create no
additional persistent field, completing all four equivalences.

## Infinite rational divisibility corollary

Let `Q` be a rational projective connection on `P1`.  If there are rational maps `P_n` of
unbounded degree and rational projective connections `Q_n` with

```text
Q=P_n^*Q_n,
```

compatibly through a nested factor tower, then the projective symmetry groupoid of `Q` is not
minimal: its Riccati reduction has an algebraic solution and it contains a rational tensor
subgroupoid.  Equivalently, an irreducible/minimal projective structure is **rationally
indivisible at unbounded depth**.

This is the projective-geometric core of the HT theorem, stated without project vocabulary.

## Physical/topological meaning

The tail is not a state propagated through time.  It is the fixed field of an approximately finite
family of nested constraint relations.  Projective curvature can survive a finite number of
coarse-graining layers, but every terminal defect must be copied across every inverse sheet.
Genus zero supplies only `2D-2` ramification units, whereas hyperbolic curvature demands at least
`D/42` more than the parabolic budget.  A fixed source can pay that excess only finitely often.

What remains at infinite depth is therefore a zero-Euler holographic surface: an affine universal
cover modulo finite holonomy.  The at-most-two non-orbifold singularities are not particles moving
in a flow; they are persistent puncture worldlines of the inverse constraint topology.  The
universal weight `12` is the finite holonomy ceiling of this surface, not a fitted parameter.

## Novelty and significance gate

### Established parents

- Lie--Cartan classification of transitive one-dimensional pseudogroups;
- Casale's rational `G1/G2/G3` classification and autonomous rational-map D-envelopes;
- local Schwarzian/exponent pullback and Riemann--Hurwitz;
- spherical and Euclidean orbifold classification;
- Garofali's autonomous parallel-tensor classification;
- the 2026 algebraic-integrability/minimality criterion for rational projective groupoids.

### Candidate residue

The searched parents do not state the nested nonautonomous theorem, the finite-source defect law
(20), the two-worldline stabilization (14)--(17), the implication from unbounded rational
divisibility to Riccati reduction, or the universal weight-`12` tail witness.  Casale explicitly
uses an autonomous repelling fixed point; that argument does not apply here.  The 2026 minimality
criterion characterizes irreducible projective groupoids but does not test them against an
unbounded nested rational quotient tower.

The result changes the classification of all scalar rational HT tails and excludes every
minimal projective groupoid from infinite rational persistence.  It is therefore significant if
correct.  Scientific novelty remains **unverified** until a broader primary-source and specialist
audit checks projective structures, orbifold morphisms, differential field intersections, and
algebraic correspondences.  Lean verification of the budget core is not evidence of novelty.

## RH impact audit

Every tail of any future source-pure rational protocol on a completed zeta or
`L`-function field must now be a parabolic-orbifold current; a genuinely projective or hyperbolic
tail cannot encode RH at infinite depth.  This turns a proposed RH construction into a sharp test:
one must exhibit the weight-`12` current and then show that its primitive current is RH-sensitive.
No such zeta protocol or sensitivity theorem is supplied here, so there is no direct RH implication.

## Lean status

The formal core is split across:

- `NonautonomousFirstOrderTailSymbol.lean`: tensor transport, defect amplification, finite cutoff,
  and integral cone-angle quantization;
- `NonautonomousProjectiveTailCollapse.lean`: affine/projective local laws, genus-zero marked-fibre
  budget, three trapped-fibre cutoff, antitone exceptional-skeleton stabilization, singleton and
  total-ramification laws, normalized hyperbolic-excess budget, and the algebraic `1/42` cutoff.
- `ParabolicOrbifoldTwelveCharge.lean`: the six parabolic sphere signatures and the universal
  divisibility of every finite cone holonomy order by `12`.

The differential fixed-field descent, Lie--Cartan classification, local analytic cone criterion,
and global orbifold uniformization remain paper-level rather than being introduced as axioms.

## Gates

- [x] 0 -> 1: source-pure statement, exact deck relation, parent boundary, RH passport
- [x] 1 -> 2: complete paper proof through higher-rank collapse and tail reconstruction
- [ ] 2 -> 3: formalize fixed-field/groupoid descent and the global orbifold signature reduction
- [ ] 3 -> 4: standalone manuscript and independent specialist proof/novelty audit

## Log

- 2026-07-15 -- proved the finite-rank reduction, projective defect law, stable two-worldline
  theorem, hyperbolic exclusion, and universal weight-`12` current witness.
