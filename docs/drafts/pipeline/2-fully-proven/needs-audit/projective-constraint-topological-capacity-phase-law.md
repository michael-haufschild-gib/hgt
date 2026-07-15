# Functional--relational phase separation for projective constraints

- **ID:** `projective-constraint-topological-capacity-phase-law`
- **Stage:** 2-fully-proven / needs novelty audit
- **Type:** THEOREM (paper) + Lean-formalized arithmetic core
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Depends on:** `nonautonomous-rational-complete-tail-orbifold-classification`
- **Statement:** Minimal projective information cannot persist through an unbounded one-sided
  rational quotient tower on a fixed sphere, but it can persist through algebraic
  correspondences whose supporting surfaces grow.  Every such hyperbolic projective phase obeys
  a degree-times-Euler-capacity law.  Its universal compact threshold is sharp: torsion-free
  `(2,3,7)` correspondence surfaces attain the least possible hyperbolic density,

  ```text
  D = 42(2g-2).
  ```

  Torsion-free modular surfaces give the noncompact saturation `D=6(2g+s-2)`.  Thus growing
  relational topology is a positive storage mechanism, not merely an escape from a no-go.

## The theorem

### A. Topological-capacity bound

Let `P : X -> P1` be a finite map of degree `D` from a smooth compact curve of genus `g`.  Suppose
a rational projective connection on the target has a hyperbolic terminal marked-orbifold defect
of normalized excess `epsilon>0`.  Let `s` be the total source exceptional correction available
outside the forced marked fibres.  Then

```text
D epsilon <= 2g+s-2.                                      (1)
```

In an integral normalization with excess `E` and scale `K`, this is

```text
D E + 2K <= K(s+2g).                                      (2)
```

For a source sphere, `(1)` becomes `D epsilon<=s-2`; hence fixed `s` bounds `D`.  More generally,
an unbounded-degree projective phase requires `2g+s` to grow at least linearly in `D`.

### B. Sharp universal threshold and Hurwitz saturation

For an integral hyperbolic sphere orbifold, the classical Hurwitz gap gives

```text
epsilon >= 1/42,                                          (H1)
```

with equality exactly for signature `(2,3,7)`.  Therefore every compact relational projective
phase satisfies

```text
D <= 42(2g-2),
D+84 <= 84g.                                              (H2)
```

This threshold is attained.  Let `Delta=Delta(2,3,7)` be the orientation-preserving triangle
group and let `H` be a torsion-free subgroup of index `D`.  For the compact surface

```text
X_H=H backslash upper half-plane
```

of genus `g`,

```text
D = 42(2g-2)=84(g-1).                                     (H3)
```

The hypergeometric Schwarzian projective connection `Q_237` uniformizing the `(2,3,7)` orbifold
has non-elementary triangle-group monodromy.  Its Riccati equation has no algebraic solution, so
its Kummer projective groupoid is minimal and admits no tensor or affine reduction.

Moreover, `Delta(2,3,7)` is arithmetic.  Elements of its commensurator give two-sided algebraic
spans

```text
X_H => P1_(2,3,7)                                        (H4)
```

of unbounded degree, both legs pulling `Q_237` back to the same projective connection.  Hence an
irreducible rank-three phase survives at the exact lower edge `1/42`.  The universal no-go
constant is therefore a sharp phase-transition constant, not an artifact of the estimate.

### C. Exact modular saturation

Let `Gamma=PSL_2(Z)`, whose compactified orbifold has signature `(2,3,infinity)`.  Let `H` be a
torsion-free finite-index subgroup, let

```text
X_H = H backslash (upper half-plane union cusps),
D   = [Gamma:H],
g   = genus(X_H),
s   = number of cusps of H.
```

Then

```text
D = 6(2g+s-2),                                             (3)
```

or equivalently

```text
D+12 = 6(s+2g).                                           (4)
```

Equation `(4)` is equality in `(2)` for the modular excess `epsilon=1/6`.  In particular, for two
torsion-free modular surfaces satisfying `(4)`,

```text
D_1<D_2  iff  2g_1+s_1 < 2g_2+s_2.                        (5)
```

The relational projective phase therefore stores degree at exactly six sheets per unit of Euler
capacity.  The capacity bound is sharp.

### D. Positive relational survival

For every finite family

```text
a_1,...,a_m in PGL_2^+(Q),
```

there is a torsion-free finite-index subgroup

```text
H subset Gamma intersect a_1^(-1)Gamma a_1 intersect ...
                 intersect a_m^(-1)Gamma a_m.              (6)
```

Consequently `X_H` has finite algebraic maps

```text
pi_0,pi_1,...,pi_m : X_H -> X(1)=P1,
pi_0([tau])=j(tau),
pi_k([tau])=j(a_k tau).                                    (7)
```

Let `Q_j` be the rational projective connection in the order-three Schwarzian equation for `j`.
Because every `a_k` is Mobius,

```text
pi_0^* Q_j = pi_k^* Q_j                                   (8)
```

for every `k`.  The images of `(pi_0,pi_k)` are modular algebraic correspondences, and the
indices in `(6)` can be chosen unbounded while preserving all previously chosen relations.

The Schwarzian equation of `j` is strongly minimal.  By the minimality criterion for Kummer
projective groupoids, its projective groupoid has no proper positive-order differential
subgroupoid and in particular no tensor or affine reduction.  Hence `(7)--(8)` are arbitrarily
large relational symmetries of an irreducible rank-three projective constraint.  They do not
collapse it to the parabolic tensor phase.

Combining A--D gives the phase separation:

```text
one-sided maps P1 -> P1, fixed source topology:
    unbounded rational depth  =>  projective rank collapses;

two-sided spans X_H => P1, growing source topology:
    unbounded relational degree + exact Euler storage
    => irreducible projective rank can persist.             (9)
```

The second line is the positive theorem paired with the first-line no-go.

## Proof

### Capacity inequality

For every marked target value `y`, write `r_y` for ramification spent above `y` and `f_y` for the
number of points in the fibre.  The fibre identity is

```text
r_y+f_y=D.                                                  (10)
```

Riemann--Hurwitz on a genus-`g` source gives

```text
sum_y r_y + 2 <= 2D+2g.                                    (11)
```

The local affine/projective exponent-discriminant transport law converts the terminal
projective defect into multiplicative orbifold defect.  Summing that local law, and separating
the exceptional corrections, gives in integral normalization

```text
D sum_y delta_y <= K(sum_y r_y + s),                        (12)
2K+E <= sum_y delta_y.                                     (13)
```

Multiplying `(13)` by `D`, applying `(12)`, and then `(11)` yields

```text
D(2K+E) <= K(2D+2g+s),
DE+2K <= K(s+2g),
```

which is `(2)`.  Division by `K` gives `(1)`.

### Sharpness at the Hurwitz triangle

For a hyperbolic sphere orbifold with integral cone orders, order the cone multiplicities.  If
there are three marked points, positivity of

```text
epsilon=1-1/a-1/b-1/c
```

is smallest for `(a,b,c)=(2,3,7)`, where it equals `1/42`; the elementary case split
`a>=3`, `a=2,b>=4`, and `a=2,b=3` proves this.  Four or more marked points have larger excess.
Putting `s=0` in `(1)` gives

```text
D/42 <= D epsilon <= 2g-2,
```

which is `(H2)`.

For a torsion-free degree-`D` cover of `(2,3,7)`, the three marked fibres contain respectively
`D/2`, `D/3`, and `D/7` points.  Their ramification contributions are

```text
D/2,  2D/3,  6D/7.
```

There is no other ramification.  Riemann--Hurwitz gives

```text
2g-2
  =-2D+D/2+2D/3+6D/7
  =D/42,                                                   (H5)
```

proving `(H3)` and equality in `(H2)`.

The Schwarz triangle equation supplies a rational projective connection `Q_237` on the target.
Its projective monodromy is `Delta(2,3,7)`, a non-elementary Fuchsian group.  An algebraic Riccati
solution would have finitely many branches, and monodromy would preserve their finite set in
`P1`.  A non-elementary Fuchsian group has no finite orbit, so no such solution exists.  The
projective Kummer minimality criterion now implies that the groupoid of `Q_237` is minimal.

For `a` in the commensurator of `Delta`, choose a torsion-free finite-index subgroup

```text
H subset Delta intersect a^(-1)Delta a.
```

The functions `t(tau)` and `t(a tau)`, where `t` is the triangle Hauptmodul, descend to the two
legs in `(H4)`.  Precomposition by the Mobius map `a` has zero Schwarzian, so both legs pull back
`Q_237` identically.  Takeuchi arithmeticity of `(2,3,7)` makes the commensurator infinite and
dense; the corresponding intersection indices are unbounded.  This proves relational survival
at the sharp threshold.

### Exact modular identity

Because `H` is torsion-free, the map `X_H -> X(1)` has `D/2` points of ramification index `2`
over the elliptic point of order `2`, and `D/3` points of ramification index `3` over the elliptic
point of order `3`.  If the cusp widths are `w_1,...,w_s`, then

```text
sum_i w_i=D,
sum_i (w_i-1)=D-s.                                         (14)
```

The total ramification is therefore

```text
R = D/2 + 2D/3 + D-s.                                      (15)
```

Riemann--Hurwitz gives

```text
2g-2 = -2D+R = D/6-s.                                      (16)
```

Rearranging proves `(3)` and `(4)`.  Subtracting two instances of `(4)` proves `(5)`.  Thus the
modular family is not merely compatible with the lower bound: it attains it exactly.

### Relational survival

The modular group and each rational conjugate `a_k^(-1)Gamma a_k` are commensurable.  Their
finite intersection therefore has finite index in `Gamma`; intersecting once more with a
torsion-free finite-index subgroup gives `H` in `(6)`.  Taking further finite-index subgroups
produces a nested family with unbounded index.

The containment `H subset a_k^(-1)Gamma a_k` makes `j(a_k tau)` invariant under `H`, so it descends
to the algebraic map `pi_k`.  The Schwarzian chain rule is

```text
S(j after a_k)=(S(j) after a_k)(a_k')^2+S(a_k).             (17)
```

Since `a_k` is Mobius, `S(a_k)=0`.  Equation `(17)` is precisely the pullback identity `(8)`.
Thus both legs of every span carry the same projective constraint.

Freitag--Scanlon prove that the order-three differential equation of `j` is strongly minimal and
that its modular-polynomial relations account for its failure of aleph-zero-categoricity.  The
projective Kummer minimality theorem identifies strong minimality with absence of a proper
positive-order subgroupoid.  Therefore the algebraic spans do not manufacture a hidden tensor
or affine equation.  They preserve the irreducible projective phase while `(3)` supplies the
necessary topology.

The one-sided statement is the complete scalar rational-tail theorem: a compatible unbounded
tower `P1 -> P1` forces a rational tensor after finite depth.  Since the modular phase is minimal,
it cannot occur in that tower.  The difference between the two regimes is exactly the growing
middle surface in the span, measured by `(3)`.

## Meaning for hypertranscendence

The modular `j`-function is differentially algebraic, not hypertranscendental.  Its role here is
to identify the last irreducible finite-rank phase before genuine hypertranscendence.  The theorem
shows that this phase is relational: a fixed carrier cannot hold its unbounded algebraic
symmetries, but a growing correspondence surface can.

Therefore a hypertranscendental function should not be modeled as a field propagated by a finite
local rule.  Even the strongest finite-rank projective constraint already demands extensive
relational topology.  Genuine hypertranscendence lies beyond that projective phase: any proposed
finite-order geometric handle must either acquire growing relational support or collapse to the
parabolic current classified by the scalar theorem.  This is a proved boundary statement, not a
claim that `(1)` characterizes all hypertranscendental functions.

## Physical/topological meaning

Equation `(1)` is an extensivity law.  Hyperbolic projective curvature consumes topology at a
nonzero density; handles contribute two units and punctures one.  Equation `(H3)` identifies the
absolute compact quantum of that density: one unit of negative Euler characteristic per `42`
sheets, realized by the `(2,3,7)` phase.  Equation `(3)` is the noncompact modular saturation at
one unit per six sheets.  The degrees of freedom are not located on either copy of `P1`; they live
in the relational surface joining them.

This gives a mathematically precise holographic analogy: projective information that cannot live
on a fixed one-dimensional carrier is stored in the topology of the correspondence surface.
Nothing here constructs a quantum theory, entropy, time evolution, event horizon, or black-hole
microstate count.  The theorem is a static topological storage law, and “holographic” refers only
to the relocation of constraint information from the carrier to a relational boundary object.

## Positive content beyond the no-go

The result does not stop at “fixed topology is impossible.”  It supplies:

1. a sufficient geometric mechanism for projective survival: finite algebraic spans with growing
   supporting surfaces;
2. an explicit sharp irreducible witness: the minimal `(2,3,7)` Schwarzian connection and its
   arithmetic correspondences;
3. the universal threshold and its exact saturation: `epsilon>=1/42` and `D=42(2g-2)`;
4. a noncompact witness: the strongly minimal Schwarzian equation of `j` and its modular
   correspondences;
5. a rigidity law: ordering by degree is exactly ordering by Euler capacity.

Thus the obstruction has a saturating positive phase on the other side.

## Novelty and significance gate

### Established parents

- the genus formula for finite-index subgroups of `PSL_2(Z)`;
- the Hurwitz `84(g-1)` automorphism bound and the `(2,3,7)` triangle group;
- Takeuchi's arithmeticity classification of triangle groups and the arithmeticity of `(2,3,7)`;
- Elkies, *Shimura curves for level-3 subgroups of the `(2,3,7)` triangle group*,
  [arXiv:math/0409020](https://arxiv.org/abs/math/0409020);
- modular correspondences and the Schwarzian covariance of `j`;
- Freitag--Scanlon, *Strong minimality and the j-function*,
  [arXiv:1402.4588](https://arxiv.org/abs/1402.4588);
- Casale's `G1/G2/G3` differential-groupoid classification and discussion of modular
  correspondences,
  [Publ. Math. 50 (2006)](https://ddd.uab.cat/pub/pubmat/02141493v50n1/02141493v50n1p191.pdf);
- Arenas Tirado--Blazquez-Sanz--Casale, projective Kummer minimality,
  [arXiv:2309.07829](https://arxiv.org/abs/2309.07829);
- modular Schwarzian symmetries in mathematical physics,
  [arXiv:1611.08493](https://arxiv.org/abs/1611.08493).

### Candidate residue

The separate ingredients do not appear, in the sources checked so far, as the sharp dichotomy
`(9)` between one-sided scalar constraint towers and growing two-sided correspondence surfaces.
Nor have they been found packaged as the exact storage interpretation `(1)--(5)` for the boundary
between tensor collapse and irreducible projective survival, or as the assertion that the same
`1/42` constant is both the universal collapse threshold and an attained minimal-projective phase.

The result is significant as a structural theorem for the emerging HT geometry because it
identifies the missing positive phase, its exact resource, and the sharp transition constant.
Nevertheless, the Hurwitz and modular saturation identities are classical consequences once the
correct comparison is posed.  This card therefore remains `[NOVELTY UNVERIFIED]` and does **not**
yet clear the Fields-Medal significance gate.  A specialist audit must check literature on
D-groupoids of algebraic correspondences, arithmetic triangle commensurators, projective
structures, and orbifold-cover complexity.

## RH impact audit

The no-go side says that a source-pure RH mechanism based on an unbounded scalar rational tower on
one completed `P1` cannot retain minimal projective information.  The positive side gives a
concrete alternative architecture: an RH-sensitive projective constraint would have to live on
Hecke-like spans

```text
X_n => P1
```

whose capacity satisfies

```text
2g(X_n)+s(X_n)-2 >= D_n epsilon.                            (18)
```

Any compact version must have topology density at least `1/42`; equality forces the Hurwitz
triangle phase.  For the modular `j` phase, equality holds at the larger cuspidal density
`epsilon=1/6`.  This suggests a falsifiable test for future RH constructions: exhibit a common
projective pullback along arithmetic correspondences, prove linear topological capacity, and only
then test whether the constraint detects critical-line zeros.  The current RH pipeline supplies
none of those three links, so the theorem changes search architecture but proves no RH statement.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/NonautonomousProjectiveTailCollapse.lean` formalizes:

- `markedFiber_cardinality_budget_with_genus`;
- `threeTrappedFibers_degree_add_two_le_exceptionalCard_add_twoGenus`;
- `projectiveOrbifold_excess_topological_capacity`;
- `projectiveCurvature_requires_extensive_topology`;
- `modularTriangle_projectiveCapacity_exact`;
- `modularTriangle_projectiveCapacity_saturates`;
- `modularProjectiveStorage_order_iff`.
- `hurwitzGap_degree_add_eightyFour_le_genus`;
- `hurwitzTriangle_projectiveCapacity_exact`;
- `hurwitzTriangle_projectiveCapacity_saturates`;
- `hurwitzProjectiveStorage_order_iff`.

The modular/triangle-curve existence theorems, Schwarzian pullback identities, arithmeticity, and
projective minimality inputs remain paper-level named theorems rather than Lean axioms.

## Gates

- [x] genus-corrected capacity inequality proved
- [x] universal `1/42` threshold and exact `(2,3,7)` saturation proved
- [x] positive sharp modular saturation proved
- [x] exact arithmetic core formalized in Lean
- [x] functional-versus-relational proof boundary stated
- [ ] broad specialist parent audit
- [ ] formal triangle/modular curves and projective Kummer minimality
