# Every critical projective horizon has full symmetric monodromy

- **ID:** `projective-horizon-full-symmetric-monodromy`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / ALL-RANK BRANCHED-COVER TOPOLOGY
- **Scientific status:** `[PROVED ON PAPER] [NOVELTY PROVISIONAL] [SIGNIFICANT]`
- **Formal status:** conormal-displacement uniqueness core formalized
- **Parents:** `projective-horizon-irreducible-simple-ramification`,
  `projective-horizon-rank-one-full-monodromy`,
  `projective-horizon-reversal-self-legendre-tower`
- **Lane:** source-pure hypertranscendental geometry; static monodromy

## Theorem

Let `K` be an algebraically closed characteristic-zero field, let `m,n>=1`, set `L=m+n`, and
consider the critical raw/reciprocal tail map

```text
Phi_(m,n): X(t)=sum_(i=0)^(L-1)x_i t^i  |->
  ((x_m,...,x_(L-1)),(y_n,...,y_(L-1))),
Y=X^-1 mod t^L.                                            (1)
```

Restrict to the open chart

```text
x_0 p_m q_n != 0,       p_m=x_m, q_n=y_n.                  (2)
```

The map is generically finite of degree

```text
D=choose(L,m).                                              (3)
```

Its geometric monodromy group on the `D` critical states is

```text
Mon_geom(Phi_(m,n))=S_D.                                   (4)
```

Moreover, the irreducible rectangular-Schur ramification divisor maps generically one-to-one to
the branch divisor.  A meridian around its smooth generic point acts as one transposition, not as
a product of several transpositions.

## Proof

### 1. Finite cover and one ramification component

The critical multiplicity theorem gives `(3)`.  Its biprojective boundary exclusion shows that,
under `(2)`, no state escapes to infinity, so the critical map is finite after restricting to the
stated open base.

The ramification theorem identifies the Jacobian divisor with the rectangular Schur polynomial,
proves that it is irreducible and reduced, and proves generic corank one.  Thus its generic points
are simple folds.  What remained open was whether several such folds lay over one generic branch
value.

### 2. The exact Lagrangian conormal remembers the tangent pair

Write a state as

```text
X=A+P,   deg A<m,   ord P>=m,
Y=B+Q,   deg B<n,   ord Q>=n.                              (5)
```

At a ramification point, a vertical tangent is a nonzero low pair `(U,V)` satisfying

```text
deg U<m,   deg V<n,   UY+XV=0 mod t^L.                     (6)
```

The inversion graph is Lagrangian for

```text
omega((dX,dY),(dX',dY'))=[t^(L-1)](dX dY'-dX' dY).         (7)
```

Pairing `(U,V)` with a general tangent and using the low-degree bounds gives the branch conormal

```text
eta_(U,V)(delta P,delta Q)
  =[t^(L-1)](U delta Q-delta P V).                         (8)
```

The pairing in `(8)` is perfect: the coefficients of `U` pair in reverse order with
`delta q_n,...,delta q_(L-1)`, and the coefficients of `V` pair in reverse order with
`delta p_m,...,delta p_(L-1)`.  Therefore the projective conormal line at the branch value uniquely
determines the projective tangent pair `(U,V)`.

### 3. A generic branch value has only one ramified state

Suppose two generic ramified states `(X,Y)` and `(X',Y')` lie over the same smooth branch value.
The branch has one conormal line, so part 2 lets us scale their kernel pairs to the same `(U,V)`.
Because the tails agree,

```text
D_0=X'-X,    deg D_0<m,
E_0=Y'-Y,    deg E_0<n.                                   (9)
```

Subtracting the two tangent equations gives the exact polynomial syzygy

```text
D_0 V+E_0 U=0.                                             (10)
```

At the generic Schur fold, the endpoint coefficient `U(0)` is nonzero.  Its vanishing is a proper
cofactor locus inside the irreducible determinant divisor: the relevant `(m-1) x (m-1)` Toeplitz
cofactor is a nonzero Schur polynomial and cannot be divisible by the larger irreducible determinant.
The degree-zero part of `(6)` then also makes `V(0)` nonzero.

Consequently `U` and `V` are coprime at the generic fold.  Indeed, any common factor `g` has
`g(0)!=0`, hence is invertible modulo `t^L`.  Dividing `(6)` by `g` would produce another low tangent
pair.  Generic corank one makes it proportional to `(U,V)`, which forces `g` to be constant.

Euclid's lemma now turns `(10)` into

```text
D_0=C U,       E_0=-C V.                                   (11)
```

for a polynomial `C`.

Subtract the two inverse identities and use the tangent identity `(6)`.  With `(11)`, the result
can be written in either of the equivalent forms

```text
C U (Y+Y')=0 mod t^L,
C V (X+X')=0 mod t^L.                                     (12)
```

If the states were distinct, `C U` would be nonzero of degree below `m`.  But the common marked
tail gives

```text
[t^n](Y+Y')=2q_n !=0.                                     (13)
```

The product in the first equation of `(12)` therefore has a nonzero coefficient strictly below
`m+n=L`, by multiplicativity of polynomial trailing degree.  This contradicts `(12)`.  Hence the
states coincide.  The ramification-to-branch degree is one, and generic branch inertia is a single
transposition.

### 4. The transpositions cannot preserve hidden blocks

Let `G<=S_D` be geometric monodromy and let `H` be the normal subgroup generated by meridians around
the irreducible Schur branch.  Part 3 makes those meridians transpositions.  A group generated by
transpositions is a product of symmetric groups on the connected components of its transposition
graph.  Its orbits are therefore a block system for `G`.

If there were more than one block, the induced block cover would be a nontrivial finite etale cover
of the whole parameter chart

```text
S=(G_m)^2 x A^(L-2),                                      (14)
```

because the only interior branch inertia lies in `H`.  For `m,n>=2`, no such intermediate cover
can occur inside the rational source function field.  Indeed, finite etale covers of `(14)` over an
algebraically closed characteristic-zero field are torus Kummer covers.  Every nontrivial one has a
cyclic quotient of the form

```text
z^r=p_m^a q_n^b,        (a,b) not both 0 mod r.             (15)
```

In the source field, the prime divisor `x_m=0` has valuation

```text
v_m(p_m)=1,   v_m(q_n)=0,                                  (16)
```

because `m>=2` and the reciprocal coefficient `y_n` remains generically nonzero when `x_m=0`.
The triangular inverse-coordinate divisor `y_n=0` likewise has

```text
v_n(q_n)=1,   v_n(p_m)=0.                                  (17)
```

Applying `(16)--(17)` to `(15)` forces `r|a` and `r|b`, a contradiction.  Thus the block cover is
trivial, `H` is transitive, and a transitive group generated by transpositions is `S_D`.

When `min(m,n)=1`, the separately proved rank-one eliminant theorem gives `S_L=S_D`, including the
exceptional `(1,1)` Kummer presentation.  This completes all cases and proves `(4)`.  `QED`

## What the theorem rules out

At the pure-tail point the `D` states are visibly `m`-subsets of `L` roots, and the subgroup `S_L`
acts through that labeling.  The theorem proves that this label is not conserved by arbitrary tail
deformation when `m,n>=2`: the generic monodromy expands to the full symmetric group on all
`choose(L,m)` states.  There is no hidden spectral polynomial whose root subsets globally label the
all-tail cover, no particle-number block system beyond the fixed cardinality of the fiber, and no
generic complement pairing at `m=n`.

The structures that survive arbitrary tails are exactly the ones proved earlier: the exact
Lagrangian graph, reversal Legendre duality, the irreducible Schur caustic, and the Q-system of its
mass determinants.

## Exact reconstruction-complexity transition

Full symmetric monodromy has two immediate sharp consequences.

First, the natural `S_D` action is primitive, so the generic finite horizon map has no nontrivial
factorization through a lower-degree connected cover.  Critical reconstruction is algebraically
atomic even though its ramification determinants satisfy an integrable Q-system.

It also has no rational section when `D>1`: a finite-tail algebraic formula cannot choose one
critical state consistently over the generic parameter space.  Any state selector must add
non-algebraic continuation data or source-specific structure outside the universal finite tails.

Second, the generic state equation is solvable by radicals exactly when `S_D` is solvable, hence
exactly when `D<=4`.  Since `D=choose(m+n,m)`, the only positive horizon pairs in this radical regime
are

```text
(1,1), (1,2), (2,1), (1,3), (3,1).                         (18)
```

Every genuinely two-sided horizon `m,n>=2` has `D>=choose(4,2)=6` and is generically not solvable by
radicals.  Rank-one horizons cross the same boundary at total depth `m+n=5`.  Thus determinant-level
integrability and state-level algebraic solvability are rigorously different properties of the
constraint.

## Physical and topological meaning

Finite horizon vacua are locally distinguishable but globally unlabelled.  Adiabatic continuation
in the static observation-parameter space can realize every permutation of the critical states.
The pure fermionic occupation labels are a symmetry-enhanced boundary coordinate system, not
fundamental particles.

The physical object is therefore a maximally braided exact-Lagrangian polarization atlas:

```text
local vacua             = sheets of a finite Lagrangian projection,
massless horizon        = one irreducible Schur fold,
global continuation     = the full symmetric group on all sheets,
all polarization masses = one nonvanishing Q-system.       (19)
```

Its first genuinely two-sided finite observation already has six globally unlabelled vacua and an
Abel--Ruffini obstruction to generic radical reconstruction.  This is static algebraic complexity,
not dynamical chaos.

This is topology of a static constraint family.  It supplies no time variable, Hamiltonian,
quantization, black-hole interior, or Born rule.

## Novelty and significance audit

Generic polynomial monodromy, fold conormals of Lagrangian maps, transposition graphs, torus etale
covers, and Kummer valuations are classical ingredients.  The candidate new result is their exact
conjunction for every reciprocal-jet horizon map: the rectangular Schur ramification component has
branch degree one and forces full `S_(choose(m+n,m))` monodromy at every rank.

The conclusion is strictly stronger than the classical pure Grassmannian/subset model and refutes
the most plausible invariant-block alternative.  A targeted literature audit found generic sparse
system monodromy and Grassmannian Bethe/subset actions, but no theorem for this all-tail reciprocal
horizon cover.  Novelty remains provisional pending expert review.

This clears the lane's stated all-rank monodromy target and gives a genuine global classification of
the finite vacuum topology.  It is significant new knowledge for the proposed hypertranscendental
geometry.  It still does not classify hypertranscendental functions themselves or create an
external application at the scale required by the user's Fields-Medal completion bar.

## Primary literature boundary checked

- Esterov proves full symmetric monodromy for general reduced irreducible sparse square systems,
  but the reciprocal-tail coefficients here form a special constrained family rather than the
  independently generic coefficient family of that theorem:
  <https://arxiv.org/abs/1801.08260>.
- Pirola--Schlesinger prove full symmetric monodromy for general linear projections of projective
  curves.  The horizon map is a fixed mixed-coordinate projection of an exact reciprocal graph,
  so their uniform-position theorem does not state this result:
  <https://arxiv.org/abs/math/0312375>.
- Gorbounov--Korff's equivariant Grassmannian Bethe theory supplies the classical pure
  `m`-subset/Bethe-vector comparison and an `S_L` action.  The theorem here proves that arbitrary
  reciprocal tails unfold beyond that action to `S_(choose(L,m))`:
  <https://arxiv.org/abs/1402.2907>.

## RH impact

For zeta, every finite critical horizon cover has generic full symmetric monodromy.  This is a
useful no-go: no state or subset label built solely from the universal reciprocal horizon geometry
can carry an RH orientation, and no finite-tail rational formula can select a preferred
reconstruction sheet.  Any RH-relevant reduction of monodromy must come from the Euler source,
functional equation, an infinite-depth limit, or a real/positive structure absent from the
universal cover.  The theorem does not imply RH.

## Formal verification

`ProjectiveHorizonExactLagrangian.lean` formalizes the perfect reversed coefficient/cotangent
pairing and Lagrangian isotropy underlying `(8)`.
`ProjectiveHorizonRamificationUniqueness.lean` formalizes the decisive impossibility in
`(11)--(13)` as `criticalHorizon_sharedConormal_displacement_eq_zero`.
`ProjectiveHorizonCriticalMultiplicity.lean` supplies the trailing-degree contradiction and the
degree `(3)`; its strongest truncation theorem derives the second factor's nonzeroness directly
from the marked nonzero coefficient.  The Schur irreducibility, generic conormal geometry, etale-cover classification, and
permutation-group closure are paper-level.

Only targeted leaf checks are used; no full build is run.
