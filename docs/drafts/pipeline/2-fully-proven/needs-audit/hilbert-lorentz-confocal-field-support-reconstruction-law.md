# Hilbert--Lorentz confocal field/support reconstruction law

- **ID:** `hilbert-lorentz-confocal-field-support-reconstruction-law`
- **Stage:** 2-fully-proven
- **Type:** MASTER THEOREM / INVERSE GEOMETRY / LORENTZ CONES / CONFOCAL ENVELOPES
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Statement:** On every nonzero real inner-product space, the complete all-direction,
  all-positive-radius confocal envelope field of a bounded Lorentz source, its causal support
  function, and its maximal Lorentz hull determine one another exactly.  The nonlinear field is
  the greatest causal-contact root of the linear support function; its only multiple-root locus is
  a single positive null ray, where an exact finite-radius fold occurs.

## Scientific delta

The previous scalar result treated one axial quotient `(x,a)` of a source.  The master theorem
varies the axis through an arbitrary real inner-product space and proves that the resulting field
recovers the **entire causal support function**, not merely one support slice.  Consequently it
recovers the maximal Lorentz hull in any finite or infinite dimension.

This is one theorem with three equivalent representations:

```text
nonlinear all-radius confocal field
        <-> causal support function on the self-dual Lorentz cone
        <-> maximal Lorentz half-space hull.                         (0)
```

The scalar fixed-point law is the exact fiber lemma.  It is paper-proved in
`../2-fully-proven/needs-audit/global-confocal-support-transform-bifurcation-law.md`.

## Setup

Let `V` be a nonzero real inner-product space and let

```text
L(V)={(y,a) in V x R: ||y||<=a}                                  (1)
```

be its Lorentz cone.  Let `S` be a nonempty subset of `L(V)` and assume that
`a<=M` on `S`, where `M>=0`.

For a unit vector `e in V` and `R>0`, define the branch, envelope, and defect

```text
b_q(e,R)=a+sqrt(R^2-2R<e,y>+a^2),
G_S(e,R)=sup_(q in S) b_q(e,R),
D_S(e,R)=G_S(e,R)-R.                                          (2)
```

On the dual Lorentz cone, which is canonically another copy of `L(V)`, define the causal support
function

```text
H_S(z,t)=sup_((y,a) in S) [<z,y>+t a],       ||z||<=t.          (3)
```

For a unit `e` and `0<=lambda<=1`, put

```text
h_(S,e)(lambda)
  =H_S(-(1-lambda)e,1+lambda)
  =sup_((y,a) in S)
     [(a-<e,y>)+lambda(a+<e,y>)],                              (4)

lambda_R(d)=d/(2R+d),
rho_(S,e)(lambda)=((1-lambda)/(2lambda))h_(S,e)(lambda)         (5)
```

for `0<lambda<1` in the last expression.

Finally define two hulls:

```text
K_H(S)={q in L(V):
          <z,y_q>+t a_q<=H_S(z,t) for every (z,t) in L(V)},     (6)

K_G(S)={q in L(V):
          b_q(e,R)<=G_S(e,R) for every unit e and every R>0}.   (7)
```

## Master theorem `[PAPER-PROVED]`

For every source above, the following hold.

### A. Global causal-contact selection

For every unit `e` and every `R>0`, the defect is the greatest nonnegative solution of

```text
d=h_(S,e)(lambda_R(d)).                                      (8)
```

Equivalently, `G_S(e,R)` is the greatest `g>=R` satisfying the causal support-contact equation

```text
H_S(-R e,g)=(g^2-R^2)/2.                                    (9)
```

There is at most one solution with `g>R`.

The contact identity `(9)` is not merely a bound: the nonlinear confocal level is exactly the
quadratic level at which the causal support hyperplane touches the source hull.

### B. Exact projective graph

For every unit `e`,

```text
{(R,D_S(e,R)):R>0,D_S(e,R)>0}
 =
{(rho_(S,e)(lambda),h_(S,e)(lambda)):
   0<lambda<1,h_(S,e)(lambda)>0}.                            (10)
```

The inverse coordinate is

```text
lambda=D_S(e,R)/(2R+D_S(e,R)).                              (11)
```

Thus the complete positive field graph and the normalized causal support graph are related by an
explicit rational projective transformation, with no exterior-radius assumption.

### C. Complete null-radical classification

For a unit `e`, the following are equivalent:

```text
H_S(-e,1)=0,
h_(S,e)(0)=0,
S subset {(a e,a):a>=0}.                                   (12)
```

Writing `A_S=sup_(q in S)a`, the radical fiber is

```text
h_(S,e)(lambda)=2A_S lambda,
D_S(e,R)=2 max(A_S-R,0),
G_S(e,R)=R+2 max(A_S-R,0).                                 (13)
```

Hence `(9)` has the root `g=R` at every radius and a second root `g=2A_S-R` exactly when
`0<R<A_S`.  The two roots merge at `R=A_S` and only the diagonal root remains thereafter.

If `S` contains a nonzero point, at most one unit direction is radical.  In every nonradical
direction, `(9)` has exactly one solution `g>=R`, and it is strictly greater than `R`.

### D. Full inverse theorem and maximal quotient

For two bounded nonempty Lorentz sources `S,T`, the following are equivalent:

```text
D_S(e,R)=D_T(e,R) for every unit e and R>0,
H_S(z,t)=H_T(z,t) for every (z,t) in L(V),
K_H(S)=K_H(T).                                              (14)
```

Moreover

```text
K_G(S)=K_H(S).                                              (15)
```

Thus the field is injective exactly on the quotient by the causal Lorentz hull.  No compactness,
support attainment, smoothness, finite dimension, or finite source hypothesis is required.

### E. Exterior stable chart and sharp modulus

For `R>M`, the operator in `(8)` is a contraction with modulus `M/R`; hence the selected root is
unique and depends Lipschitz-continuously on the normalized causal support field.  The modulus is
optimal uniformly over all bounded Lorentz sources, already for the singleton null source
`S={(M e,M)}`.

The exterior contraction is therefore the stable chart of the global transform, while clauses
A--D identify its full domain and its exact interior bifurcation.

## Paper proof

### 1. Projection to the scalar Lorentz cone

Fix a unit vector `e` and define

```text
pi_e:V x R -> R x R,
pi_e(y,a)=(<e,y>,a).                                        (16)
```

For `(y,a) in L(V)`, Cauchy--Schwarz gives

```text
|<e,y>|<=||e|| ||y||=||y||<=a,                             (17)
```

so `pi_e(S)` lies in the scalar Lorentz cone.  It is nonempty and its second coordinate is bounded
by `M`.

The scalar lifted branch of `pi_e(q)` is exactly `(2)`:

```text
a+sqrt((R-<e,y>)^2+(a^2-<e,y>^2))
 =a+sqrt(R^2-2R<e,y>+a^2).                                 (18)
```

Likewise its scalar null support is exactly `(4)`.  Therefore every assertion of the scalar global
confocal-support theorem applies to `pi_e(S)` without loss and without an attainment hypothesis.

It follows immediately that `D_S(e,R)` is the greatest nonnegative solution of `(8)`, that positive
solutions are unique, and that the projective graph is `(10)` with inverse `(11)`.

### 2. Causal support-contact equation

Let `g>=R`, set

```text
d=g-R,
lambda=d/(2R+d)=(g-R)/(g+R),
c=(g+R)/2.                                                  (19)
```

Then `c>0` and

```text
c (-(1-lambda)e,1+lambda)=(-R e,g).                        (20)
```

Positive homogeneity of the support function and `(4)` give

```text
H_S(-R e,g)=c h_(S,e)(lambda),
(g^2-R^2)/2=c d.                                           (21)
```

Consequently `(9)` is equivalent to the fixed-point equation `(8)`.  Greatest-root selection and
uniqueness above the diagonal follow from the scalar theorem.  Substituting the realized
`g=G_S(e,R)` proves the exact contact identity.

### 3. Radical equality forces a single null ray

Every source point satisfies

```text
a-<e,y>>=a-||y||>=0.                                      (22)
```

If `H_S(-e,1)=0`, nonemptiness and the least-upper-bound property force equality in `(22)` for
every point.  Hence

```text
a=<e,y><=||y||<=a.                                        (23)
```

All inequalities are equalities.  Since `||e||=1`,

```text
||y-ae||^2=||y||^2-2a<e,y>+a^2=0,                         (24)
```

so `y=ae` and `a>=0`.  Conversely every point `(ae,a)` has zero incoming null coordinate.
This proves `(12)`.

On this ray, `(4)` becomes

```text
h_(S,e)(lambda)=sup_(q in S) 2lambda a=2A_S lambda.        (25)
```

The scalar radical factorization gives `(13)` and the complete root bifurcation.  If two unit axes
`e,f` were radical and `S` contained a nonzero point `(y,a)`, then `y=ae=af` with `a>0`, hence
`e=f`.  This proves the global uniqueness of the radical direction.

If the direction is nonradical, `h_(S,e)(0)>0`; the scalar graph theorem gives positive defect at
every radius and exactly one nonnegative fixed point.  Equation `(21)` transfers this to `(9)`.

### 4. Normalized directions parameterize the full causal cone

Let `(z,t) in L(V)` be nonzero.  Then `t>0`.  If `z=0`, choose any unit `e` and write

```text
(z,t)=(t/2)(0,2)=(t/2)(-(1-1)e,1+1).                      (26)
```

If `z!=0`, put

```text
e=-z/||z||,
r=||z||/t in (0,1],
lambda=(1-r)/(1+r) in [0,1),
c=t/(1+lambda)>0.                                         (27)
```

Then

```text
(z,t)=c (-(1-lambda)e,1+lambda).                           (28)
```

Thus the normalized directions in `(4)`, as `e` and `lambda` vary, are a projective section of
the entire nonzero Lorentz cone.  Positive homogeneity shows that all the slice fields
`h_(S,e)` determine `H_S` everywhere on `L(V)`.

The scalar faithfulness theorem says that `D_S(e,.)` and `h_(S,e)` determine one another for every
fixed unit `e`.  Applying this for all axes and then using `(26)`--`(28)` proves the first two-way
equivalence in `(14)`.

### 5. The causal support hull is exact

By definition, `S subset K_H(S)`.  Hence for every causal direction `w`,

```text
H_S(w)<=H_(K_H(S))(w).                                     (29)
```

The defining half-space inequalities of `K_H(S)` give the reverse inequality.  Thus

```text
H_(K_H(S))=H_S on L(V).                                    (30)
```

It follows that equality of causal support functions is equivalent to equality of the canonical
hulls: one implication is immediate from `(6)`, and the other follows from `(30)`.  This completes
`(14)`.

To prove `(15)`, fix `q=(y,a) in L(V)`.  For every unit `e`, its scalar projection `pi_e(q)` lies
in the scalar null-support hull of `pi_e(S)` exactly when

```text
<-(1-lambda)e,y>+(1+lambda)a<=h_(S,e)(lambda)
```

for every `0<=lambda<=1`.  The scalar hull theorem says this is equivalent to

```text
b_q(e,R)<=G_S(e,R) for every R>0.                           (31)
```

Requiring `(31)` for every unit `e` is membership in `K_G(S)`.  Requiring all normalized support
inequalities is, by `(26)`--`(28)` and positive homogeneity, membership in `K_H(S)`.  Hence the two
hulls coincide.

### 6. Stable exterior chart

For fixed `e`, every outgoing null coordinate satisfies

```text
0<=a+<e,y><=2a<=2M.                                       (32)
```

Therefore `h_(S,e)` is `2M`-Lipschitz in `lambda`.  The projective parameter
`d |-> d/(2R+d)` is `1/(2R)`-Lipschitz on the nonnegative half-line.  Their composition has
modulus `M/R`, which is strictly below one for `R>M`.

For the singleton source `(M e,M)`,

```text
h_(S,e)(lambda)=2M lambda.                                 (33)
```

The derivative-free quotient comparison at `d=0` shows that every proposed nonnegative uniform
modulus strictly below `M/R` fails for some positive `d`.  Thus the modulus is sharp.  The standard
fixed-point perturbation inequality gives the stated exterior stability.

This completes the dependency-closed proof of clauses A--E.

## Hostile proof audit

1. **Infinite dimension.**  The proof uses only Cauchy--Schwarz, norm definiteness, real order
   completeness for bounded suprema, and existence of one unit vector.  No compact unit sphere,
   finite basis, or support attainment occurs.
2. **Dual-cone coverage.**  Equations `(26)`--`(28)` include the axial direction, timelike interior,
   and null boundary.  The zero covector is trivial by homogeneity.
3. **Interior multiple roots.**  The theorem does not suppress them.  The scalar greatest-root
   theorem proves that a second root occurs exactly on a positive null ray and gives its closed
   formula.
4. **Zero source.**  If `S={(0,0)}`, all fields and supports vanish, both hulls are `{(0,0)}`, and
   every direction is radical with `A_S=0`.  The “at most one radical axis” clause explicitly
   assumes a nonzero source point.
5. **Support-hull circularity.**  Equation `(30)` follows from two opposite order inequalities,
   not from an assumed support-function reconstruction theorem.
6. **Physical boundary versus full cone.**  Sources on `a=||y||` give literal two-leg Euclidean
   travel time `||y||+||Re-y||`.  Allowing `a>||y||` is an algebraic Lorentz completion, stated
   explicitly rather than disguised as physical distance.
7. **Exterior contraction.**  It is retained only as a stable chart.  Global invertibility comes
   from projective graph order and radical classification, not from extending a false contraction
   below `R=M`.

The proof survives these attacks and the exact source-level formalization design audit against the
existing scalar confocal corpus.  In particular, the corpus already contains the axial projection
and branch identity; the missing work is the global scalar theorem and the full causal-cone
assembly, not a new analytic assumption.

## External frontier and novelty audit

Classical support-function theory reconstructs a closed convex set from support values in all
linear directions.  Self-duality of the Lorentz cone and projective sections of causal directions
are standard.  Farthest-distance theory studies regularity and farthest-point maps.  Oliker's
reflector theory characterizes compact convex hypersurfaces obtained as intersections of confocal
paraboloids through a focal function.

Those parent theories do not, in the sources checked so far, state the exact all-radius causal
contact equation `(9)`, greatest-root selection, null-ray fold `(13)`, projective graph `(10)`, or
the equivalence of the complete nonlinear field with the causal support hull `(14)`--`(15)` on
arbitrary inner-product spaces.

Closest primary comparisons:

- V. I. Oliker, *A Minkowski-style theorem for focal functions of compact convex reflectors*,
  <https://arxiv.org/abs/math/0612757>.
- P. Bandyopadhyay and S. Dutta, *Farthest points and the farthest distance map*, Bulletin of the
  Australian Mathematical Society 79 (2009), 234--248.
- R. Schneider, *Convex Bodies: The Brunn--Minkowski Theory*, support-function reconstruction.

Exact-formula searches for `(9)`, the rational parameter `(11)`, all-radius confocal/support graph
inversion, and Lorentz null-radical extinction found no matching theorem.  This is not a priority
proof.  Status remains `[NOVELTY UNVERIFIED]` until the proof is formalized and its full citation
ancestry is audited.

## Formalization architecture

1. Generalize the scalar pointwise branch lower bound, projective identity, and sublevel theorem to
   all positive radii.
2. Formalize the scalar greatest-root, positive-graph, radical, transform-faithfulness, and hull
   theorems in one focused module.
3. Define the generic Lorentz cone, axis projection, causal support, and confocal field on a real
   inner-product space.
4. Transfer the scalar theorem through `pi_e` and prove the causal-contact identity.
5. Prove normalized-direction coverage and the field/support/hull equivalence.
6. Reuse the existing exterior contraction and optimal-modulus results; do not duplicate them.

## Gates

- [x] dimension-free Lorentz representation found
- [x] exact causal-contact master equation proved on paper
- [x] normalized directions shown to cover the full causal cone
- [x] radical and zero-source cases classified
- [x] maximal hull equality proved on paper
- [x] first external parent-theory audit completed
- [x] final hostile source-level proof audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] formalize the exact scalar global theorem (`ConfocalGlobalSupportTransform.lean` + `ConfocalGlobalSupportFaithfulness.lean`: greatest-root, projective graph, radical bifurcation, transform faithfulness, maximal-hull identity)
- [ ] formalize the Hilbert--Lorentz master theorem
- [ ] narrow source checks and final module builds
- [ ] axiom audit
- [ ] rewrite the paper around this theorem

## Log

- 2026-07-20 -- The all-radius scalar law was projected back into its natural ambient object.  The
  family of all axes covers a projective section of the complete self-dual Lorentz cone.  This
  yields the exact quadratic causal-contact equation, a dimension-free field/support/hull inverse
  theorem, and a unique null-ray fold.  The scalar theorem is now the fiber lemma rather than the
  paper headline.

## Lean progress

- 2026-07-24 — **Scalar global theorem formalized** (gate `formalize the exact scalar global
  theorem`): the all-radius scalar confocal transform is complete in
  `HTGeometry/ConfocalGlobalSupportTransform.lean` (defect fixed point, greatest/unique selection,
  projective graph equality, radical extinction-bifurcation) and
  `HTGeometry/ConfocalGlobalSupportFaithfulness.lean` (support↔defect faithfulness both directions,
  the maximal-hull identity `K_G = K_h` unconditionally, `globalDefect_eqOn_iff_nullSupport_eqOn`).
- 2026-07-24 — **Dimension-free master theorem core** (`HTGeometry/HilbertLorentzConfocalReconstruction.lean`,
  axioms `[propext, Classical.choice, Quot.sound]`): the scalar theory transfers to any real
  inner-product space through the canonical axial Lorentz lift `z ↦ (⟪z, axis⟫, ‖z‖)`, exactly because
  the axial distance-sum branch equals the lifted Lorentz branch
  (`liftedConfocalBranch_axialLorentzLift`):
  * `axialGlobalEnvelope` / `axialGlobalDefect` — the all-radius axial confocal envelope and defect
    along a unit direction, with bridges `axialGlobalEnvelope_eq_confocalGlobalEnvelope`,
    `axialGlobalDefect_eq_confocalGlobalDefect`.
  * `axialGlobalDefect_eq_nullSupport_fixedPoint` — the **causal-contact master equation**: the
    realized axial defect is a nonnegative fixed point of the one-dimensional null-support operator,
    at every positive radius, in any dimension.
  * `axialGlobalDefect_isGreatest_fixedPoint` — the greatest-root selection, dimension-free.
  **Remaining for gate `formalize the Hilbert--Lorentz master theorem`:** the all-directions causal
  support function and normalized-direction coverage, and the field/support/hull equivalence in `E`
  (each a further transfer of the scalar faithfulness + hull results through the axial lift).
- 2026-07-24 — **Master theorem part A (global causal-contact selection) formalized for general
  Lorentz sources** in `HTGeometry/HilbertLorentzConfocalReconstruction.lean` (axioms `[propext,
  Classical.choice, Quot.sound]`).  The card's actual setup — a bounded source `S ⊆ L(V) = {(y,a) :
  ‖y‖ ≤ a}` with branch `b_q(e,R) = a + sqrt(R² - 2R⟪e,y⟫ + a²)` — is handled by the scalar axial
  projection `(y,a) ↦ (⟪e,y⟫, a)`:
  * `lorentzAxialProjection`, `lorentzAxialProjection_mem_confocalLorentzCone` (`‖e‖=1, ‖y‖≤a ⇒`
    projection lands in the scalar cone), `liftedConfocalBranch_lorentzAxialProjection` (the branch
    `b_q(e,R)` is exactly the scalar lifted branch of the projection).
  * `lorentzAxialEnvelope` / `lorentzAxialDefect` — the all-radius confocal envelope/defect along a
    unit direction.
  * `lorentzAxialDefect_eq_nullSupport_fixedPoint` — the **causal-contact master equation (8)/(9)**:
    the realized defect is a nonnegative fixed point of the one-dimensional null-support operator, at
    every positive radius, in any dimension.
  * `lorentzAxialDefect_isGreatest_fixedPoint` — the greatest-root selection, dimension-free.
  (The earlier `axialGlobal*` theorems are the `a = ‖z‖` null-boundary specialization for sources
  lifted from `E`.)  **Remaining for the master theorem:** the causal support function `H_S` and the
  `h_{S,e}` identity (4), normalized-direction coverage, projective graph (10) per direction, and the
  field/support/hull equivalence (0) with `K_H(S) = K_G(S)` in `L(V)` — each a further transfer of the
  scalar faithfulness/hull results through the axial projection.
- 2026-07-24 — **Master theorem representation (0) formalized per direction** in
  `HTGeometry/HilbertLorentzConfocalReconstruction.lean` (axioms `[propext, Classical.choice,
  Quot.sound]`):
  * `lorentzAxialSupport` — the causal support function `h_{S,e}(λ)` as the scalar null support of the
    axial projection, with `confocalNullFunctional_lorentzAxialProjection` giving its explicit causal
    linear form `(a − ⟪e,y⟫) + λ(a + ⟪e,y⟫)` (equation (4)).
  * `lorentzAxialDefect_eqOn_iff_axialSupport_eqOn` — **field ↔ causal support** along a unit
    direction: equal all-radius defect fields iff equal `h_{·,e}` on `[0,1]`.
  * `lorentzAxial_confocalHull_eq_nullSupportHull` — **field ↔ maximal hull** along a unit direction:
    the all-radius confocal hull of the axial projection equals its causal null-support hull.
  These are the three representations (0) fixed one axis at a time.  **Remaining:** the all-directions
  integration — normalized-direction coverage of the full causal cone and the global
  `K_H(S) = K_G(S)` over all `(z,t) ∈ L(V)` (assembling the per-direction equivalences across the unit
  sphere of `V`).
- 2026-07-24 — **Global causal support + dual-cone coverage** toward the all-directions equivalence,
  in `HTGeometry/HilbertLorentzConfocalReconstruction.lean` (axioms `[propext, Classical.choice,
  Quot.sound]`):
  * `causalSupport` — the global causal support function `H_S(z,t) = sup_{(y,a)∈S}(⟪z,y⟫ + t·a)` on the
    dual Lorentz cone (equation (3)).
  * `lorentzAxialSupport_eq_causalSupport` — **equation (4)**: the per-direction causal support
    `h_{S,e}(λ)` equals `H_S(-(1-λ)e, 1+λ)`, tying the per-axis support to the global one.
  * `exists_axial_of_mem_dualCone` — **dual-cone coverage**: every `(z,t)` with `‖z‖ ≤ t`, `t > 0` is
    a positive multiple of an axial dual point `(-(1-λ)e, 1+λ)` (`‖e‖=1`, `λ∈[0,1]`).
  **Remaining for the global `K_H(S) = K_G(S)`:** the positive-homogeneity of `H_S` (a `sSup`-scaling
  step) and the assembly — with coverage + homogeneity, the per-direction axial constraints extend to
  the full dual cone, giving the all-directions hull equivalence and completing master theorem
  representation (0).
