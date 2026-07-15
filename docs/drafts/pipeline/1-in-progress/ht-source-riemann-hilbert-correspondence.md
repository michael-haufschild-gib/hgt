# A source Riemann--Hilbert correspondence for hypertranscendental constraints

- **ID:** `ht-source-riemann-hilbert-correspondence`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL HT CONJECTURE / ALGEBRAIC--ANALYTIC COMPARISON THEORY
- **Scientific status:** `[CONJECTURE] [PARAMETERIZED GALOIS PARENT IDENTIFIED] [ANALYTIC COMPARISON OPEN] [NOVELTY OPEN]`
- **Parents:**
  - `constraint-curvature-integration-stack.md`
  - `constraint-linearization-gerbe.md`
  - `hypertranscendental-source-mobility-profile.md`
- **Statement:** The algebraic prolongation tower of a constrained HT source and its analytic
  anomaly-colligation stack should be two opposite-variance realizations of one source constraint
  object. Their comparison torsor is the proposed rigorous interval between finite algebraic
  observables and the global source boundary.

## What parameterized difference Galois theory already explains

A rank-`r` shift, `q`-difference, or Mahler module is a finite source constraint. Its parameterized
Picard--Vessiot group is a differential algebraic group whose differential dimension measures the
differential-algebraic relations among its solutions. Gamma's rank-one shift equation can have a
solution with maximal differential transcendence.

Therefore the coexistence

```text
finite-rank functional constraint + infinite differential capacity          (1)
```

is not by itself new. In the linear difference setting it is part of parameterized difference
Galois theory. Likewise, analytic connection matrices, monodromy, and Riemann--Hilbert problems for
important classes of difference and `q`-difference systems are parent theory.

The parameterized Galois group alone does not canonically choose the source test-space topology,
affine normalization, closed operator domains, Hermitian orientation, or positivity realization
needed by the obstruction chains in this project.

## Algebraic clock realization

Let `M_x` be a finite-rank source constraint module with derivation `delta` and nonlocal operator
`sigma`. Let `M_x^(N)` be its `N`-th differential prolongation. Its algebraic solution fiber
functor is

```text
omega_alg,N : <M_x^(N)> -> Vec_F.                          (2)
```

Write `G_x^(N)` for its algebraic Galois group and `G_x^delta` for the parameterized differential
Galois group.

The finite clock capacity of a solution should be read from the orbit/prolongation dimensions of
`G_x^(N)`. In regular Picard--Vessiot settings, equality of differential transcendence degree and
Galois-group differential dimension is parent theory.

**[CONJECTURE — CLOCK/GALOIS IDENTIFICATION]** For a source-minimal constrained function, the
intrinsic algebraic clock-capacity filtration agrees with the dimension filtration of the minimal
parameterized constraint groupoid, including in nonlinear functional-equation settings after
replacing groups by the correct differential-algebraic groupoid.

**Falsifier.** Two source-minimal presentations with the same deformation problem produce
different capacity filtrations after passage to their minimal Galois groupoids.

## Analytic source realization

The same source constraint has an analytic realization retaining:

1. its source domain and continuation site;
2. its calibrated finite-shadow curvature;
3. its admissible completions and operator domains;
4. its linearization gerbe and period/deck lattice;
5. reflection and Hermitian orientation.

Denote the corresponding fiber functor or nonlinear realization functor by

```text
omega_an : C_x -> SourceTop.                               (3)
```

Its moduli of global integrations is the stack `I_x` from the parent card.

## The comparison torsor

In the linear neutral setting, the formal model is the tensor-isomorphism torsor

```text
P_x=Isom^tensor(omega_alg,omega_an).                        (4)
```

In nonlinear or nonneutral settings, `(4)` must be replaced by a derived comparison groupoid. It
must retain clock filtration, affine calibration, source topology, and reflection.

**[CONJECTURE — HT SOURCE RIEMANN--HILBERT]** There is a natural equivalence between:

1. the analytification of the minimal parameterized source-Galois groupoid of `M_x`; and
2. the automorphism groupoid of its calibrated curvature-integration stack.

Under this equivalence, `(4)` is the moduli object of source-compatible comparisons. It is
independent of source presentation and functorial under actual morphisms of constraints.

This is not the generic Tannakian fact that two fiber functors have an isomorphism torsor. The open
claim is that an HT source canonically supplies both functors and that the analytic functor carries
exactly the curvature, topology, domains, and orientation erased by the bare differential field.

**Falsifiers.** The analytic automorphism groupoid has a different differential dimension from the
parameterized Galois group; source-equivalent equations yield inequivalent comparison torsors; or
the analytic topology can be changed without changing any data in `(4)`.

## Conjecture I: the common interval is the comparison torsor

**[CONJECTURE — COMPARISON-INTERVAL LAW]** The five obstruction languages are invariants of the
same comparison object:

1. continuation failure is failure to extend a point of `P_x`;
2. monodromy is descent holonomy of `P_x`;
3. boundary-condition ambiguity is nonuniqueness of an analytic extension of `omega_an`;
4. spectral incompleteness is homology of a representation of the derived tangent of `P_x`;
5. positivity failure is absence of a positive real/polarized point in the reflected torsor.

A common determinant or degeneracy set does not establish this law. The comparison functors must
intertwine the source algebra, curvature derivation, period lattice, and reflection.

## Conjecture II: maximal dimension on a thin module

**[CONJECTURE — HT THINNESS]** A regular group-constrained HT function corresponds to a finite-rank
source module or perfect source groupoid whose differential prolongation dimensions grow
maximally, while the analytic comparison torsor has finite source rank and bounded cotangent
amplitude.

This is a representation-theoretic formulation of

```text
infinite algebraic clock capacity concentrated on a thin constraint boundary.   (5)
```

The finite rank and maximal differential dimension are independent invariants. Hypertranscendence
asserts the second; a source functional equation supplies the first.

**[CONJECTURE — DIMENSION/CURVATURE MATCH]** The leading Kolchin dimension data of the algebraic
side equals an intrinsic growth invariant of the analytic clock-curvature field. This equality is
the first quantitative theorem required from the correspondence.

**Falsifier.** Gamma or another rank-one HT difference module has maximal Galois dimension but an
analytic curvature-growth invariant incompatible with it under every source calibration.

## Conjecture III: self-dual polarized comparison

Suppose reflection sends `M_s` to the dual of `M_(s^vee)` and acts on both fiber functors.

**[CONJECTURE — POLARIZED HT COMPARISON]** The comparison torsor carries a source-defined real or
Hermitian polarization whose degeneracy is the nontransversality of the self-dual analytic
integration stack. Reflection explains paired symmetry; positivity of the comparison point is a
separate analytic theorem.

The general existence of polarizations in Tannakian categories is not the claim. The polarization
must be forced by the original source constraint and agree with the closed-domain/positivity
realizations, not added after a spectrum is known.

## Solvable model program

### Gamma

Use the rank-one shift module `sigma(y)=z y`. Construct:

1. its parameterized algebraic solution torsor;
2. its analytic normalized solution fiber;
3. the logarithmic period cocycle;
4. the rank-one clock-curvature field;
5. a comparison proving that the analytic integration stack is contractible after normalization.

Gamma should prove the correspondence in the integrable abelian phase. Its hypertranscendence is
parent input, not the new theorem.

A point value alone does not rigidify the analytic fiber: solutions differ by nonzero period-one
multipliers. The uncalibrated analytic integration object is therefore a periodic-gauge torsor, not
a point. The project already Lean-formalizes both the generic same-constraint ratio theorem and the
positive source-selection mechanism: for the additive digamma cocycle, a common logarithmic
asymptotic kills the entire periodic ambiguity and selects the explicit source uniquely on the
right half-plane. The comparison theorem must identify the algebraic periodic automorphism torsor
with this analytic torsor and carry asymptotic calibration to a single comparison point.

The finite comparison now has a concrete exact shape. Analytic Taylor translation `E_N` is
Ind-flat with outgoing factorial boundary transfer. Algebraic coordinate-multiplication
prolongation `Z_N(z)` is Pro-flat with incoming Leibniz boundary transfer. Both halves are
Lean-formalized. Their paper-proved finite Weyl seam is

```text
E_N Z_N(z)-Z_N(z+1)E_N=-N v_N tensor top_N.               (6)
```

The incoming/outgoing channel product cancels the old level's defect and pushes `(6)` entirely to
the newest boundary. The first comparison theorem should identify this migrating boundary current
with the extension class of the parameterized difference module's analytic realization. This is
strictly more concrete than comparing a bare Galois group to a chosen curvature stack.

The general old-block conservation law is now Lean-formalized:

```text
p R_(N+1)i=R_N+kappa_an,N gamma_alg,N.                    (7)
```

Hence every proposed comparison torsor has a mandatory finite skeleton: its algebraic and analytic
realizations must induce the same boundary current satisfying `(7)`.

### Böttcher

Use the minimal difference-algebraic groupoid of a nonexceptional Böttcher coordinate. Local
logarithmic linearization moves polynomial nonlinearity into deck holonomy. The comparison theorem
must identify that deck class with the analytic realization of the algebraic groupoid.

Böttcher tests nontrivial holonomy, not genuinely higher minimal curvature.

### Beyond abelianization

A third source must have a minimal nonlinear groupoid that cannot be killed by a source logarithm.
Only then can the nonlinear correspondence and higher curvature be tested.

## RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** A zeta source category would have to be constructed from the
prime and archimedean constraint algebra before the divisor. Prime, continuation, Calkin,
nonclosable, boundary, monodromy, and positivity constructions would count as one object only if
they are representations of a single polarized comparison torsor.

The critical zeros would be fixed-locus degeneracies of its self-dual analytic realization. No
zeta function, completed xi function, zero set, or zero-indexed operator may define the algebraic
or analytic fiber functor. No such torsor has yet been constructed.

## Collision boundary

- Parameterized Picard--Vessiot theory already measures differential relations and proves many
  hypertranscendence results.
- Difference Riemann--Hilbert, connection matrices, monodromy, and Stokes data are parent theory in
  established classes.
- Tannakian comparison torsors and period torsors are parent language.
- The new residue can only be the source-canonical enhanced correspondence retaining clock
  filtration, topology, domain, curvature, affine calibration, reflection, and positivity, plus a
  proof that distinct obstruction chains preserve it.

## Gates

- [x] parameterized difference Galois theory identified as parent of `(1)`
- [x] bare Galois group rejected as the full analytic boundary object
- [x] algebraic and analytic realization functors separated
- [x] Gamma algebraic incoming and analytic outgoing finite boundary channels Lean-formalized
- [x] Gamma finite Weyl seam and charge-migration law paper-proved
- [x] general opposite-variance seam conservation Lean-formalized
- [x] Gamma/digamma analytic periodic torsor and asymptotic source selection identified from
  existing Lean-formalized theorems
- [ ] Gamma finite Weyl seam formalized in Lean
- [ ] Gamma algebraic solution torsor constructed in the project language
- [ ] Gamma analytic integration torsor constructed
- [ ] Gamma comparison equivalence proved
- [ ] clock/Galois dimension equality proved at every finite prolongation for Gamma
- [ ] Böttcher minimal groupoid constructed
- [ ] Böttcher deck class identified under comparison
- [ ] one nonabelian nonlinear source treated
- [ ] dimension/curvature match proved in two classes
- [ ] reflected polarization constructed in a non-RH parameter family
- [ ] two different analytic obstruction chains proved to be representations of one torsor
- [ ] independent novelty and significance audit
