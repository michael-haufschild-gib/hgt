# A universal constraint-corona object for hypertranscendental sources

- **ID:** `hypertranscendental-constraint-corona-motive`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL UNIFIED-FIELD CONJECTURE / UNIVERSAL REALIZATION THEORY
- **Scientific status:** `[CONJECTURE] [FINITE ANOMALY LAWS LEAN-FORMALIZED] [UNIVERSAL OBJECT OPEN] [NOVELTY UNVERIFIED]`
- **Parents:**
  - `hypertranscendental-source-mobility-profile.md`
  - `clock-descent-anomaly.md`
  - `source-mackey-clock-interval.md`
  - `self-dual-decorated-clock-boundary.md`
- **Statement:** A constrained HT source should determine one universal object in a
  finite-observable quotient of its nonlocal deformation theory. Its topology, lifting-gerbe,
  spectral, positivity, monodromy, and boundary-condition constructions are realization functors
  of that object. The object is not a finite operator and is not defined from a zero set.

## Why a new category is forced

A finite differential-operator category cannot contain the source object of a corona-pure HT
constraint:

1. hypertranscendence removes finite algebraic-differential relations;
2. maximal source mobility makes every exact finite shadow zero;
3. the source tangent is dense in the raw product clock topology;
4. nevertheless the source topology carries a nonzero infinite conormal.

Thus the source constraint is zero under every finite clock realization but nonzero in at least
one faithful nonlocal realization. It belongs in a quotient measuring precisely the failure of
finite observables to be conservative.

## Constraint presentations

Let `Src_x` be a category of independently given nonlocal source constraints selecting `x`:
translations, dilations, substitutions, reflections, boundary relations, arithmetic products, or
other constraint operations are allowed, but no hidden evolution parameter is installed.

Linearization at `x` sends a source presentation to:

```text
(V_x,S_x; q_N:V_x->O_N; T_N:O_N->O_N;
 alpha_N=T_N q_N-q_N S_x).                               (1)
```

Compatible finite observations and shadows force the `alpha_N` to be coherent. In the
maximal-mobility case their range on source solutions is the whole range of `T_N`. These facts are
Lean-formalized.

Two presentations are equivalent only when they induce equivalent deformation functors and carry
the same coherent anomaly, affine calibration, and global conormal class. Adding an arbitrary
normalization is not an equivalence.

## Universal property `[CONJECTURE]`

For every admissible exact or topological realization category `R`, let

```text
Anom_x(R)                                                   (2)
```

be the groupoid of source-compatible coherent descent anomalies in `R`, modulo anomalies factoring
through finite mobility defects. Pullback along faithful realization functors makes `(2)`
functorial in `R`.

**[CONJECTURE — CORONA REPRESENTABILITY]** There exists an object `M_x`, unique up to canonical
equivalence, such that

```text
Hom(M_x,R)  ~=  Anom_x(R)                                 (3)
```

naturally in every admissible realization `R`. Here `(3)` is schematic: the left side denotes
realizations of `M_x` in `R`, not morphisms to the category itself. A precise 2-categorical or
stable-infinity-categorical formulation is part of the open core.

Call `M_x` the **HT constraint-corona object**. For a corona-pure source:

```text
every finite clock realization of M_x is zero,
but at least one source realization of M_x is nonzero.     (4)
```

Property `(4)`, plus the universal property `(3)`, prevents `M_x` from being a renamed operator,
determinant, zero divisor, or freely generated formal object.

## Self-duality `[CONJECTURE]`

If the source constraint has an anti-linear reflection `J`, it should induce a duality `D` on the
realization theory and a source-defined equivalence

```text
eta_x : M_x ~= D(M_x),                                    (5)
```

with the expected bidual coherence. Reflection symmetry alone gives `(5)`; it does not give
positivity or fixed-locus degeneracy.

The pair `(M_x,eta_x)` is the proposed unified field object. It is a constraint object with
multiple observables, not a state evolving in time.

## The lifting-gerbe realization

In a rigged-dual realization, finite covectors and source-continuous covectors form an exact
sequence

```text
0 -> I_x -> Phi_x' -> C_x -> 0.                           (6)
```

The conormal part of `M_x` gives a line or perfect complex in the corona `C_x`. The groupoid of
local lifts through `(6)` is a source-defined lifting gerbe.

**[CONJECTURE — FIVE-REALIZATION LAW]** When the conormal component is perfect and self-dual, the
following are functorial faces of this one lifting object:

1. **continuation failure:** obstruction to extending a local lift;
2. **monodromy:** the Cech cocycle or determinant holonomy of the lift groupoid;
3. **boundary-condition ambiguity:** the torsor of inequivalent lifts;
4. **positivity failure:** obstruction to a `J`-real positively oriented lift;
5. **spectral incompleteness:** homology or nontransversality of the lifted self-dual comparison
   complex.

The first three follow the shape of standard descent theory once `(6)` is supplied. The hard new
claim is that source-derived spectral and positivity constructions factor through the same class,
not merely analogous gerbes.

## Common degeneracy spectrum `[CONJECTURE]`

For a parameterized source, suppose a realization of `(M_x,eta_x)` is perfect enough to have a
support theory and determinant section derived before examining its zeros. Define

```text
Sigma_x = support of the self-dual realization of M_x.     (7)
```

The spectrum is **common** only when every claimed obstruction chain is the image of `(7)` under a
faithful realization functor preserving `(5)`. Coincidence of scalar zero sets is not evidence.

Fixed points of the anti-linear reflection give the self-dual part of `Sigma_x`; nonfixed points
occur in reflected pairs. Self-duality therefore explains symmetry of a spectrum, not confinement
to the fixed locus.

## Gamma realization

The period-one Gamma/digamma source supplies the first nonzero model data:

- `S h=h(.+1)-h`;
- arbitrary finite jets on `ker(S)` via periodic Fourier packets;
- a nonzero infinite Taylor conormal;
- a formal shift cofactor which is a unit locally but a global source nonunit;
- a reflected global divisor;
- a coherent finite descent anomaly and forced source-topology enlargement.

**[CONJECTURE]** These data represent a nonzero rank-one `M_Gamma`. Its Mackey interval is one
topological realization; its formal/global unit defect is one symbol realization; its conormal
lift through `(6)` is one gerbe realization. Constructing `M_Gamma` and proving these universal
identifications is the first theorem target.

### The linear-register slice of `M_Gamma` is Lean-proven

`formal/GaloisForLFunctions/HTGeometry/GammaClockCoronaConormal.lean` constructs the corona
carrier of the Gamma-clock conormal in the linear category, unconditionally
(axioms `[propext, Classical.choice, Quot.sound]` only):

- `streamCoronaSource_adjoint`: the stream constraint `sigma = prepend_0 - id` is the exact
  adjoint of the clock source `S h = h(.+1) - h` under the finite clock pairing — the object is
  source-defined, not freely constructed;
- `streamCoronaSource_injective`: **no exact conormal carrier exists** — the raw dual constraint
  is injective;
- `ker_streamCoronaConstraint` and `coronaClass_const_ne_zero`: modulo the ideal of finitely
  observable covectors, the descended corona constraint has kernel **exactly one nonzero line**,
  spanned by the class of the constant stream — the predicted rank-one `M_Gamma` appears as a
  forced kernel, with the predicted rank;
- `windowSupported_mem_eventuallyZeroStream`, `coronaClass_eq_zero_of_windowSupported`: every
  finite clock window kills the class — the linear register of `(4)`;
- `finiteBlind_realization_factors_uniquely`, `conormal_transport`: the corona quotient is the
  universal finite-blind realization, and every intertwining realization transports the constant
  stream into its shadow kernel — the linear skeleton of representability `(3)`.

This slice proves the dichotomy `(4)` and the representability shape `(3)` at the 1-categorical
linear level for the Gamma source.  The open core above this slice: the presentation
2-category, invariance under change of presentation, the groupoid (not vector-space) anomaly
functor, and the self-duality `(5)`.

## RH-chain speculation `[CONJECTURE; NOT AN RH RESULT]`

A completed-zeta source would need to produce `M_zeta` from prime and archimedean constraints,
independently of `xi`, a zero table, or a zero-indexed operator. The different RH chains would then
be candidate realizations of `M_zeta`:

- Sonin/Calkin: quotient-kernel realization;
- Hedenmalm: nonclosable positive-topology realization;
- Böttcher/Pruefer: monodromy realization, presently lacking the source comparison map;
- continuation chains: localization/lift realization;
- semilocal boundary chains: extension-torsor realization.

The critical zeros would be the fixed-locus part of `Sigma_zeta`. This is a research hypothesis,
not an RH result, and it makes no assertion that all degeneracies lie on the fixed locus.

## Parent-theory attack

- Freely constructing a category with a representing object is mathematical theatre. `M_x` counts
  only if it is forced by the source deformation functor and proved nonzero by a source invariant.
- Motives, Verdier quotients, derived cotangent complexes, determinant gerbes, and realization
  functors are established parent languages. None is the discovery.
- A generic exact sequence like `(6)` already unifies continuation, Cech monodromy, and lift
  torsors. The spectral and positivity factorizations are the nonroutine obligations.
- The object cannot depend on a chosen source presentation. Presentation invariance is an open
  core, not a cosmetic coherence lemma.
- A self-dual object can have off-fixed degeneracies. Any RH conclusion requires an independent
  orientation or positivity theorem and is outside this card.

The candidate-new residue is the existence and source-presentation invariance of a nonzero object
satisfying `(3)`--`(5)` for corona-pure HT sources, together with one proved five-realization law.

## Gates

- [x] finite operator carrier killed
- [x] raw product-topology carrier killed
- [x] coherent anomaly and quotient laws Lean-formalized
- [x] source mobility separated from ambient hypertranscendence
- [x] lifting-gerbe realization conjectured with five exact proof obligations
- [ ] admissible source-presentation 2-category defined
- [ ] finite-mobility localization defined without collapsing the source object
- [x] corona representability `(3)` proved for Gamma in the linear register: the corona quotient
  is the universal finite-blind realization and the conormal transports functorially
  (`GammaClockCoronaConormal.lean`); the 2-categorical groupoid form remains open
- [x] nontriviality `(4)` proved in the linear register: no exact conormal carrier, every finite
  window kills the class, the corona kernel is one nonzero line; the categorical
  (realization-independent) form remains open
- [ ] source-presentation invariance proved
- [ ] coherent self-duality `(5)` constructed
- [ ] two non-equivalent realizations of `M_Gamma` proved identical
- [ ] one non-Gamma corona-pure HT source constructed
- [ ] one genuine spectral/positivity/monodromy factorization theorem proved
- [ ] independent novelty/significance audit
