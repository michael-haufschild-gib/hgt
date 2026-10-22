# The source-transgression field of a constrained hypertranscendental function

- **ID:** `source-transgression-field`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL HT CONJECTURE / CALIBRATED DERIVED BOUNDARY FIELD
- **Scientific status:** `[RAW FINITE-DIMENSIONAL LIM1 CARRIER KILLED] [CURVATURE DERIVATION LAW LEAN-FORMALIZED] [SUCCESSOR: constraint-curvature-integration-stack]`
- **Parents:**
  - `calibrated-clock-curvature-class.md`
  - `hypertranscendental-constraint-corona-motive.md`
  - `self-dual-decorated-clock-boundary.md`
- **Statement:** Hypertranscendence supplies unbounded algebraic clock capacity. A nonlocal source
  constraint supplies a canonical transgression into the derived obstruction to choosing its
  calibrated finite shadows coherently. The source-generated image of this transgression, rather
  than the whole formal-completion defect, is the proposed thin boundary field.

## Two independent axes

Let `F` be a differential field and `x` a source point. Define its algebraic clock capacity by

```text
c_x(N)=trdeg_F F(x,delta x,...,delta^N x).                 (1)
```

Hypertranscendence is maximal capacity:

```text
c_x(N)=N+1 for every N.                                   (2)
```

Equation `(2)` concerns the algebraic independence of observables. It does not say that the
tangent space of a chosen source presentation realizes every finite jet. Source mobility and
algebraic clock capacity are independent axes.

For a nonlocal source constraint `C`, let `S_N(C,x)` be the affine space of its finite
`N`-clock shadows satisfying all source-imposed finite data:

1. the principal clock symbol induced by `C`;
2. the affine normalization selecting `x` rather than an untranslated tangent;
3. the reflection law, when the source has one;
4. any declared source-local boundary value.

Differences of points of `S_N(C,x)` form a gauge module `G_N(C,x)`. These are precisely the
symbol-zero, normalization-zero corrections; the zero shadow is not admissible unless the source
symbol itself is zero.

## The raw transgression class and its terminal obstruction

Choose one calibrated shadow `T_N` at each finite resolution. Truncation need not carry `T_(N+1)`
to `T_N`. Its mismatch is

```text
kappa_N=p_N T_(N+1)-T_N p_N.                              (3)
```

After identifying `(3)` with the appropriate invisible gauge module, changing the calibrated
shadows changes `kappa` by a gauge coboundary. Hence the tower of calibrated-shadow torsors should
define a class

```text
tau_x(C)=[kappa(C,x)] in lim^1_N G_N(C,x).                 (4)
```

The use of `lim^1` and the obstruction class of a tower of torsors are standard homological
algebra. Low rank of `(3)` is also classical displacement structure. Neither is new scientific
knowledge. More decisively, when the `G_N` are finite-dimensional linear gauge spaces, their
transition images stabilize at every fixed level. The tower is Mittag--Leffler and `(4)` vanishes.
Thus `(4)` cannot be the general nonzero finite-clock boundary field.

The positive successor retains the source curvature and replaces `(4)` by its derived integration
fiber. It is developed in `constraint-curvature-integration-stack.md`. The earlier proposed object
was the source-marked transgression morphism

```text
tau_x : P_x -> lim^1_N G_N(x),                            (5)
```

where `P_x` is the minimal perfect complex of independently given source constraints. Define the
**source-transgression field** by

```text
B_x=im(tau_x),                                            (6)
```

with its clock filtration, affine calibration, constraint-algebra action, and reflection. The
whole completion cokernel is deliberately excluded: it is generally huge and already occurs for
ordinary analytic function spaces.

## Conjecture I: source-transgression existence and invariance

**[CONJECTURE — SOURCE TRANSGRESSION]** Every regular nonlocal constraint presentation of `x`
constructs `(5)` canonically. A quasi-equivalence of source deformation problems induces an
isomorphism of transgression fields carrying `tau_x` to `tau_x'`.

This is stronger than invariance under a change of finite clock basis. It says that replacing a
functional equation by a genuinely equivalent constraint resolution leaves `(5)` unchanged,
whereas adding an independent normalization or a new source equation is allowed to change it.

**Falsifier.** Two equivalent presentations of Gamma's shift constraint produce inequivalent
classes after all symbol, affine, and reflection data are transported.

## Conjecture II: thin concentration

**[CONJECTURE — THIN CONCENTRATION]** For a source-minimal regular constrained HT point, `P_x` is
perfect of finite rank and `B_x` is a nonzero finite-constraint-rank object even though `(1)` is
unbounded. This is the precise proposed meaning of

```text
hypertranscendence = infinite algebraic clock capacity
                     concentrated on a thin constraint boundary.    (7)
```

Thinness is rank relative to the source-constraint complex, not finite dimension of the ambient
completion corona and not low displacement rank alone.

**[CONJECTURE — GAMMA ONE-FIELD]** The period-one Gamma/digamma shift has a one-dimensional
source-transgression field. Its rank-one clock curvature and infinite Taylor conormal are two
realizations of the same generator.

**Falsifier.** The Gamma curvature class becomes zero after imposing its actual source symbol and
affine calibration, or two independent calibrated generators survive.

## Conjecture III: the constraint algebra acts through a curvature derivation

For composable finite source shadows, the exact algebraic law is

```text
kappa(T U)=kappa(T) U_+ + T_- kappa(U).                   (8)
```

Gauge addition is also exact:

```text
kappa(T+g)=kappa(T)+kappa(g).                             (9)
```

Both laws are Lean-formalized. They show that curvature is a derivation from the algebra of finite
source operations into a boundary bimodule.

**[CONJECTURE — CALIBRATED DERIVATION]** Equation `(8)` descends to `(5)`, making `tau_x` a
presentation-invariant derived derivation of the complete source-constraint algebra. The field is
therefore not one operator or one cohomology class: it is the smallest calibrated bimodule on
which the whole source algebra has nonzero curvature.

**Falsifier.** Composition of two source-equivalent constraints changes the transgression by a
term that is not a calibrated coboundary, or the descended derivation is inner after preserving
the source symbol and affine section.

## Linear reconstruction no-go and nonlinear upgrade

The unary field `(B_x,tau_x)` cannot reconstruct a nonlinear source constraint. Distinct analytic
constraint germs can have the same derivative at `x`, hence the same tangent deformation problem
and unary transgression, while differing at quadratic or higher order. This kills the linear
reconstruction proposal in its strong form.

The positive replacement uses the complete source Taylor hierarchy. For an analytic constraint
map, every homogeneous derivative should have a source-calibrated transgression

```text
tau_x^(m) : Sym^m(T_x) -> lim^1_N G_N^(m)(x),  m>=1.     (10)
```

Write

```text
bold_tau_x(h)=sum_(m>=1) tau_x^(m)(h,...,h)/m!.           (11)
```

**[CONJECTURE — HIGHER SOURCE TRANSGRESSION]** In a characteristic-zero analytic or formal-moduli
source category, the hierarchy `(10)` carries the higher coherence operations induced by source
syzygies. After transfer to the minimal model it is a calibrated curved `L_infinity`-type boundary
field whose Maurer--Cartan deformation functor is equivalent to the original source deformation
functor.

**[CONJECTURE — NONLINEAR SOURCE RECONSTRUCTION]** For source-minimal regular analytic constraints,
the package

```text
(clock-capacity filtration, affine calibration,
 source-algebra action, {tau_x^(m)}_(m>=1))               (12)
```

determines the nonlocal source germ up to analytic presentation equivalence.

Formal-moduli problems and `L_infinity` transfer are parent theory. The candidate-new claim is
that a constrained HT source canonically places all higher operations in one thin
finite-observable corona and that this corona model is presentation invariant.

**Falsifiers.** An analytic source equivalence fails to transport the complete hierarchy; the
higher classes depend on arbitrary finite-shadow representatives; or two inequivalent analytic
source germs have isomorphic complete packages `(12)`.

Gamma's shift equation is an abelian rank-one test because its tangent constraint is linear. A raw
Böttcher power constraint has higher Taylor layers, but a local logarithm linearizes them and moves
their content into a period-lattice cocycle. Therefore Böttcher tests curvature--holonomy transfer,
not intrinsic higher minimal curvature. A genuinely non-linearizable source is required to test
`tau^(2)` in the minimal model.

## Conjecture V: effectiveness dichotomy

**[CONJECTURE — EFFECTIVENESS]** The class `tau_x(C)` vanishes exactly when the calibrated finite
shadows can be gauge-corrected to one compatible global shadow in the source category. Thus

```text
tau_x(C)=0  <=>  C is clock-effective,
tau_x(C)!=0 <=>  C is intrinsically corona-supported.    (13)
```

The abstract torsor implication is parent obstruction theory. The new obligation is to prove that
the source category and calibration are canonical and that its compatible point really is a
global source operation, not merely a formal pro-operator.

**Positive no-go.** If the gauge tower is Mittag--Leffler, `(4)` vanishes. Such a constraint is not
a failed HT object; it belongs to the positive **clock-effective phase**, where finite shadows can
be coherently summed. Non-Mittag--Leffler behavior is therefore a necessary test for the proposed
corona phase.

## Conjecture VI: the source topology is reconstructed, not chosen

The raw product topology makes every finitely visible source tangent dense and kills all
continuous linear constraints. Arbitrarily strengthening the topology can manufacture any desired
dual and is equally unacceptable.

**[CONJECTURE — TOPOLOGY RECONSTRUCTION]** There is a minimal complete source topology for which
the clock observations, source-algebra action, affine section, and every element of `B_x` are
continuous. It is invariant under `(12)` and its continuous conormal is generated by the dual of
the source-transgression field.

**Falsifier.** Two incomparable minimal complete topologies realize the same data `(12)`, or the
resulting topology depends on a chosen representative of `tau_x`.

## Conjecture VII: self-dual field and common degeneracy spectrum

Suppose a parameterized source has an anti-linear reflection `J:s -> s^vee`. It should carry the
gauge tower, source algebra, and transgression to their duals.

**[CONJECTURE — SELF-DUAL TRANSGRESSION]** There is a coherent perfect pairing

```text
B_s tensor B_(s^vee) -> L_s[-1]                           (14)
```

to a source-defined orientation line. The **common degeneracy spectrum** is the support where the
pairing of the source-generated transgression fields loses transversality.

This gives the five proposed representations literal meanings:

1. continuation failure is nonvanishing of the sewing obstruction `(4)`;
2. monodromy is holonomy of the calibrated-shadow torsor carrying `(4)`;
3. boundary-condition ambiguity is the torsor of local primitives of `(4)`;
4. spectral incompleteness is homology of a perfect realization of `(14)`;
5. positivity failure is failure to orient the Hermitian fixed part of `(14)` positively.

**[CONJECTURE — FIVE-REALIZATION LAW]** Every valid realization functor carries the same
source-marked `tau_s`, respects `(8)`, and preserves `(14)`. Equality of determinants, spectra, or
abstract operator ideals without these intertwiners is insufficient.

Reflection alone permits off-fixed degeneracies in paired orbits. A separate positive-orientation
theorem is required for fixed-locus confinement.

## RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** A completed-zeta source may have a pre-divisor transgression
field constructed from its prime and archimedean constraint algebra. If Sonin/Calkin,
Hedenmalm/nonclosability, continuation, positivity, and Böttcher/monodromy chains are realizations
of one object, then they must carry one `tau_zeta`, one composition law `(8)`, and one reflected
pairing `(14)`. The critical zeros would be fixed-locus degeneracies of that pairing.

No zeta function, completed xi function, zero set, or zero-indexed operator may be used to define
`tau_zeta`. The current chains have not supplied the required intertwiners, so this is a
falsifiable research hypothesis and not evidence for RH.

## Collision audit

- Countable `lim^1`, towers of torsors, derived completion, and obstruction-to-sewing are parent
  homological algebra.
- Low-rank curvature is low displacement rank; Toeplitz, Hankel, Cauchy, Vandermonde, and related
  finite-section structures already inhabit that theory.
- Atiyah classes, Hochschild derivations, determinant gerbes, boundary triples, and Tate objects
  are parent carriers.
- The full analytic-to-formal completion defect is not HT-specific.
- Nonzero transgression does not by itself imply hypertranscendence: a DA function can be given an
  extra nonlocal constraint. Maximal capacity `(2)` and source minimality are separate mandatory
  hypotheses.
- A generic self-dual perfect complex does not force positivity or a fixed-locus spectrum.

The candidate-new residue is the canonical construction, presentation invariance, reconstruction,
and multi-realization rigidity of the source-marked morphism `(5)` for actual constrained HT
functions.

## Gates

- [x] maximal algebraic clock capacity separated from source mobility
- [x] whole completion corona rejected as non-HT-specific
- [x] low displacement rank identified as parent theory
- [x] curvature gauge-additivity Lean-formalized
- [x] curvature composition/Leibniz law Lean-formalized
- [x] curvature vanishing characterized as finite-shadow compatibility in Lean
- [ ] calibrated-shadow torsors `S_N(C,x)` constructed for Gamma
- [ ] gauge tower `G_N(C,x)` and its transition maps constructed for Gamma
- [ ] nonzero `tau_Gamma` proved
- [ ] Gamma curvature and Taylor conormal proved to carry one generator
- [ ] source-presentation invariance proved for two Gamma presentations
- [x] unary source-reconstruction conjecture killed by nonlinear tangent blindness
- [x] raw Böttcher higher arity rejected as non-invariant under logarithmic source charts
- [ ] higher transgression hierarchy constructed for a genuinely non-linearizable source
- [ ] nonlinear source reconstruction theorem proved in one nontrivial class
- [ ] minimal topology reconstructed from `B_Gamma`
- [ ] self-dual pairing `(12)` constructed for Gamma
- [ ] a second corona-pure HT source constructed
- [ ] two genuinely different realizations proved to preserve one transgression
- [ ] independent novelty and significance audit
