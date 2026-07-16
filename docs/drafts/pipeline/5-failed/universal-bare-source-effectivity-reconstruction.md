# Universal bare-source effectivity reconstruction is false

- **ID:** `universal-bare-source-effectivity-reconstruction`
- **Stage:** 5-failed
- **Type:** UNIVERSAL RECONSTRUCTION NO-GO / MAXIMAL POSITIVE CORRECTION
- **Scientific status:** `[PROVED FALSE AS STATED] [LEAN ANALYTIC WITNESS]`
  `[PARENT PHENOMENON] [NOT AN RH RESULT]`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/GammaPointedSourceNonEffectivity.lean`
  - `formal/GaloisForLFunctions/HTGeometry/JointSourceRealizationConservativity.lean`
  - `formal/GaloisForLFunctions/HTGeometry/DiscretePeriodGaugeClassification.lean`
- **Positive special case:**
  `../2-fully-proven/new_scientific_knowledge/irrational-triptic-source-effectivity-character.md`

## Verdict

The literal universal claim

```text
bare source constraint + one regular pointing
  -> canonical analytic HT germ                            (1)
```

is false.  A source constraint determines a solution torsor.  Reconstruction is possible exactly
on the source-effectively normalized stratum where the normalized joint-fixed gauge is trivial.
The required normalization may be a regular value for a dense rank-three source, but it must be an
asymptotic or positivity condition for rank-one Gamma.  No universal point-value recipe exists.

## Concrete Gamma falsifier

Let

```text
f(z)=Gamma(z),
h(z)=exp(2 pi i z),
g(z)=h(z) Gamma(z).                                       (2)
```

Since `h(z+1)=h(z)`, both meromorphic functions satisfy

```text
f(z+1)=z f(z),
g(z+1)=z g(z).                                             (3)
```

At the common regular point `z_*=1`,

```text
f(1)=g(1)=1.                                               (4)
```

They are nevertheless distinct because `h(1/2)=-1` and `Gamma(1/2) != 0`.

Both regular meromorphic germs are hypertranscendental.  The first is Hölder's theorem.  The gauge
`h` is a nonzero differentially algebraic meromorphic unit.  If `h Gamma` were differentially
algebraic, closure of the differentially algebraic meromorphic field under division by `h` would
make `Gamma` differentially algebraic, a contradiction.  Thus `(2)` is an actual HT-to-HT
collision, not a counterexample outside the intended class.

Lean proves the periodic gauge identity, the common pointed value, non-equality at the half point,
and Hölder hypertranscendence of the untwisted member.  The standard differential-field stability
argument for the twisted member is kept as paper mathematics; it is not inserted as an axiom.
Axiom inspection of the Lean witness reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Every finite jet pointing also fails in rank one

For any `N`, put locally at an integer point `z_*`

```text
h_N(z)=1+(exp(2 pi i (z-z_*))-1)^(N+1).                    (5)
```

Then `h_N` is period one, is a nonzero analytic unit near `z_*`, and

```text
j^N_(z_*) h_N = j^N_(z_*) 1.                              (6)
```

Hence `Gamma` and `h_N Gamma` obey the same source equation and have the same `N`-jet pointing,
yet define different HT germs.  The existing Gamma periodic-corona theorem is stronger at the
additive tangent level: finite Fourier packets realize arbitrary finite jets.  Therefore no fixed
finite-order pointing kills the rank-one periodic gauge.

## Maximal correct theorem

Let `S` act on an analytic differential field `K`, let `b` be a source boundary, and let `nu` be a
normalization.  If `x` is one solution, every other solution has the form `u x` with

```text
u in (K^S)^x.                                              (7)
```

The normalized solution fibre is a torsor under

```text
G_(S,nu)={u in (K^S)^x : nu(u x)=nu(x)}.                   (8)
```

Thus canonical analytic reconstruction and reconstruction of source-preserving morphisms hold
if and only if:

```text
the normalized solution fibre is nonempty,
G_(S,nu)={1}.                                              (9)
```

For an additive family of realization maps, Lean proves the exact joint form

```text
intersection_r ker(R_r) intersection K^S={0}.              (10)
```

Equation `(10)` is necessary and sufficient for the boundary plus all realization values to be
conservative.  A nonzero element of the intersection is an explicit counterexample.

## Two different positive mechanisms

1. **Irrational triptic source.**  Three rationally independent periods generate a nondiscrete
   subgroup.  A global meromorphic function fixed by all three translations is constant.  One
   nonzero regular value kills the remaining scalar.  The pointed fibre is a singleton and the
   elliptic-gamma germ is reconstructed.
2. **Rank-one Gamma source.**  The fixed gauge is the full field of period-one meromorphic
   functions.  One point and every fixed finite jet fail.  An infinite normalization such as
   Bohr--Mollerup convexity or a source-compatible asymptotic condition is required.  The corpus
   already formalizes the analogous asymptotic uniqueness mechanism for the digamma cocycle.

These mechanisms cannot be collapsed into one canonical finite pointing.  The source must carry
or force a gauge-separating normalization.

## Universal period-source strengthening `[PROVED; LEAN-FORMALIZED]`

The Gamma witness is now the rank-one endpoint of a complete theorem. For every integral period
source `L<=C`, Lean proves

```text
L discrete
  <-> complete period incidence has a continuous left inverse
  <-> a nonconstant global meromorphic L-fixed gauge exists,

L nondiscrete
  <-> complete period incidence has no continuous left inverse
  <-> every global meromorphic L-fixed gauge is constant.                 (11)
```

Hence no bare period source is both uniformly effective and gauge-rigid modulo constants.
Discrete sources solve attainment and retain nonconstant automorphisms; nondiscrete sources kill
those automorphisms and lose attainment, with a scalar calibration still needed for uniqueness.
The positive theorem is the exhaustive dichotomy itself: successful reconstruction must add
transverse normalization in the first phase or transverse completion in the second.

This strengthening is a classical bridge, not new science. Its value is to rule out every attempt
to repair the Gamma collision merely by changing period rank or densifying the same source.

## Consequence for the six-channel object

A pointed, polarized, critically completed, transported, integral, unbounded descent object built
only from the bare source cannot choose between `(2)`.  Adding more source-derived realizations
does not repair the information-theoretic collision if all of them are invariant under the same
normalized fixed gauge.  The viable category is therefore not all source-minimal HT constraints;
it is the maximal **source-effectively normalized** subcategory satisfying `(9)` and the typed
analogue of `(10)`.

The irrational triptic construction is a complete positive object on one natural stratum.  A
universal theorem beyond it must first classify which normalizations are forced by the source and
prove their stability under morphisms.  Calling a chosen normalization canonical without that
classification is precisely the circularity the reconstruction program forbids.

## Literature and parent-theory gate

The periodic ambiguity of `f(z+1)=g(z)f(z)` and its removal by convexity or asymptotic conditions
are classical characterization theory, not a new discovery.  Relevant modern primary sources
include:

- Hooshmand, *Remarks on the functional equation `f(x+1)=g(x)f(x)` and a uniqueness theorem for
  the gamma function*, `https://arxiv.org/abs/2110.00040`;
- Marichal--Zenaidi, *A Generalization of Bohr--Mollerup's Theorem for Higher Order Convex
  Functions*, `https://arxiv.org/abs/2009.14742`;
- Adamczewski--Dreyfus--Hardouin, *Hypertranscendence and linear difference equations*,
  `https://arxiv.org/abs/1910.01874`.

The common-kernel criterion is parent algebra.  The candidate-new residue remains an HT-specific
classification of the maximal source-effectively normalized essential image together with a new
analytic theorem transferred across its genuinely different realizations.

## Anti-theatre and novelty gate

- `[ANTI-THEATRE -- PASS]` The universal wording is retired after an explicit HT collision; no
  amount of added categorical vocabulary is allowed to conceal the fixed gauge.
- `[NOVELTY -- PARENT NO-GO]` Periodic ambiguity and kernel separation are not new science.
- `[SIGNIFICANCE -- DECISIVE CORRECTION]` The no-go replaces an impossible universal theorem by an
  exact maximality criterion and a complete period-source uncertainty theorem.
- `[FIELDS VERDICT]` Neither the no-go nor the triptic special case alone is Fields-scale.  A
  functorial gauge-to-nonattainment transgression in a natural degenerating HT family could be.
- `[RH BOUNDARY]` No zeta input or RH conclusion occurs.

## Gates

- [x] actual analytic source collision constructed
- [x] common source equation and pointing Lean-formalized
- [x] two distinct HT germs proved on paper
- [x] every fixed finite-jet pointing ruled out
- [x] exact normalized-gauge criterion stated
- [x] additive joint-realization criterion Lean-formalized
- [x] triptic and rank-one effectivity mechanisms separated
- [x] all integral period sources classified into the two exclusive obstruction phases
- [x] parent characterization literature identified
- [ ] construct the gauge/attainment defect complex and wall-crossing map
- [ ] classify source-forced normalizations on a second natural nontriptic HT family
- [ ] prove the nonlinear typed common-kernel theorem for all five realization categories
