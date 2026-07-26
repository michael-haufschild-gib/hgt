# Prime weld affine-exact/bounded-spectral obstruction universality law

- **ID:** `prime-weld-affine-exact-bounded-spectral-obstruction-universality-law`
- **Law:** LAW499
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proof and direct Lean check complete)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
  `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`
- **Target:** `formal/GaloisForLFunctions/RHTower/PrimeWeldAffineExactBoundedSpectralObstructionUniversalityLaw.lean`

## Theorem

For every prime `p`, the affine lift of the prime weld cocycle has a functional-equation-covariant
primitive, but no exact primitive is realizable by bounded operators on the fixed spectral
`L²`-space.  More sharply:

```text
there exists b:
  FE-covariant(b)
  and delta b = weldAffineCocycle(log p);

for every b:
  delta b = weldAffineCocycle(log p)
  implies derivationCoefficient(b, weldGenD) = 1
      and not BoundedSpectralRealization(b).
```

Thus coefficient enlargement kills the algebraic cohomology class, but analytic boundedness
restores the obstruction universally.  Functional-equation covariance does not alter either side:
every exact gauge contains one forced, reflection-odd, unbounded derivation direction.

## Theorem-generated derivation

This law was not predicted and then searched.  Whole-corpus same-folder leaf pairing exposed:

- `WeldAffineTrivialization.prime_exists_FECovariantAffinePrimitive`;
- `WeldAffineTrivialization.weldAffinePrimitive_derivCoeff_eq_one`;
- `WeldBoundedSpectralGauge.prime_no_boundedWeldSpectralPrimitive`;
- `WeldBoundedSpectralGauge.BoundedWeldSpectralCochain.isOrderZero`.

The first theorem supplies an FE-covariant exact primitive.  Since `p` is prime, `log p > 0`, so
the primitive-rigidity theorem applies to every exact cochain and fixes its derivation coefficient
at `1`.  If any such cochain admitted a bounded spectral realization, it would witness the
existential statement prohibited by `prime_no_boundedWeldSpectralPrimitive`.  Therefore every
exact affine trivialization is necessarily spectrally unbounded.

No numerical computation is used.

## Strict corpus delta

`WeldAffineTrivialization` proves algebraic exactness, FE covariance, and forced derivation
coefficient, but does not state that its primitive—or every other exact primitive—is excluded from
the bounded spectral category.  `WeldBoundedSpectralGauge` proves the existential bounded no-go,
but does not retain the simultaneous positive existence theorem or FE covariance.  Their
combination exposes the exact category wall: nonempty FE-covariant algebraic trivializations,
empty bounded-spectral trivializations, and a universal coefficient-`1` unbounded direction.

## Post-proof novelty audit

Performed only after the dependency-closed Lean proof passed.

- Battista--Francaviglia--Moraschini--Sarti--Savini, [*Bounded Cohomology Classes of Exact
  Forms*](https://arxiv.org/abs/2211.16125), shows a related broad phenomenon: algebraically exact
  nonzero forms can define nontrivial bounded-cohomology classes.  It does not treat the weld
  group, prime logarithmic rate, FE-covariant affine coefficient extension, or spectral
  multiplication operator.
- Frigerio--Sisto, [*Central extensions and bounded cohomology*](https://arxiv.org/abs/2003.01146),
  and Fournier-Facio--Löh--Moraschini, [*Bounded cohomology of finitely presented groups:
  vanishing, non-vanishing, and computability*](https://arxiv.org/abs/2106.13567), develop the
  algebraic/bounded comparison at group level but do not give this operator-theoretic prime-weld
  category separation.

Targeted searches for algebraically exact cocycles with no bounded primitive, affine
functional-equation primitives, and Euler-multiplier/derivative cocycles found bounded-cohomology
analogues but no statement of this exact law.  Verdict:
`[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is not claimed for the generic possibility
that ordinary and bounded cohomology differ; it is claimed for the exact prime weld, its
FE-covariant affine trivialization, forced coefficient `1`, and fixed spectral-`L²` bounded no-go.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean` passed
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
