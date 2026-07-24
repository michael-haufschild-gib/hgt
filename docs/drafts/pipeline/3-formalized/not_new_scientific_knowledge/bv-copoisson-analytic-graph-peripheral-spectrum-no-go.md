# Analytic BV--co-Poisson contraction graphs have a peripheral-spectrum obstruction

- **ID:** `bv-copoisson-analytic-graph-peripheral-spectrum-no-go`
- **Stage:** 3-formalized
- **Type:** ROUTE NO-GO / POSITIVE SURVIVOR CLASSIFICATION
- **Scientific status:** `[PROVED] [CLASSICAL OPERATOR CORE] [ROUTE APPLICATION]`
- **Formal module:**
  `formal/GaloisForLFunctions/HTGeometry/PeripheralContractionPointSpectrum.lean`

## Statement

Let `H` be a separable complex Hilbert space and `D` a contraction on `H`. Suppose an analytic
source graph supplies a nonzero continuous evaluation functional `ell_w` for every `w` in a
nontrivial critical-line interval, and suppose exact source covariance gives

```text
ell_w(Da)=chi(w) ell_w(a),
|chi(w)|=1.
```

On any subinterval on which `chi` is injective, the Riesz vectors `k_w` satisfy

```text
D* k_w=conj(chi(w)) k_w.
```

Distinct peripheral eigenvectors of a contraction are orthogonal. A separable Hilbert space
contains only countably many mutually orthogonal nonzero vectors, whereas the interval is
uncountable. Therefore no such analytic contraction graph exists.

For the BV square-decimation character,

```text
chi(1/2+it)=r^(2it),
```

every interval shorter than one period is injective. Hence the proposed pole-cancelled analytic
RKHS graph cannot simultaneously have:

1. separable Hilbert topology;
2. contractive square-decimation;
3. nonzero continuous ordinary evaluation throughout a critical-line interval;
4. exact global BV dilation covariance.

## Proof

Let `Tx=lambda x`, `|lambda|=1`, and `||T||<=1`. Equality in the contraction norm gives

```text
T* x=conj(lambda)x.
```

If `Ty=mu y` with `mu!=lambda`, then

```text
lambda <x,y>
 =<T*x,y>
 =<x,Ty>
 =mu <x,y>,
```

so `<x,y>=0`.

For an injective family of peripheral eigenvalues, normalize the corresponding eigenvectors.
They are pairwise orthogonal unit vectors, hence pairwise at distance `sqrt(2)`. The open balls of
radius `1/2` around them are nonempty and disjoint. A separable space has only countably many
pairwise disjoint nonempty open sets, so the parameter set is countable.

The Lean module proves the adjoint equality case, orthogonality, and the countability theorem
without a custom axiom.

## Exact route consequence

This kills the ordinary analytic provider proposed in
`../../1-in-progress/bv-prime-window-decimation-boundary-contraction-rh.md`. Pole cancellation and
holomorphic evaluation cannot be combined with exact global decimation covariance in one
separable contractive RKHS.

It does **not** kill the Burnol co-Poisson quotient route. There the dilation character is only an
eigencharacter **modulo the co-Poisson multiplier ideal** and becomes exact on the countable
annihilator spectrum. Ordinary evaluation may remain continuous away from that spectrum because
it is not a contraction eigenfunctional there.

## Strongest positive survivor

Any viable source metric must be a singular quotient/fibre metric satisfying all of:

1. source definition before zero selection;
2. separable completion;
3. contractive decimation;
4. global covariance only modulo the completed multiplier ideal;
5. exact eigenfunctional covariance only after restriction to annihilator characters;
6. nonzero principal-part evaluation on those characters.

Thus the live theorem is no longer “construct a holomorphic cancelled-source RKHS”. It is:

```text
construct a source-defined contractive quotient representation
whose multiplier-ideal defect absorbs every ordinary critical-line evaluation,
while its annihilator fibres retain the BV Laurent character.
```

That is the exact singular boundary realization problem. It is stronger than pole cancellation
and weaker than choosing a divisor-indexed metric.

## Novelty boundary

Peripheral eigenvector orthogonality and countability are classical Hilbert-space facts. No
novelty is claimed for that operator theorem. The contribution here is a rigorous route
falsification and survivor classification: it removes an apparently natural but impossible
analytic graph from the RH pipeline and identifies the multiplier-ideal defect as mandatory, not
optional.

## Gates

- [x] contraction equality case proved
- [x] distinct peripheral eigenvectors proved orthogonal
- [x] injective peripheral family proved countable in separable Hilbert space
- [x] analytic BV graph contradiction extracted
- [x] strongest singular quotient survivor stated
- [x] formal module compiles directly
- [ ] construct source-defined multiplier-ideal defect with contractive quotient norm
- [ ] prove annihilator-fibre Laurent continuity
- [ ] compose to RH
