# Pole-blind Poisson boundaries have positive origin degree

- **ID:** qii-pole-blind-positive-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/q-ii-source-effectivity-and-linear-degree.md
- **Statement:** A nonzero genuine Poisson boundary sharp square has both Mellin pole values zero and strictly positive origin degree. No correction depending only on those two values makes origin degree descend.

## Paper proof [PROVED HERE]

Let `fXi` be the actual Meyer cap whose Poisson boundary Mellin transform is `xi`.
The negative Euler operator `E` preserves the cap and multiplies its boundary
transform by `s`. Set `f = E(E(fXi)) - E(fXi)` and `g = Poisson(f)`.
Then `M_g(s) = s(s-1)xi(s)`. Thus `M_g(0)=M_g(1)=0`, while
`M_g(2)=2xi(2)` is nonzero by the existing unconditional half-plane result.
In particular `g` is a nonzero actual boundary, not a prescribed transform.

Let `q=g*g^sharp`. The actual boundary convolution ideal supplies a cap preimage
of `q`. Multiplicativity of the Mellin transform preserves both zero pole values.
The already certified origin identity gives
`origin(q) = integral(exp(t)*normSq(g(t))) > 0`.
Consequently `q` is nonzero and `(0,0,q)` is a nonzero genuine principal cycle:
its two compensating pole coordinates vanish identically. Every intersection
reading of this cycle vanishes, despite its positive origin degree.

For any function `F : C -> C -> C`, the normalized corrected expression
`origin(h)+F(M_h(0),M_h(1))-F(0,0)` equals `origin(q)` on this boundary.
A linear functional on the actual Poisson quotient takes its class to zero,
so cannot equal the corrected expression on every source. This rules out even
nonlinear pole corrections, and hence every linear combination of pole degrees.

## No-go closure

- **Exact obstruction:** A positive origin square degree survives on a boundary invisible to both pole evaluations.
- **Positive survivor:** Explicit nonzero pure-source principal cycles; their positive source mass is invisible to every intersection reading and every pole correction.
- **New insight:** Failure of origin-degree descent is intrinsic to the source quotient, rather than a mismatch in the two polar coordinates.
- **Status:** Dependency-closed paper proof. Existing inputs: exact Xi cap, actual negative Euler operator, actual convolution ideal, positive origin mass. Actual-file check and all five standard-axiom audits passed.

## Gates

- [x] Source-pure, unconditional construction.
- [x] Complete paper proof and internal corpus audit.
- [x] Direct Lean check, standard axiom audit, umbrella import.

## Lean certificate

`ArithmeticCastelnuovoSeveri/PoleBlindPoissonBoundariesHavePositiveOriginDegree.lean`.

The five audited endpoints are:

- `meyerPoleBlindXiCap_mellin`
- `exists_meyer_pole_blind_boundary_positive_originDegree`
- `exists_meyer_pure_source_principal_positive_originDegree`
- `exists_meyer_pure_source_radical_positive_originDegree`
- `meyerOriginDegree_pole_correction_not_cohomology_degree`

Each `#print axioms` returned exactly `[propext, Classical.choice, Quot.sound]`.
Final actual-file check passed:

```
lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/PoleBlindPoissonBoundariesHavePositiveOriginDegree.lean
```

Temporary prints removed; ACS umbrella and README wired. No olean built for this
leaf; the previously missing origin-degree dependency olean was built for this
actual importer only. External novelty unverified.
