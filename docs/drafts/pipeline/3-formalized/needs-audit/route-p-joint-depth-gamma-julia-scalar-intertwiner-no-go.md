# Route P joint-depth Gamma--Julia scalar-intertwiner no-go

- **ID:** `route-p-joint-depth-gamma-julia-scalar-intertwiner-no-go`
- **Stage:** 3-formalized / needs audit
- **Type:** `[FALSIFIED] [POSITIVE SURVIVOR] [THEOREM] [P-G105E]`
- **Parent:** `route-p-fourth-depth-gamma-cyclic-julia-intertwiner.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveJointDepthGammaJuliaScalarIntertwinerNoGo.lean`

## Goal

Test whether P-G105D's universal Gamma--Julia pivot is literally the reciprocal-promotion
co-source in corpus's already proved joint-depth Xi landing.

## Conjecturing loop

### Conjecture 1 — actual Xi source and co-source differ by one constant

This would let P-G105C's universal `B tensor G` completion attach directly to existing Xi-landing
Krein pair.

**Falsified.** On every `(prime,depth)` label,

```text
source(p,e)=log(p) coSource(p,e).
```

Ratio is independent of depth but varies strictly with prime. Evaluating at primes `2` and `3`
proves no real constant exists. Taking real parts of a hypothetical complex Hilbert-vector equality
proves no complex constant exists either, on every positive source chamber.

### Conjecture 2 — scalar no-go leaves no compatible Gamma--Julia transport

**Falsified, with exact positive survivor.** Multiplying source by P-G105D Gamma amplitude `d` gives

```text
d source(p,e) = d log(p) coSource(p,e).
```

Thus correct intertwiner is label-diagonal multiplier

```text
M_GammaJulia(p,e)=d log(p),
```

not a constant. Although ambient log multiplier is not asserted bounded, applying it to literal
co-source lands exactly in the already proved Hilbert source vector; hence that vector lies in its
natural domain.

## Paper proof

Corpus definitions are

```text
promotion(p,e)=sqrt(log p),
source=promotion * boundary,
coSource=promotion^-1 * boundary.
```

Since `promotion^2=log p` and all factors are nonzero,

```text
source=log(p) coSource.
```

Suppose `coSource=lambda source` for all labels. Then cancellation at prime `p` gives
`log(p) lambda=1`. At `p=2,3`, this forces `log 2=log 3`, contradicting strict monotonicity of
logarithm. For a complex Hilbert scalar, coordinate equality and real parts produce same forbidden
real scalar `Re(lambda)`.

Multiplying exact coordinate law by P-G105D's positive Gamma amplitude gives operator-valued
survivor. The scaled primitive source is already in joint-depth `l2`; coordinate equality proves it
is precisely log-diagonal image of co-source. `QED`

## No-go closure

- **Exact killing theorem:**
  `routePPrimitiveJointDepth_no_complex_scalar_intertwiner`.
- **Strongest positive survivor:** prime-log diagonal Gamma--Julia multiplier and Hilbert-valued
  transport, formalized by
  `routePPrimitiveJointDepthGammaJuliaLogTransport_apply`.
- **New insight:** constant Julia channel is correct on one carrier, but literal arithmetic
  source/co-source polarization includes primitive promotion. Completion must occur after retaining
  `log p`, as operator-valued block or weighted Gram; universal Kronecker block cannot be declared
  Xi landing.
- **Status:** dependency-closed paper and Lean proof; external novelty audit pending.

## Novelty and anti-theatre audit

Nonproportional weighted vectors are elementary. Route-specific new knowledge is exact collision
between P-G105D and corpus's real Xi producer: it rules out proposed scalar weld and identifies the
unique surviving label multiplier `d log p`. This materially changes architecture from universal
tensor completion to prime-log diagonal completion before scalarization.

No Stokes orientation, bounded ambient multiplier, completed determinant, or RH claim is made.

## Formal status

Lean proves unconditionally:

- exact source/co-source prime-log coordinate relation;
- no real scalar for any source parameter;
- no complex Hilbert scalar on every positive chamber, parameterized without premises by `exp tau`;
- exact Gamma--Julia log multiplier relation;
- Hilbert transport coordinate theorem;
- combined scalar-no-go/log-survivor capstone.

Direct Lean and target-only module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Forbidden scan and `git diff --check` pass. Module is wired;
no umbrella build was run.

## Refined open core

Build finite operator-valued Julia--Krein completion with diagonal `L(pe)=log p`, preserving actual
joint-depth source/co-source cross which already lands in von Mangoldt/Xi. Then determine whether
its completed finite determinants retain signed-permutation stability and converge cofinally.
Constant-block source identification is retired.

## Higher universal principle

Stuckness came from confusing channel universality with arithmetic polarization. Julia coefficient
is universal, but primitive promotion is not: source and co-source are dual half-densities separated
by logarithmic Radon--Nikodym derivative. Universal completion must be conjugated by this derivative
before finite incidence is formed.

## Log

- 2026-08-16 — P-G105E scalar intertwiner falsified; exact prime-log operator-valued survivor
  paper-proved and formalized.
