# Every arithmetic pole survives the averaged Eisenstein product

- **ID:** W11-EP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W11 programme](../1-in-progress/ads3-scalar-modular-bootstrap.md)
- **Statement:** The product quotient `N(u,z)N(u,w)/ξ(1+2u)` detects every arithmetic resonance, with full multiplicity, on every prescribed pair of horocycles. Its iterated horocycle average does too.

## Proof

[PROVED HERE] Let `D(u)=ξ(1+2u)` and let `N` be the corpus's analytic
Eisenstein numerator. Its mean on the height-`Y` horocycle is

`C_Y(u)=Y^(1/2+u)D(u)+A(u)Y^(1/2−u)`,
`A(u)=((1+2u)/(2u−1))ξ(2u)`.

At a zero `p` of `D`, `−1/2<Re p<0`. Both rational factors in `A(p)`
are nonzero. Functional equation and the zero-free half-plane give
`ξ(2p)=ξ(1−2p)≠0`. Thus `C_Y(p)≠0` at every positive height.

The iterated average is exactly `C_Y C_Z/D`. Its analytic numerator is
nonzero at `p`, so its meromorphic order is the negative of the zero order
of `D`. That zero order is a finite positive integer. Each nonzero mean
also gives a point with `N(p,z)≠0`; choose one on each horocycle to obtain
the same full pole order for a pointwise product.

The exact numerator decomposition is
`C_Y C_Z = D²Y^sZ^s + DA(Y^sZ^(1−s)+Y^(1−s)Z^s) + A²Y^(1−s)Z^(1−s)`,
where `s=1/2+u`. Only the final term survives on the zero divisor of `D`.

## Lean

Module: `ArithmeticScatteringHolography/ModularBootstrap/EisensteinProductDetection.lean`.
Namespace: `GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap`.

- `integral_productQuotient`: exact double average.
- `meanNumerator_decomposition`: denominator and reflected terms.
- `exists_product_full_order`: pointwise detection on prescribed horocycles.
- `meanQuotient_full_order`, `meanQuotient_pole`: exact finite pole multiplicity of the average.

`lake --old env lean GaloisForLFunctions/ArithmeticScatteringHolography/ModularBootstrap/EisensteinProductDetection.lean` passes. Transitive audits of the integral, pointwise detector and averaged pole theorem use only `propext`, `Classical.choice`, `Quot.sound`. Imported by the programme umbrella; no umbrella build.

## Scope

No simple-zero assumption or unproved analytic input. The zero and height
subtypes index actual arithmetic resonances and positive horocycles.
This extends the corpus's single-Eisenstein nonvanishing result to the
product and its explicit average. No scientific novelty beyond that extension
is claimed. The equality with an actual Narain partition-function overlap,
and the RH-strength remainder bound, remain unproved.

## Gates

- [x] 0 → 1: concrete Eisenstein numerator.
- [x] 1 → 2: dependency-closed constant-term and order proof.
- [x] 2 → 3: direct Lean check and transitive axiom audit.
