# Schwarz-pair null cone and transverse crossing

Status: Lean-formalized null-cone theorem; transverse crossing law in progress.
`[CORPUS-NEW SYNTHESIS]`. Does not prove RH.

## Conjecture loop outcome

The Cauchy localization theorem identifies critical-line reflection `alpha ↦ conj alpha` as the
parity involution. Corpus search of the positive-paired source route exposed a second involution:
source Schwarz pairing is `alpha ↦ -conj alpha`. Lean now proves that the boundary test supported
on one fiber and its source-Schwarz partner,

```text
1_{alpha} + 1_{-conj alpha},
```

is disjoint from its critical-line reflection whenever `alpha` is nonzero and nonreal. Therefore
its Weil square and Hilbert quadratic are exactly zero.

This is not zero-vector degeneracy. On every hypothetical off-line Xi quartet, its
reflection-even and reflection-odd energies are equal and both strictly positive. Hence the
positive-paired Cauchy closure reaches a genuine Krein null direction at the divisor boundary.

The resulting higher principle is:

```text
Schwarz-paired boundary values lie on the parity null cone;
orientation lives in the first transverse crossing, not in boundary positivity.
```

This explains why paired-diagonal negativity appears only at nearby regular poles and why a
boundary-value coercivity argument cannot close RH. `FiniteHankelBoundaryKreinCrossing` exhibits
the same structure algebraically: a null state is oriented by its first extension coordinate.

## Lean source

`formal/GaloisForLFunctions/RHTower/ThetaCuspTiltFluxWeilParitySchwarzPairNullCone.lean`

Key closed declarations:

```text
xiWeilSchwarzPairedFiberTest_product_eq_zero
xiWeilPolarization_schwarzPairedFiber_eq_zero
xiWeilSchwarzPairedFiber_evenEnergy_eq_oddEnergy
xiWeilHilbertQuadratic_schwarzPairedFiber_eq_zero
xiWeilSchwarzPairedFiber_evenEnergy_pos
xiWeilSchwarzPairedFiber_oddEnergy_pos
```

Verification:

- direct source check and exact target build passed; no umbrella/full build was run;
- all audited `#print axioms` reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`;
- forbidden-token and whitespace scans passed;
- module is wired into `RHTower.lean` without building umbrella.

## Next hard conjecture

Export the exact transverse crossing rate hidden inside
`exists_xiReciprocalSquareUpperSector_neg_near_of_zero`. For the canonical horizontal approach
from the side opposite `alpha.re`, step `epsilon_n = 1/(n+1)`, the corpus calculations predict

```text
epsilon_n * ccmPositivePairedReducedKernel(z_n, z_n)
  -> -2 * |alpha.re| * ord_alpha(Xi) / normSq(alpha).
```

The limit is strictly negative. This would identify the positive-paired source diagonal as the
exact first Krein crossing form of the nonzero parity-null boundary state, including divisor
multiplicity. It sharpens existing nearby-negativity existence to a canonical spectral-flow law.

## Log

- 2026-08-21 — Proved exact nonzero Schwarz-paired parity-null boundary law. Began extraction of
  multiplicity-exact transverse source crossing.
