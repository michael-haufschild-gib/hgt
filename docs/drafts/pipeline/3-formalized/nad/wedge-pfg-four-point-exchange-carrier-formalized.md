# Wedge PFG four-point exchange carrier — formalized

- **ID:** `wedge-pfg-four-point-exchange-carrier-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `wedge-pfg-four-point-exchange-carrier.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/WedgeFourPointExchangeCarrier.lean` | the connected four-point coefficient `(5)`, the generator identity `(6)`, the DA/HT transfer `(7)`, and the Kolchin slope `(8)` |
| `HTGeometry/KolchinSlopeDichotomy.lean` | the jet rank and the exact slope dichotomy used by `(8)` |
| `HTGeometry/DifferentialAdjoinMobiusGenerator.lean` | equality of differential adjunctions from mutual membership |
| `HTGeometry/ExponentialObservationHypertranscendence.lean` | HT is unchanged by adding a differentially algebraic observable |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `(5)` `wedgeFourPointCoefficient S = S − 1` — the exact two-rapidity coefficient distribution of
  the truncated four-point function, in the canonical scattering coordinate;
- `(6)` `differentialAdjoin_wedgeFourPointCoefficient` — `K⟨S₂ − 1⟩ = K⟨S₂⟩` as differential fields,
  proved by mutual membership rather than by a class-level shortcut;
- `(7)` `hypertranscendentalOver_wedgeFourPointCoefficient_iff` and
  `differentialAlgebraicOver_wedgeFourPointCoefficient_iff` — both halves of the transfer;
- `(8)` `tendsto_kolchinSlope_one_wedgeFourPointCoefficient` — on the HT branch the connected
  coefficient has normalized Kolchin slope exactly `1`, and
  `tendsto_kolchinSlope_zero_wedgeFourPointCoefficient` gives slope `0` on the DA branch, so the
  connected sector **separates** the two branches.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/WedgeFourPointExchangeCarrier.lean
lake build GaloisForLFunctions.HTGeometry.WedgeFourPointExchangeCarrier
```

## What closed last

Equation `(8)`.  The card asserts that on the HT branch every finite jet packet of the connected
coefficient has full transcendence degree and the one-reporter slope is `1`; until
`KolchinSlopeDichotomy.lean` existed there was no Lean object for that slope at all.  With the jet
rank and its exact dichotomy in place, `(8)` is a two-line consequence of `(7)`, and the DA branch
statement comes for free.

## Boundary

The finite ZF operator algebra, the unbounded-domain theory, the distributional extraction of the
coefficient from `(1)`–`(4)`, and Lechner's constructive-QFT locality theorem are not in the formal
tree; the card records that boundary itself.  The remaining paper gates — a formula-level external
novelty audit, a compact-local derivation-preserving transfer theorem, a locality or positivity
inequality controlling the HT coefficient, and an independent operator-algebraic QFT review — are
onward theorem targets and external obligations, not formalization gates for the transfer certified
above.
