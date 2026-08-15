# Exterior range observability — formalized closure

- **ID:** `ccm-exterior-range-observability-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-exterior-range-observability-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.HTGeometry.RangeObservabilityDuality`

Placed in `HTGeometry` rather than `RHTower` because nothing in it mentions apertures, `Xi`, or
primes: it is range duality for an injective self-adjoint operator.

Umbrella: `GaloisForLFunctions.HTGeometry`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(2)` | `ObservableBy` | the observability predicate |
| self-adjointness | `inner_isSelfAdjoint_left` | `⟪D x, y⟫ = ⟪x, D y⟫` from `adjoint D = D` |
| `(3)` | `observableBy_of_mem_range` | a preimage supplies its own norm as an observability constant |
| `(4)`–`(5)` | `mem_range_of_observableBy` | the hard direction. Injectivity gives `H ≃ range D`, which makes `D h ↦ ⟪g,h⟫` well defined without hand-choosing a section; the observability bound makes it continuous via `LinearMap.mkContinuous`; Hahn–Banach (`exists_extension_norm_eq`) extends it; Riesz (`InnerProductSpace.toDual`) represents it. No closedness, compactness, or density of the range is used here |
| `(1)`–`(2)` | `observableBy_iff_mem_range` | the equivalence |
| `(12)` | `setOf_observableBy_eq_range` | the admissible set is exactly the range, hence a submodule: linearity of the admissible trace space is the range characterisation, not an extra verification |
| `(10)` | `norm_le_of_observable_bound`, `observable_bound_norm` | `‖x‖` is admissible and every admissible constant dominates it. Density of the range enters only here, from the corpus's `denseRange_of_isSelfAdjoint_of_injective`. The nonnegativity hypothesis on the constant is genuinely needed: on the zero space the bound is vacuous for every constant |
| `(11)` | `inner_sandwich_adjoint` | `⟪Q R P f, h⟫ = ⟪f, P R Q h⟫` for self-adjoint factors — what converts exterior forcing into an interior pairing |

## Axioms

`#print axioms` on every theorem returns exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Deliberately outside the Lean statement

The Fourier leakage estimate `(9)` for the concrete screw kernel, the Evans test `(15)`, and the raw
`L²` transformed-trace regularity. These are the card's own **open** gates, not theorems it proves.

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
