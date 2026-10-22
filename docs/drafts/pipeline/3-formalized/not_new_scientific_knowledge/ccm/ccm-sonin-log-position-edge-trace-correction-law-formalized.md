# Formalization certificate — `ccm-sonin-log-position-edge-trace-correction-law`

- **Card:** `ccm-sonin-log-position-edge-trace-correction-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCM/CCMSoninEdgeCommutatorAlgebra.lean`
  (plus the already-formalized coordinate commutators cited in the card's "Coordinate scope")
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext]` on all 4 theorems
- **Hypotheses:** only the quantified algebraic data; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(10)` formal complement commutator | `commutator_formal_complement` |
| `(6e)` alternating-block commutator | `commutator_alternating_block` |
| `(6d)` resolvent commutator | `commutator_resolvent` |
| `(6c)` exact projection commutator | `commutator_exactProjection` |
| coordinate scope `[log\|x\|,U_p]`, `[x,U_p]` | already in the corpus (cited on the card) |

## Deliberately outside the Lean statement

- the distributional edge formula `(3)`–`(4)` and parity polarization `(11)`–`(12)`;
- the Sobolev domain failure `(13)`–`(14)`;
- the rigged extension making `(6c)` an operator identity, and Hilbert–Schmidtness of `C_a`;
- the first-moment kernel `(6)`.

The card's open route items (the nonlocal Mellin-scattering commutator and its source-defined
relative trace) are route gates, not statements of this card.
