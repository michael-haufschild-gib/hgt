# The completed logarithmic source has a canonical closed two-channel graph — formalized closure

- **ID:** `ccm-logderivative-closed-two-channel-graph-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-logderivative-closed-two-channel-graph-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

`GaloisForLFunctions.RHTower.CCM.CCMTwoChannelGraph` (new), over the Pick-cluster modules.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| section 1, statement 2 | `pairedGraph_closed` | the paired channel map of a closed source operator is closed |
| `(12)` | `cauchy_insertion_split` | the exact causal/anti-causal split of a Cauchy insertion |
| `(13)` | `cauchy_insertion_split` (second summand) | the rank-one anti-causal residue coordinate |
| `(20)` | `residue_vector_energy` | the residue vector has `L²` energy `\|c\|²/(2a)` |
| `(17a)`, `(17b)` | `integral_cexp_unit`, `bilateral_atom_factorization` | the bilateral atom factors through `L²(0,1)` with opposite causal orientations |

## Axioms

`#print axioms` on all five declarations returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The half-plane Hardy decomposition `H²₊ ⊕ H²₋` and its projections; mathlib has no such layer.
- The outer-function majorants `(5)` and `(8b)` giving the dense core `(6)` and the dense adjoint
  core `(8d)`.
- Closedness of multiplication by a measurable a.e.-finite function on `L²` — the analytic input of
  `pairedGraph_closed`, which is stated there as the hypothesis `hTclosed`.
- The Cartwright/bounded-type property of the centred Xi source `(15)` and the Euler-region
  expansion `(17)`.
- The card's open gates: the boundary-block Hilbert–Schmidt theorem, the four-unit relative-trace
  density bound `(22)`, and RH.

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCM.CCMTwoChannelGraph`: success.
- `#print axioms` on every declaration: clean.
- Umbrella import added.
