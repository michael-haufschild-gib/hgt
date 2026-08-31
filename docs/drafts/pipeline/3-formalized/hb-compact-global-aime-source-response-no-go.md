# HB compact global AIME source-response no-go

Status: fully formalized in Lean 4. Novelty audited 2026-08-31; novelty unverified pending specialist
review.

## Route class killed

Every compact bounded complex-linear global response on `ℓ²(XiZeroCopy)` is excluded as a universal
canceller of the literal cubic AIME pole packet. Response may have infinite algebraic rank and mix
all Xi fibres. No diagonal, locality, passivity, Schwarz, self-adjointness, finite-band,
determinant, or finite-rank condition is used.

This strictly strengthens the finite-algebraic-rank no-go and formally includes every
Hilbert–Schmidt response.

## New theorem

Universal cancellation for one nonzero seed forces

`(Delta e_q)(q) = -1`

for every canonical Xi basis vector `e_q`. Thus `1 ≤ ‖Delta e_q‖` on the infinite orthonormal Xi
enumeration. Compact operators send this enumeration to zero, contradiction.

Stronger positive survivor:

`1 ≤ ‖Delta - K‖`

for every compact operator `K`. Hence any successful bounded source-adapted completion must carry a
noncompact Calkin-class component of norm at least one.

## Exact RH chain affected

`source-adapted radiative cancellation`
→ `full causal-cut extinction`
→ `source-FE clock covariance`
→ existing FZZ-P/PW-B/RBH Ward transductions
→ RH.

The first arrow cannot be supplied by any compact global Hilbert response.

## Lean artifact

Module:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingHBCompactGlobalAIMESourceResponseNoGo`

Main declarations:

- `d4HBCompactAIMESourceResponse_diagonal_eq_neg_one`
- `d4HBCompactAIMESourceResponse_one_le_norm_basis`
- `not_d4HBCompactAIMESourceResponse_universalCancellation`
- `d4HBCompactAIMESourceResponse_one_le_norm_sub_compact`
- `not_d4HBHilbertSchmidtAIMESourceResponse_universalCancellation`
- `d4HBCompactGlobalAIMESourceResponseCancellationRouteKilled`

The source and full response retain the exact half-turn oddness and cubic real-scale laws.

## Novelty scope

Corpus search supplied separate exact AIME nonvanishing, Xi enumeration, ℓ² coordinate, and compact
orthonormal-decay results, but no compact global AIME response obstruction or essential-distance
floor. Primary AIME and causal-QNM literature audited during this run did not state this
Xi-indexed theorem. No priority claim is made without specialist review.

## Verification

- `lake env lean` passed on scratch and direct module.
- Target-only `lake build` passed: `11899/11899`.
- `#print axioms` for diagonal law, compact no-go, essential-distance floor, Hilbert–Schmidt
  consequence, and route-kill capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint recognizes this module as umbrella-reachable and reports no defect in it. Its nonzero
  status comes only from unrelated pre-existing unreachable modules.
- No full or umbrella build was run.
