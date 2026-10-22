# HB bounded global AIME response trivialization no-go

Status: formalized in Lean 4. Novelty audited 2026-08-31; novelty unverified pending specialist review.

## Route class killed

Existence of an arbitrary bounded complex-linear response on `ℓ²(XiZeroCopy)` cancelling the
literal cubic AIME packet is not an RH producer.

## Exact classification

For one nonzero seed, universal cancellation holds exactly when

`(Delta e_q)(q) = -1`

for every canonical Xi basis vector. Equivalently, `Delta + I` has zero canonical diagonal, so all
cancellers form the affine space `-I + {bounded zero-diagonal operators}`.

Canonical `-I` cancels every seed on every Xi copy unconditionally and is noncompact.

## Proof-chain consequence

The unqualified arrow

`bounded single-packet AIME cancellation → full causal-cut extinction`

is invalid as a producer interface: left premise is automatic. Physical survivor must construct
the radiative retarded-minus-advanced jump on the two-leg Peierls carrier with its bilinear pairing,
cyclic residual, skew jump, and independent source/left-QNM legs. Existing full-cut extinction then
implies source-FE clock covariance and RH through the four-route transductions.

## Lean artifact

Module:
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBBoundedGlobalAIMESourceResponseTrivializationNoGo`

Capstone:
`d4HBBoundedGlobalAIMESourceResponseExistenceRouteKilled`.

## Verification

- Direct `lake env lean` passed.
- Target-only `lake build` passed: `11900/11900`.
- `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint recognizes capstone; only unrelated pre-existing unreachable-module errors remain.
- Forbidden-token, whitespace, and scoped diff checks passed; no full/umbrella build ran.
