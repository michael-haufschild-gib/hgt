# Library ticket — Böttcher dyadic monodromy witnesses C11/C20

## Request

Add the new disconnected quadratic Böttcher monodromy witnesses to the Door hypertranscendence ledger/status.

## New cards

- `../2-fully-proven/bottcher-dyadic-monodromy-finite-type-absence.md`
- `../2-fully-proven/bottcher-pruefer-monodromy-no-finite-cover.md`
- Supporting algebraic lemma: `../3-formalized/not_new_scientific_knowledge/unbounded-one-coordinate-monodromy-obstruction.md`

## Door mapping

- C11 finite-type monodromy absence: disconnected nonexceptional quadratic Böttcher coordinates have unbounded dyadic scalar monodromy around Cantor cylinders, so no finite branch cover / finite monodromy permutation representation captures continuation.
- C20 finite-cover descent failure: the dyadic monodromy image contains the Prüfer `2`-group; finite covers correspond to finite-index subgroups; Prüfer monodromy survives every finite cover.

## Grade

THEOREM (paper), BRIDGE / concrete witness. Not a proof of generic C11/C20, but a precise finite-handle failure mode in a hypertranscendental family.

## Important caveat

Use the direct Böttcher convention `phi_c(f_c)=phi_c^2`. The monodromy is topological period monodromy of `d log phi_c` around clopen Julia cylinders, not local branching at escaping precritical points.

## 2026-06-24 exact-image update

Also add `../2-fully-proven/bottcher-exact-pruefer-monodromy.md` to the Door
ledger. It strengthens the C11/C20 witnesses by identifying the scalar monodromy
image exactly as `mu_{2^infty}` and the period group exactly as
`2*pi*i Z[1/2]`.
