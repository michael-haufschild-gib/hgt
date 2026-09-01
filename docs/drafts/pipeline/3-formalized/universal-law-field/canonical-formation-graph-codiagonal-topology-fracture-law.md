# Canonical formation-graph codiagonal topology-fracture law — formalized

- **ID:** ULF-TAFM-29
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/canonical-formation-graph-codiagonal-topology-fracture-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.CanonicalFormationGraphCodiagonalFracture`
- **Capstone:** `formationGraphTopologyFracture`

## Certified content

- `formationGraphLoad x` multiplies grade `n` by `n+1`.
- canonical formation resolvent exactly inverts this load on finite packets;
- inverse-grade codiagonal weights are square summable;
- constant base-gauge codiagonal is closable iff its coefficient is zero;
- every constant coefficient has bounded recovery after formation loading.

## Audit

- `lake env lean GaloisForLFunctions/HTGeometry/CanonicalFormationGraphCodiagonalFracture.lean`: PASS
- `lake build GaloisForLFunctions.HTGeometry.CanonicalFormationGraphCodiagonalFracture`: PASS
- `#print axioms formationGraphTopologyFracture`: only `propext`, `Classical.choice`, `Quot.sound`
- umbrella import added to `GaloisForLFunctions/HTGeometry.lean`; umbrella build intentionally not run.

## RH consequence

Canonical formation-graph boundedness is nonselective. Any final selector must control compatibility
between base and formation gauges, or preserve a reflection-odd adjacent-grade channel that the
canonical `(N+1)` regularization cannot absorb.
