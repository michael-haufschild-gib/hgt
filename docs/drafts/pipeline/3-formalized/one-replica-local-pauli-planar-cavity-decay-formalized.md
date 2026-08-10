# Formalization certificate — one-replica local-Pauli planar cavity decay

- **Card:** `one-replica-local-pauli-planar-cavity-decay.md`
- **Primary module:** `formal/GaloisForLFunctions/HTGeometry/OneReplicaTracelessPauliSpectralDecay.lean`
- **Capstone:** `oneReplicaLocalPauliPlanarCavityDecay`
- **Status:** `[LEAN-FORMALIZED] [KERNEL-AUDITED] [UMBRELLA-WIRED]`

For arbitrary `n q : ℕ`, `q ≥ 1`, nonnegative bounded-word variances, and common strictly positive
weight-one variance, the capstone works on `n + 1` qubits and proves one closed conjunction:
Hermiticity, exact rank-nondecreasing fullness, scalar spectral-law absolute continuity, decay of
every entry, decay of every vector matrix coefficient, and operator-norm decay at the cocompact
filter.  The `n + 1` indexing is exactly the positive-qubit domain; no extra theorem premise is
introduced.

Reusable infrastructure proves the finite Dyson--Hall obstruction, formal algebraic branch,
coordinate and averaged spectral laws, Radon--Nikodym density identities, and
Riemann--Lebesgue/finite-matrix norm upgrade.  No external matrix-semicircle conclusion is assumed.

Verification on 2026-08-10:

```text
lake env lean GaloisForLFunctions/HTGeometry/OneReplicaTracelessPauliSpectralDecay.lean  # pass, no warnings
lake build GaloisForLFunctions.HTGeometry.OneReplicaTracelessPauliSpectralDecay          # pass
#print axioms oneReplicaLocalPauliPlanarCavityDecay                                      # propext, Classical.choice, Quot.sound
```
