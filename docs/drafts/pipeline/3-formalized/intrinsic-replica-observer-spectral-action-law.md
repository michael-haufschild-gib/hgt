# Intrinsic replica observer--spectral action law

- **ID:** `intrinsic-replica-observer-spectral-action-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / universal action decomposition and local capstone
- **Date:** 2026-08-05
- **Paper proof:** `../2-fully-proven/intrinsic-replica-observer-spectral-action-law.md`
- **Formal sources:**
  - `formal/GaloisForLFunctions/HTGeometry/IntrinsicReplicaObserverSpectralActionLaw.lean`
  - `formal/GaloisForLFunctions/HTGeometry/LocalHamiltonianObserverSpectralActionLaw.lean`

## Exact universal law

For every finite real spectrum, every nonnegative normalized weight vector,
every replica order `r`, and every `T>0`, define the intrinsic resolution

\[
 \delta_r(E)=
 \min\bigl(\{1\}\cup
 \{|\Delta_{a,b}|:\Delta_{a,b}\ne0\}\bigr).
\]

Lean proves unconditionally that `delta_r(E)>0` and

\[
 \left|\overline F_r(T)-C_r(E,p)\right|
 \leq\min\{1,(T\delta_r(E))^{-1}\}.
\]

Here `C_r` is the exact zero-action replica collision mass. Existing
formalized dependencies prove its decomposition into permutation floor plus
nonnegative resonance excess, and prove that all orders attain the floor
exactly when the energy family has maximal projective rational rank.

## Ordinary local-Hamiltonian capstone

For every `n,q>=2`, the full real trace-zero onsite-plus-nearest-neighbour
Hamiltonian space on an open `n`-site `q`-level path has a dense residual
full-Lebesgue-measure subset on which, simultaneously:

- projective spectral rank is `q^n-1`;
- every positive normalized spectral weighting obeys the intrinsic action
  bound to the permutation floor;
- every replica order is covered.

## New declarations

- `nonzeroReplicaActionMagnitudes`;
- `intrinsicReplicaActionResolution`;
- `intrinsicReplicaActionResolution_pos`;
- `intrinsicReplicaActionResolution_le`;
- `norm_finiteSpectralSurvivalFidelityMean_sub_collisionMass_le_intrinsic`;
- `norm_finiteSpectralSurvivalFidelityMean_sub_floor_le_intrinsic`;
- `HasIntrinsicReplicaObserverSpectralActionLaw`;
- `MaximallyProjectiveEnergy.hasIntrinsicReplicaObserverSpectralActionLaw`;
- `exists_uniformQuditPathTracelessIntrinsicObserverSpectralAction_dense_residual_fullMeasure`.

## Verification

Foreground source checks pass for both new modules. Project lint passed.
Axiom audit of the load-bearing declarations reports only `propext`,
`Classical.choice`, and `Quot.sound`. Final target audit passed with:

```text
lake build GaloisForLFunctions.HTGeometry.LocalHamiltonianObserverSpectralActionLaw
```

## Boundary

This is the complete observer--spectral action law for finite-order
survival-return reporters. It is not the still-open adaptive circuit
shortcut upper law. No statement about state circuit complexity follows
without selector-uniform endpoint anti-concentration.
