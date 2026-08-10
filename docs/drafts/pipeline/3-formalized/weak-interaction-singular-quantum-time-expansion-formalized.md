# Arbitrarily weak local interaction singularly expands quantum time — formalized closure

- **ID:** `weak-interaction-singular-quantum-time-expansion-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./weak-interaction-singular-quantum-time-expansion.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SPECIALIST AUDIT OPEN]`

## Lean modules

New in this closure:

- `GaloisForLFunctions.HTGeometry.FiniteHorizonReporterHausdorff` — equation `(7)`.
- `GaloisForLFunctions.HTGeometry.ComplexAffineLinePolynomialAvoidance` — complex obstructions on
  almost every affine line.
- `GaloisForLFunctions.HTGeometry.OneKnobSpectralActivationLaw` — the one-knob law instantiated
  with the actual spectral relation polynomials.
- `GaloisForLFunctions.HTGeometry.OneKnobLocalChainActivationLaw` — the local qudit chain instance.

Pre-existing and reused:

- `AffineLinePolynomialAvoidance` (generic one-knob polynomial restriction);
- `FiniteHorizonCStarPerturbationLaw` (dimension-free Duhamel and Heisenberg bounds);
- `PolynomialHermitianSpectrumGenericity`, `ComplexSpectralCoefficientPolynomialGenericity`,
  `RealAffineHermitianFamilyProjectiveGenericity` (the spectral obstruction layer);
- `TracelessLocalHamiltonianGenericityLaw`, `NearestNeighborQuditPathGenericityLaw` (the physical
  path witness of the parent card, already in `3-formalized`);
- `ReplicaCollisionExtremality` (the collision-floor layer behind `(6)`).

Umbrella: `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. **Finite-horizon continuity `(7)`.**  `norm_reporterOrbit_sub_le` lifts the single-observable
   `C⋆` stability bound to a whole weighted reporter family with its scale
   `𝓑 = (∑_a λ_a ‖B_a‖²)^{1/2}` (`norm_reporterFamily`), and
   `hausdorffDist_coupledReporterOrbit_le` gives the card's bound
   `d_H(X_{H+gV}(T), X_H(T)) ≤ 2 T |g| ‖V‖ 𝓑` in an arbitrary unital `C⋆`-algebra.
2. **Complex obstruction avoidance.**  Spectral obstructions have complex coefficients but real
   parameters; `mvPolynomialRealShadow` picks a nonzero real part, and
   `countable_complexMvPolynomialAffineLineAvoidance_ae_pair` transports the real affine-line
   avoidance layer to them.
3. **One-knob activation with the actual relation polynomials.**
   `countable_exceptional_coupling_of_maximallyProjective_witness`: a single maximally projective
   member of a polynomial Hermitian family forces, along almost every affine line `A + gV` of
   parameters, maximal projective rational rank at all but countably many `g`.
   `mem_polynomialMatrixProjectiveGenericSet_of_maximallyProjective` is the witness transfer, and
   `countable_exceptional_coupling_maximallyProjectiveEigenvalues` states the conclusion on the
   actual eigenvalue packet.
4. **The local qudit chain `(4)`.**
   `exists_uniformQuditPath_countable_exceptional_coupling`: for every `n, q ≥ 2` there is a
   physically realized path system of Hilbert dimension `q ^ n` such that, along almost every
   affine coupling line inside its trace-zero local Hamiltonian space, all but countably many
   coupling strengths lie in the maximally projective set.  The witness consumed is the parent
   card's `exists_uniformQuditPathTracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure`.
5. **Collision floor `(6)`.**  `fidelityReplicaCollisionMass_eq_floor_iff` and
   `all_fidelityReplicaCollisionMass_eq_floor_iff` in `ReplicaCollisionExtremality` characterize
   equality with the fixed-weight floor by exactly the maximal-projectivity condition that item 4
   supplies off the countable exceptional set.

## Verification

- `lake env lean` clean, with no warnings, on all four new modules.
- `lake build GaloisForLFunctions.HTGeometry` — green with all four wired into the umbrella.
- `#print axioms` on the twelve capstones of the chain above: `propext`, `Classical.choice`,
  `Quot.sound` only.

## Scope boundary

The two gates left open on the paper card are not Lean gates: the independent specialist proof
audit and the hostile editorial pass.  Within the formal layer, item 4 delivers the countable
exceptional set on almost every coupling line; the card's `(5)` onsite bound `ρ(A) ≤ n(q-1)` and the
Minkowski-dimension readings `(8)`–`(9)` are consequences drawn in the paper from the rank statement
and the reporter-orbit dimension theorem, and are not re-proved in these modules.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready
