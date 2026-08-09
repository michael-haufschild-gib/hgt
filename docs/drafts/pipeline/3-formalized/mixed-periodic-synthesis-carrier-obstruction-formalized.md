# Mixed periodic-synthesis carrier obstruction — formalized closure

- **ID:** `mixed-periodic-synthesis-carrier-obstruction-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./mixed-periodic-synthesis-carrier-obstruction.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`

## Lean modules

- `GaloisForLFunctions.HTGeometry.MixedPeriodicCarrierObstruction` (new)
- `GaloisForLFunctions.HTGeometry.LatticeGaussianDensity` (new)
- reused: `FastForwardableStratumCodimension`, `GaussianSmallBallLowerBound`,
  `ObserverInvisibleTubeShortcut`, `ObserverKernelTubeVolume`, `ExactPenaltyCircuitBellman`

Umbrella: `GaloisForLFunctions.HTGeometry`.

The coefficient space is `W × (G × T)` with `W = Fin dW → ℝ`, `G = Fin r → ℝ` carrying the full
lattice `Γ = A(ℤ^r)` for an injective linear `A` with `σ‖x‖ ≤ ‖A x‖ ≤ M‖x‖`, and `T = Fin v → ℝ`
the orthogonal complement, so `v = m − dim W − rank Γ`.  Hypothesis `(2)` is carried as an
explicit finite synthesis certificate on `W + Γ`, never as membership in the shortcut locus.

## Formal theorem chain

1. `unitaryEvolution_smul_one`, `orbitState_eq_smul` — the radial identity `t H(x) = H(t x)` in the
   form `orbit H t = orbit (t·H) 1`.
2. `exists_witness_mixedTube` — the mixed tube inclusion: if the `G`-part is within `δ/(2t)` of the
   rescaled lattice and the transverse part within `δ/(2t)` of the origin, the certificate carries
   over at slack `ε₊`.
3. `gaussianFloorTwo`, `gaussianPDFReal_ge_floorTwo`, `gaussianReal_Icc_shifted_lower`,
   `measure_pi_gaussian_shifted_ball_lower` — the **shifted** small-ball bound.  The corpus had
   only the centred version; a fine lattice needs balls centred away from the origin.
4. `measure_pi_gaussian_separatedCenters_lower` — a finite family of `σ`-separated centres inside
   the unit ball carries at least its cardinality times the shifted small-ball mass.
5. `scaledLatticeCenters`, `card_scaledLatticeCenters`, `norm_intVector_le`,
   `one_le_norm_intVector_sub`, `scaledLatticeCenters_norm_le`, `scaledLatticeCenters_separated`,
   `measure_pi_gaussian_scaledLattice_lower` — the fine-lattice density: the `δ/t`-neighbourhood of
   the `1/t`-rescaled lattice keeps a share of Gaussian mass bounded below **independently of `t`**,
   because `(2⌊t/M⌋+1)^r` usable points each carry mass `≳ (δ/t)^r`.  This is the mechanism that
   makes the discrete rank `r` add to the continuous dimension.
6. `measure_mixedShortcut_ge` — equation `(5)`: the shortcut event has product-Gaussian measure at
   least a fixed constant times `t^{-v}`.
7. `exponent_le_mixedCodimension` — the boxed `(6)`: `κ ≤ v = m − dim W − rank Γ`.
8. `measure_mixedShortcutLocus_ge` — equation `(3)`: deterministically, over the shell
   `R ≤ ‖p_W‖ ≤ 2R` the Haar measure of the unit-time shortcut locus is at least a constant times
   `R^{dW}` times the lattice-point count `(2N+1)^r`, so it grows like `R^{d+r}`.

## Verification

- `lake env lean` clean, no warnings, on both new modules.
- `lake build GaloisForLFunctions.HTGeometry.MixedPeriodicCarrierObstruction` — green.
- `#print axioms` on statements 2–8: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella imports present.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready: priority not established.
