# Fast-forwardable-stratum codimension obstruction — formalized closure

- **ID:** `fast-forwardable-stratum-codimension-obstruction-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./fast-forwardable-stratum-codimension-obstruction.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`

## Lean modules

- `GaloisForLFunctions.HTGeometry.FastForwardableStratumCodimension` (new)
- `GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity` (new)
- reused: `GaussianSmallBallLowerBound`, `ObserverInvisibleTubeShortcut`,
  `ObserverKernelTubeVolume`, `ExactPenaltyCircuitBellman`,
  `CommutingPauliObserverRankDominance`

Umbrella: `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

The stratum hypothesis `(2)` is carried as an explicit *finite synthesis certificate* — a gate
word of length at most `B` within slack `ε₋` — exactly as the paper card requires, never as
membership in the shortcut locus.

1. `approxComplexity_le_of_witness`, `exists_witness_of_dist_le` — a bounded word certifies
   approximate complexity, and enlarging the slack by the distance moved preserves the
   certificate.
2. `orbitState`, `dist_orbitState_le` — the Duhamel transport `(9)`:
   `dist (orbit H t) (orbit K t) ≤ |t| ‖H − K‖` for a unit state.
3. `exists_witness_tube` — the tube inclusion: for `‖p₂‖ ≤ r/t` and `L r ≤ ε₊ − ε₋`,
   `approxComplexity … ε₊ (orbit (Hmap p) t) ≤ B`.
4. `le_cost_budget` — the relative-budget step: on `‖p₁‖ ≥ 1` and `t ≥ 2 B p(n)/(a λ₋)`,
   `B ≤ a Λ(H(t·p))/p(n)`.
5. `gaussianReal_Icc_pos`, `measure_pi_gaussian_box_pos`, `measure_pi_gaussian_shell_pos` — the
   standard Gaussian charges every nondegenerate interval, hence every box, hence the shell
   `1 ≤ ‖x‖ ≤ 2`.  This is the positivity of the factor `p_f` in `(4)`; mathlib has the density
   and its positivity but not the resulting set positivity.
6. `measure_shortcut_ge` — equation `(4)`: the shortcut event has product-Gaussian measure at
   least `p_f · (2 g r)^v · t^{-v}`, with `g` the corpus Gaussian density floor.
7. `exponent_le_codimension` — the boxed `(5)`: any uniform upper law `K t^{-κ}` on that event
   forces `κ ≤ v`, the codimension of the stratum.
8. `measure_shortcutLocus_ge_annulusTube` — equation `(6)`: deterministically, the unit-time
   shortcut locus contains the fixed-radius tube over the stratum, so its Haar measure over the
   shell `R ≤ ‖p₁‖ ≤ 2R` is at least a constant times `R^f`.
9. `zStringSectorDim`, `zStringSectorDim_le_nonidentityPauliWeightCount`,
   `nonidentityPauliWeightCount_sub_zStringSectorDim` — equations `(14)`–`(15)`: the commuting
   `Z`-string sector has dimension `Σ_{k≤q} C(n,k)`, the full nonidentity Pauli coefficient space
   has dimension `Σ_{k≤q} 3^k C(n,k)`, and their difference — the codimension entering `(5)` — is
   `Σ_{k≤q} (3^k − 1) C(n,k)`.

## Verification

- `lake env lean` clean, no warnings, on both new modules.
- `lake build GaloisForLFunctions.HTGeometry.FastForwardableStratumCodimension` — green.
- `#print axioms` on statements 3–9: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella imports present.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready: priority is not established; the card's own hostile audit forbids
      promoting this as a headline theorem.
