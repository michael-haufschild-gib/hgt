# Replica crowding central-limit floor — Lean certificate

- **ID:** `replica-crowding-central-limit-floor-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `replica-crowding-central-limit-floor.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Lean modules

| Module | Content |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/FiniteLawCentralBinCrowding.lean` | the crowding floor for an arbitrary finite law on `ℝ` |
| `formal/GaloisForLFunctions/HTGeometry/ReplicaAmplitudeMoments.lean` | multinomial Pascal rule, amplitude recursion, replica energy moments |
| `formal/GaloisForLFunctions/HTGeometry/ReplicaCrowdingCentralLimitFloor.lean` | the card's `(3)` and `(4)` |

All three are imported by `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. `finiteLaw_crowding_floor_center` — for any `a : A → ℝ` with `0 ≤ a` and `∑ a = 1`, any centre
   `m`, and any `δ > 0`,
   `9δ/(16(δ + 4√(∑ a α (X α − m)²))) − finiteLawCollisionMass a X ≤ finiteLawNearMass a X δ`.
   This is `(3)` with the product structure stripped away: Chebyshev, a `δ`-cell partition,
   Cauchy–Schwarz, and the charge of a common cell to close pairs.  `finiteLaw_crowding_floor`
   specialises the centre to the mean.
2. `multinomial_sum_update_pred` — Pascal's rule for multinomial coefficients: for
   `∑ q = r + 1`, `∑_{i : q i ≠ 0} multinomial (q − δ_i) = multinomial q`.
3. `replicaAmplitudeMoment_succ` — the amplitude recursion it produces: every weighted sum over
   multiplicity vectors of mass `r + 1` is the single level average of the sums of mass `r`.
4. `replicaAmplitudeMoment_one`, `replicaAmplitudeMoment_energy`,
   `replicaAmplitudeMoment_energy_sq`, `replicaAmplitudeMoment_energy_variance` — total mass `1`,
   mean `r·Ē`, second moment, and `Var = r·σ²`.  Step 4 is the exact finite form of variance
   additivity under independent sampling, obtained with no measure theory and no independence
   hypothesis.
5. `fidelityReplicaNearActionMass_crowding_floor` — the card's `(3)`, after transporting
   `finiteLawCollisionMass`/`finiteLawNearMass` onto `fidelityReplicaCollisionMass` and
   `fidelityReplicaNearActionMass` (`finiteLawCollisionMass_replicaAmplitude`,
   `finiteLawNearMass_replicaAmplitude`).
   `fidelityReplicaNearActionMass_crowding_floor_sigma_sqrt` writes the denominator as `δ + 4σ√r`.
6. `fidelityReplicaPermutationFloor_microcanonical_le` — the uniform permutation floor obeys
   `≤ r!/d^r`, from `multinomial ≤ r!` and `∑_p multinomial p = d^r`.
7. `fidelityReplicaNearActionMass_microcanonical_floor` — the card's `(4)`: for a maximally
   projective spectrum carried by the uniform weighting,
   `9δ/(16(δ + 4σ√r)) − r!/d^r ≤ fidelityReplicaNearActionMass`.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/FiniteLawCentralBinCrowding.lean` — clean.
- `lake env lean GaloisForLFunctions/HTGeometry/ReplicaAmplitudeMoments.lean` — clean.
- `lake env lean GaloisForLFunctions/HTGeometry/ReplicaCrowdingCentralLimitFloor.lean` — clean.
- `lake build GaloisForLFunctions.HTGeometry.ReplicaCrowdingCentralLimitFloor` — succeeds.
- `#print axioms` on every theorem above: `[propext, Classical.choice, Quot.sound]` only.  No
  `sorry`, no added axiom, no hypothesis beyond nonnegativity, normalisation and `0 < δ`.
