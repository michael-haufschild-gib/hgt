# Reflexive polarization synchronization law — Lean certification

- **Paper card:**
  `../../../2-fully-proven/universal-law-field/law-generated-polarization-dynamics/reflexive-polarization-synchronization-conservation-cubic-transport-and-properness-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveReflexivePolarizationSynchronization`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED CORE] [NO SORRY] [NO NEW AXIOMS]`

## Certified surface

| paper mechanism | Lean declaration |
|---|---|
| positive total polarization | `totalPolarization_pos` |
| balanced relative-velocity packet | `synchronization_balance` |
| local = fused + synchronization power | `localPolarPower_eq_fused_add_tension` |
| exact synchronization zero locus | `synchronizationTension_eq_zero_iff` |
| exact joint-neutrality zero locus | `localPolarPower_eq_zero_iff` |
| homogeneous velocity and three-power amplification | `sharedPolarVelocity_amplify`, `localPolarPower_amplify`, `fusedPolarPower_amplify`, `synchronizationTension_amplify` |
| bounded scale orbit iff every local correction vanishes | `boundedLocalPolarOrbit_iff` |
| algebraic cubic transport of synchronization tension | `localRate_sub_fusedRate_eq_cubicTransport` |
| quadratic channels carry zero cubic transport | `cubicSynchronizationTransport_zero` |
| persistent two-channel quadratic mismatch | `quadratic_twoChannel_persistent_tension` |
| combined theorem surface | `reflexivePolarizationSynchronization_capstone` |

## Exact boundary

Lean certifies the unconditional finite scalar-polarization algebra, including the full bounded
amplification theorem.  The paper's coordinate-free bilinear formulation follows by the same
Pythagorean expansion and is already covered statically by `QuotientFusionProjectionGenesis`.
The Fréchet chain-rule derivation from `C^3` potentials to the instantaneous rate equations is not
claimed formalized here; the new module certifies the exact cubic identity once those rates are
formed.
