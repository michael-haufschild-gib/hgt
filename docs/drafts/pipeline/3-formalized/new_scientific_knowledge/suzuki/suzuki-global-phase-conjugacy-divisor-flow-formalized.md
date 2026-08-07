# Suzuki global phase conjugacy integrates the complete divisor and its weights — Lean certificate

- **ID:** `suzuki-global-phase-conjugacy-divisor-flow-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-global-phase-conjugacy-divisor-flow.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/CompactOperatorDiscreteSpectrum.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiFiniteMorseResolventOperatorLift.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiGlobalPhaseConjugacy.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.CompactOperatorDiscreteSpectrum`:

```text
GaloisForLFunctions.HTGeometry.countable_setOf_hasEigenvalue
GaloisForLFunctions.HTGeometry.countable_spectrum_of_isCompactOperator
GaloisForLFunctions.HTGeometry.finite_setOf_hasEigenvalue_norm_ge
GaloisForLFunctions.HTGeometry.finite_setOf_mem_spectrum_norm_ge
```

`GaloisForLFunctions.RHTower.SuzukiFiniteMorseResolventOperatorLift`:

```text
RHTower.finite_setOf_negativeLevel_of_isCompactOperator
```

`GaloisForLFunctions.RHTower.SuzukiGlobalPhaseConjugacy`:

```text
GaloisForLFunctions.RHTower.integral_phaseSpeed_fullTurn
GaloisForLFunctions.RHTower.integral_phaseSpeed_phaseCell
GaloisForLFunctions.RHTower.suzukiGlobalPoleVelocity_eq_sourceGenerator
GaloisForLFunctions.RHTower.suzukiPhaseTransport
GaloisForLFunctions.RHTower.suzukiPhaseTransport_atomMass
GaloisForLFunctions.RHTower.suzukiPhaseTransport_comp
GaloisForLFunctions.RHTower.suzukiPhaseTransport_level
GaloisForLFunctions.RHTower.suzukiPhaseTransport_phaseSpeed
GaloisForLFunctions.RHTower.suzukiPhaseTransport_probabilityMass
GaloisForLFunctions.RHTower.suzukiPhaseTransport_self
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 15 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- 3 -> 4 publication-ready: standalone paper, specialist priority review
- intrinsic cofinal shift schedule
- compactness of normalized inverse-phase maps and lattice derivatives
- Xi divisor identification
- RH

These are research frontier items, not formalization debt.

---

## Earlier certificate (merged from the flat stage-3 companion)

# Formal core of Suzuki's global phase-conjugacy divisor flow

- **ID:** `suzuki-global-phase-conjugacy-divisor-flow-formal`
- **Status:** formalized and audited
- **Paper theorem:**
  `./suzuki-global-phase-conjugacy-divisor-flow.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiGlobalPhaseConjugacy.lean`
- **RH used:** no
- **Computation used:** no

## Formalized content

The module represents each proper normalized Suzuki phase by an order isomorphism
`phi : R ≃o R` and defines

```text
suzukiPhaseTransport phi_s phi_r = phi_r.trans phi_s.symm,
suzukiPhasePole phi level = phi.symm level.
```

It proves:

- exact preservation of every lifted phase level and hence every extension spectrum;
- identity, inverse, and flat cocycle laws for global phase transport;
- strict ordering of phase-labeled poles and orientation preservation of transport;
- the differentiated phase-density law `q_s * T' = q_r`;
- the Clark/Nevanlinna atom Jacobian `mu_s = T' * mu_r` from `mu=2/q`;
- the normalized Donoghue probability law with exact compactifying factors;
- transport of the restricted-Weil source norm-weight formula;
- equality of global fixed-level velocity with the already formalized logarithmic source
  generator and local Clark velocity.

## Source-specific capstones

```text
suzukiPhaseTransport_phase
suzukiPhaseTransport_comp
suzukiPhaseTransport_symm
suzukiPhaseTransport_level
suzukiPhaseTransport_pole
suzukiPhasePole_lt_phasePole
suzukiPhaseTransport_strictMono
suzukiPhaseTransport_phaseSpeed
suzukiPhaseTransport_atomMass
suzukiPhaseTransport_probabilityMass
suzukiPhaseTransport_sourceNormWeight
suzukiGlobalPoleVelocity_eq_sourceGenerator
```

## Boundary of the formal layer

The paper proof constructs the order isomorphism from Suzuki's concrete source: the meromorphic
Donoghue measure is pure point and cyclic on an infinite-dimensional space, parity makes its
support two-sided, and positive atom weights make the normalized phase strictly increasing and
proper.  The Lean module consumes the resulting order isomorphisms because Suzuki's unbounded
Friedrichs and differential operators, spectral projections, and concrete Donoghue measure are not
yet represented in Lean.

No cofinal compactness or Xi identification is assumed or proved.

## Audit

- [x] direct `lake env lean GaloisForLFunctions/RHTower/SuzukiGlobalPhaseConjugacy.lean`
- [x] exact `lake build GaloisForLFunctions.RHTower.SuzukiGlobalPhaseConjugacy`
- [x] SOTA import source check
- [x] `#print axioms` capstone audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] global formal lint
- [x] `git diff --check`
