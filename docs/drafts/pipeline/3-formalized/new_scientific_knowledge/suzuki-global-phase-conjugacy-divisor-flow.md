# Formal core of Suzuki's global phase-conjugacy divisor flow

- **ID:** `suzuki-global-phase-conjugacy-divisor-flow-formal`
- **Status:** formalized and audited
- **Paper theorem:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-global-phase-conjugacy-divisor-flow.md`
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
