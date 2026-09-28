# Literal self-copy mixed cusp-flux coefficient — Lean certificate

- **Paper card:** `rbh-pw-b-literal-self-mixed-cusp-flux.md`
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old env lean` clean; `#print axioms` = `propext`, `Classical.choice`,
  `Quot.sound`; no `sorry`.

| Card item | Lean theorem |
|-|-|
| `Re q < 1/2` ⇒ `fluxCoefficient q q branch 2 ≠ 0` (every factor nonzero) | `fluxCoefficient_self_lower_ne_zero` |
