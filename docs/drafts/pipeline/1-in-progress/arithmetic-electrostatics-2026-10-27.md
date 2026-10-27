# Arithmetic Electrostatics of the Zero Divisor programme

- **ID:** aes
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2710/obstacles-summary.md §4 ("arithmetic electrostatics of the zero divisor")
- **Statement:** Develop the potential theory of the zero divisor of `ξ` and of the torsion of the
  characteristic circle: energy, field, renormalized self-energy and reflection pairing of one
  logarithmic potential; equilibrium laws, quantization, adjunction (renormalization of the
  diagonal), stability, and the inequalities that would turn detection into exclusion.

## Goal
Lean folder `formal/GaloisForLFunctions/ArithmeticElectrostatics/`, umbrella
`ArithmeticElectrostatics.lean`, foundational README. Answer the twelve questions of §4.4 by
theorems or sharp no-gos with survivors; build the tools of §4.5 ("not yet built").

Territory: RHTower owns the transverse-equilibrium chain (`TransverseEquilibrium`,
`ZeroNetworkConductance`, `TransverseMaximumPrinciple`, `TransverseAttainment`,
`AngularEnergyQuantization`, `CalogeroVirialCollapse`); ACP owns terminals, outward rays and the
Rankin–Selberg field (`fieldAt`, `xiTransverseField`); AET owns torsion orbits and torsion energies;
APol owns `W`, `D`, `Δ`. AES imports them and adds: finite-configuration virial laws, the transverse
energy of the divisor, renormalized squares (Selberg `Λ₂`), torsion self-intersections and
adjunction, counterterm rates, the arithmetic point, stability.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  paper proofs for each pillar
- [ ] 2 → 3  each pillar in Lean, audited with `lake --old env lean`

## Pillars and modules

| Pillar | Module | Status |
|---|---|---|
| ES1 field dictionary, Newton, Stieltjes and transverse virial | `TheVirialLawsOfAFiniteConfiguration` | planned |
| ES2 equilibrium is the critical line; quantized work; gap | `TransverseEquilibriumIsTheCriticalLine` | planned |
| ES3 transverse energy of the ξ divisor | `TheTransverseEnergyOfTheZeroDivisor` | planned |
| ES4 renormalized square = Selberg `Λ₂`; Laurent self-terms | `TheRenormalizedSquareIsSelbergsSource` | planned |
| ES5 torsion self-intersection, adjunction on Hecke orbits, conjugation on cycles | `TheSelfIntersectionOfATorsionOrbit` | planned |
| ES6 minimal counterterm on orders `≤ N` is `Θ(log N)` | `TheTorsionCountertermIsLogarithmic` | planned |
| ES7 the arithmetic point | `TheArithmeticPoint` | planned |

## Key paper facts
- `Σ_j m_j (Re z_j − c) Re E_j = ½ Σ_{j≠k} m_j m_k (Re z_j − Re z_k)²/|z_j − z_k|²` (symmetrize).
- `Σ_j m_j z_j E_j = ½((Σ m)² − Σ m²)`; transverse + vertical energy = that number.
- `f''/f = (f'/f)² + (f'/f)'`; at a zero of order `m`: double pole `m(m − 1)`, residue `2m R(ρ)`.
- `I(n, n) = φ(n) log n − (φ ⋆ Λ)(n)`, so `I(n,n)/φ(n) = log n − Σ_{p∣n} log p/(p − 1)`.
- Schur test with weights `n^{−1/2}`: `λ_max(P + diag ℓ |_{[1,N]}) ≤ 2 log N + O(1)`.

## Log
- 2026-10-27 — created; README first draft.
